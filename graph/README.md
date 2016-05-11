Graph
=====

An easy-to-use graph implementation. Here's the Graph class interface:

```cpp
template <typename NodeId = int, typename NodeData = int, typename EdgeData = int,
          bool Directed = false, bool MultiGraph = false>
class Graph {
  public:
    using NodeIdType    = NodeId;
    using NodeDataType  = NodeData;
    using EdgeDataType  = EdgeData;

    using NodeType      = Node<NodeId, NodeData, EdgeData>;
    using EdgeType      = Edge<NodeId, NodeData, EdgeData>;

    Graph()             = default;
    Graph(Graph&&)      = default;
    Graph(const Graph&) = delete;

    Graph& operator=(Graph&&)      = default;
    Graph& operator=(const Graph&) = delete;

    bool directed() const;
    bool multigraph() const;

    // node & edge counts
    auto nodesSize();
    auto edgesSize();

    // unspecified-order node iterators
    auto nodesBegin();
    auto nodesEnd();

    // unspecified-order edge iterators
    auto edgesBegin();
    auto edgesEnd();

    // breadth-first node iterators
    auto breadthBegin(NodeId start);
    auto breadthEnd();

    // depth-first node iterators
    auto depthBegin(NodeId start, bool postorder = false);
    auto depthEnd();

    // query node/edge
    bool hasNode(NodeId id) const;
    bool hasEdge(NodeId startNodeId, NodeId endNodeId) const;

    // retrieve node/edge (must exist)
    NodeType* getNode(NodeId id) const;
    EdgeType* getEdge(NodeId startNodeId, NodeId endNodeId) const;

    // retrieve edge range (iterator pair) for multigraphs
    auto getEdges(NodeId startNodeId, NodeId endNodeId) const;

    // add node/edge
    NodeType* addNode(NodeId id, const NodeData& data = NodeData());
    EdgeType* addEdge(NodeId startNodeId, NodeId endNodeId,
                      const EdgeData& edgeData      = EdgeData(),
                      const NodeData& startNodeData = NodeData(),
                      const NodeData& endNodeData   = NodeData());
};
```

One convenient feature in all node and edge iterators is that their `->`
operator returns a pointer to the `NodeType`/`EdgeType`, which means that you
can directly access members of `Node`/`Edge` from the iterator (i.e. no need to
dereference it first).

The breadth-first and depth-first begin iterators have the regular forward
iterator semantics except that they're non-copyable (which also means they don't
have a suffix increment operator). This is because they hold a lot of state, so
it would be grossly inefficient to allow them to be copied.

The breadth-first and depth-first end iterators have different types from their
begin counterparts. You can copy/move them or compare them against their begin
counterparts, but these are pretty much the only operations allowed on them.

Finally, the breadth-first iterator has a `parent()` method that returns the
parent node of the current node in the breadth-first traversal tree (i.e. the
node that introduced the current node in the traversal).

`addEdge()` adds the terminal nodes if they haven't already been added.

`Node` and `Edge` have the following interfaces:

```cpp
template <typename NodeId, typename NodeData, typename EdgeData>
class Node {
  public:
    using EdgeType = Edge<NodeId, NodeData, EdgeData>;

    NodeId    id() const;
    NodeData& data();

    // adjacent edges
    auto edgesSize() const;
    auto edgesBegin();
    auto edgesEnd();

    // adjacent nodes
    auto nodesSize() const;
    auto nodesBegin();
    auto nodesEnd();

    size_t indegree()  const;
    size_t outdegree() const;
};

template <typename NodeId, typename NodeData, typename EdgeData>
class Edge {
  public:
    using NodeType = Node<NodeId, NodeData, EdgeData>;

    bool hasNode(const NodeType* n) const;

    NodeType* startNode() const;
    NodeType* endNode()   const;
    EdgeData& data();

    // given a node on the edge, returns the other node.
    // the given node must be on the edge.
    NodeType* otherNode(const NodeType* n) const;
};
```

Following is a dynamic-programming implementation of breadth-first
shortest-distance algorithm using this class (HackerRank's first graph problem):

```cpp
#include <iostream>
#include "graph.hpp"

using namespace std;
using namespace artifacts;

template <typename NodeId>
struct NodePairHasher {
  size_t operator()(const std::pair<NodeId, NodeId>& nodePair) const {
    size_t seed = 0;
    hash_combine(seed, nodePair.first);
    hash_combine(seed, nodePair.second);

    return seed;
  }
};

template <typename NodeId = int, typename NodeData = int, typename EdgeData = int,
          bool Directed = false>
class ShortestDistCalc {
  public:
    using GraphType = Graph<NodeId, NodeData, EdgeData, Directed>;
    using NodePair  = std::pair<NodeId, NodeId>;

    ShortestDistCalc(GraphType& g):
      _g(g)
    {}

    bool hasDistance(NodeId s, NodeId e) const {
      if (s == e) {
        return true;
      }

      if (!_g.directed() && e < s) {
        std::swap(s, e);
      }

      return _distances.find(NodePair(s, e)) != _distances.end();
    }

    int distance(NodeId s, NodeId e) const {
      if (s == e) {
        return 0;
      }

      if (!_g.directed() && e < s) {
        std::swap(s, e);
      }

      return _distances.at(NodePair(s, e));
    }

    void addDistance(NodeId s, NodeId e, int dist) {
      if (s == e) {
        return;
      }

      if (!_g.directed() && e < s) {
        std::swap(s, e);
      }

      _distances[NodePair(s, e)] = dist;
    }

    int exec(NodeId s, NodeId e) {
      if (!_g.directed() && e < s) {
        std::swap(s, e);
      }

      if (hasDistance(s, e)) {
        return distance(s, e);
      }

      auto sIt  = _g.breadthBegin(s), eIt = _g.breadthBegin(e),
           last = _g.breadthEnd();

      ++sIt;
      ++eIt;

      for (; sIt != last && eIt != last; ++sIt, ++eIt) {
        auto sId = (*sIt)->id();
        auto sParentId = sIt.parent()->id();

        auto eId = (*eIt)->id();
        auto eParentId = eIt.parent()->id();

        addDistance(sParentId, sId, _g.getEdge(sParentId, sId)->data());
        addDistance(eParentId, eId, _g.getEdge(eParentId, eId)->data());

        addDistance(s, sId, distance(s, sParentId) + distance(sParentId, sId));
        addDistance(e, eId, distance(e, eParentId) + distance(eParentId, eId));

        if (hasDistance(s, e)) {
          return distance(s, e);
        }
      }

      addDistance(s, e, -1);
      return -1;
    }

  private:
    GraphType& _g;
    std::unordered_map<NodePair, int, NodePairHasher<NodeId>> _distances;
};

void printShortestDists(Graph<>& g, int s, int n) {
  ShortestDistCalc<> calc(g);
  for (int i = 1; i <= n; ++i) {
    if (i != s) {
      cout << calc.exec(s, i) << ' ';
    }
  }

  cout << '\n';
}

int main() {
  int t, n, m, b, e, s;
  cin >> t;
  for (int i = 0; i < t; ++i) {
    Graph<> g;

    cin >> n >> m;
    for (int j = 1; j <= n; ++j) {
      g.addNode(j);
    }

    for (int j = 0; j < m; ++j) {
      cin >> b >> e;
      g.addEdge(b, e, 6);
    }

    cin >> s;

    printShortestDists(g, s, n);
  }
}
```

