//
// Author:      Haitham Gad
// Date:        5/1/2016
// Description: An easy-to-use generic enough graph implementation.
//

#ifndef ARTIFACTS_GRAPH_HPP
#define ARTIFACTS_GRAPH_HPP

#include <algorithm>
#include <cassert>
#include <deque>
#include <memory>
#include <iterator>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

namespace artifacts {

template <typename NodeId, typename NodeData, typename EdgeData>
class Node;

template <typename NodeId, typename NodeData, typename EdgeData>
class Edge;

class Exception : public std::exception {
  public:
    Exception(const std::string& msg):
      _msg(msg)
    {}

    std::string getErrMsg() {
      return _msg;
    }

  private:
    std::string _msg;
};

template <class T>
inline void hash_combine(std::size_t& seed, const T& v) {
  std::hash<T> hasher;
  seed ^= hasher(v) + 0x9e3779b9 + (seed << 6) + (seed >> 2);
}

template <typename NodeType, typename Iter>
class OtherNodeIter {
  public:
    OtherNodeIter(NodeType* node, Iter iter):
      _node(node),
      _iter(iter)
    {}

    NodeType* operator*()  const { return (*_iter)->otherNode(_node); }
    NodeType* operator->() const { return (*_iter)->otherNode(_node); }

    friend bool operator==(const OtherNodeIter& iter1,
                           const OtherNodeIter& iter2) {
      return iter1._iter == iter2._iter;
    }

    friend bool operator!=(const OtherNodeIter& iter1,
                           const OtherNodeIter& iter2) {
      return !(iter1 == iter2);
    }

    OtherNodeIter& operator++() {
      ++_iter;
      return *this;
    }

    OtherNodeIter  operator++(int) {
      OtherNodeIter it = *this;
      ++_iter;
      return it;
    }

    OtherNodeIter& operator--() {
      --_iter;
      return *this;
    }

    OtherNodeIter  operator--(int) {
      OtherNodeIter it = *this;
      --_iter;
      return it;
    }

  private:
    NodeType* _node;
    Iter      _iter;
};

template <typename NodeType, typename Iter>
OtherNodeIter<NodeType, Iter> otherNodeIter(NodeType* node, Iter iter) {
  return OtherNodeIter<NodeType, Iter>(node, iter);
}

template <typename NodeId, typename NodeData, typename EdgeData>
class Node {
  public:
    using EdgeType = Edge<NodeId, NodeData, EdgeData>;

    NodeId    id()   const { return _id;   }
    NodeData& data()       { return _data; }

    auto edgesSize() const { return _edges.size(); }
    auto edgesBegin()      { return _edges.begin();  }
    auto edgesEnd()        { return _edges.end();    }

    auto nodesSize() const { return edgesSize();   }
    auto nodesBegin()      { return otherNodeIter(this, _edges.begin());  }
    auto nodesEnd()        { return otherNodeIter(this, _edges.end());    }

    size_t indegree()  const { return _indegree; }
    size_t outdegree() const { return _edges.size(); }

  private:
    using EdgeCont = std::vector<EdgeType*>;

    Node(NodeId id, const NodeData& data = NodeData()):
      _data(data),
      _id(id)
    {}

    Node(Node&&)      = default;
    Node(const Node&) = delete;

    Node& operator=(Node&&)      = default;
    Node& operator=(const Node&) = delete;

    template <typename NId, typename NData, typename EData,
              bool Directed, bool MultiGraph>
    friend class Graph;

    void addEdge(EdgeType* e) { _edges.push_back(e); }
    void incIndegree() { ++_indegree; }
    void decIndegree() { --_indegree; }

    EdgeCont _edges;
    size_t   _indegree;
    NodeData _data;
    NodeId   _id;
};

template <typename NodeType>
class EdgeId {
  public:
    EdgeId(EdgeId&&)      = default;
    EdgeId(const EdgeId&) = default;

    EdgeId& operator=(EdgeId&&)      = default;
    EdgeId& operator=(const EdgeId&) = default;

    NodeType* startNode() const { return _startNode; }
    NodeType* endNode()   const { return _endNode;   }

    bool hasNode(const NodeType* n) const {
      return n->id() == _startNode->id() ||
             n->id() == _endNode->id();
    }

  private:
    template <typename EdgeData, typename NodeId, typename NodeData>
    friend class Edge;

    template <typename NId, typename NData, typename EData,
              bool Directed, bool MultiGraph>
    friend class Graph;

    friend bool operator==(const EdgeId& edgeId1, const EdgeId& edgeId2) {
      return edgeId1._startNode == edgeId2._startNode &&
             edgeId1._endNode == edgeId2._endNode;
    }

    friend bool operator!=(const EdgeId& edgeId1, const EdgeId& edgeId2) {
      return !(edgeId1 == edgeId2);
    }

    EdgeId(NodeType* startNode, NodeType* endNode):
      _startNode(startNode),
      _endNode(endNode)
    {
      if (!_startNode) {
        throw Exception("invalid start node");
      }

      if (!_endNode) {
        throw Exception("invalid end node");
      }
    }

    NodeType* _startNode;
    NodeType* _endNode;
};

template <typename NodeType>
struct EdgeIdHasher {
  size_t operator()(const EdgeId<NodeType>& edgeId) const {
    size_t seed = 0;
    hash_combine(seed, edgeId.startNode());
    hash_combine(seed, edgeId.endNode());

    return seed;
  }
};

template <typename NodeId, typename NodeData, typename EdgeData>
class Edge {
  public:
    using NodeType = Node<NodeId, NodeData, EdgeData>;

    bool hasNode(const NodeType* n) const { return _id.hasNode(n); }

    NodeType* startNode() const { return _id.startNode(); }
    NodeType* endNode()   const { return _id.endNode();   }
    EdgeData& data()            { return _data;           }

    NodeType* otherNode(const NodeType* n) const {
      assert(hasNode(n));
      return n == startNode() ? endNode() : startNode();
    }

  private:
    using EdgeIdType = EdgeId<NodeType>;

    template <typename NId, typename NData, typename EData,
              bool Directed, bool MultiGraph>
    friend class Graph;

    Edge(NodeType* startNode, NodeType* endNode,
         const EdgeData& data = EdgeData()):
      _id(startNode, endNode),
      _data(data)
    {}

    Edge(Edge&&)      = default;
    Edge(const Edge&) = delete;

    Edge& operator=(Edge&&)      = default;
    Edge& operator=(const Edge&) = delete;

    EdgeIdType& id() const { return _id; }

    EdgeIdType _id;
    EdgeData   _data;
};

template <typename Iter>
class ValueIter {
  public:
    using ValueType =
      typename std::decay<decltype(std::declval<Iter>()->second)>::type;

    ValueIter(Iter iter):
      _iter(iter)
    {}

    ValueType operator*()  const { return _iter->second; }
    ValueType operator->() const { return _iter->second; }

    friend bool operator==(const ValueIter& iter1, const ValueIter& iter2) {
      return iter1._iter == iter2._iter;
    }

    friend bool operator!=(const ValueIter& iter1, const ValueIter& iter2) {
      return !(iter1 == iter2);
    }

    ValueIter& operator++() {
      ++_iter;
      return *this;
    }

    ValueIter& operator++(int) {
      ValueIter it = *this;
      ++_iter;
      return it;
    }

  private:
    Iter _iter;
};

template <typename Iter>
ValueIter<Iter> valueIter(Iter iter) {
  return ValueIter<Iter>(iter);
}

struct BreadthEndIter {
  friend bool operator==(BreadthEndIter, BreadthEndIter) {
    return true;
  }

  friend bool operator!=(BreadthEndIter, BreadthEndIter) {
    return false;
  }
};

template <typename NodeType>
class BreadthIter {
  public:
    BreadthIter():
      _current(nullptr),
      _parent(nullptr)
    {}

    BreadthIter(NodeType* start):
      _current(start),
      _parent(nullptr)
    {}

    BreadthIter(BreadthIter&&) = default;
    BreadthIter& operator=(BreadthIter&&) = default;

    NodeType* parent() const { return _parent; }

    NodeType* operator*()  const { return _current; }
    NodeType* operator->() const { return _current; }

    friend bool operator==(const BreadthIter& iter1, const BreadthIter& iter2) {
      return iter1._current == iter2._current;
    }

    friend bool operator!=(const BreadthIter& iter1, const BreadthIter& iter2) {
      return !(iter1 == iter2);
    }

    friend bool operator==(const BreadthIter& iter1, BreadthEndIter iter2) {
      return !iter1._current;
    }

    friend bool operator==(BreadthEndIter iter1, const BreadthIter& iter2) {
      return !iter2._current;
    }

    friend bool operator!=(const BreadthIter& iter1, BreadthEndIter iter2) {
      return !(iter1 == iter2);
    }

    friend bool operator!=(BreadthEndIter iter1, const BreadthIter& iter2) {
      return !(iter1 == iter2);
    }

    BreadthIter& operator++() {
      if (!_current) {
        return *this;
      }

      _visitedNodes.insert(_current);

      for (auto first = _current->nodesBegin(), last = _current->nodesEnd();
           first != last; ++first) {
        if (!visitedNode(*first) && !discoveredNode(*first)) {
          _discoveredNodes.insert(*first);
          _scheduledNodes.emplace_back(*first, _current);
        }
      }

      if (_scheduledNodes.empty()) {
        _current = nullptr;
        _parent  = nullptr;
      } else {
        _current = _scheduledNodes.front().first;
        _parent  = _scheduledNodes.front().second;
        _scheduledNodes.pop_front();
      }

      return *this;
    }

  private:
    using NodePair = std::pair<NodeType*, NodeType*>;

    friend struct BreadthEndIter;

    BreadthIter(const BreadthIter&) = delete;
    BreadthIter& operator=(const BreadthIter&) = delete;

    bool visitedNode(NodeType* node) const {
      return _visitedNodes.find(node) != _visitedNodes.end();
    }

    bool discoveredNode(NodeType* node) const {
      return _discoveredNodes.find(node) != _discoveredNodes.end();
    }

    std::unordered_set<NodeType*> _visitedNodes;
    std::unordered_set<NodeType*> _discoveredNodes;
    std::deque<NodePair>          _scheduledNodes;
    NodeType*                     _current;
    NodeType*                     _parent;
};

template <typename NodeType>
BreadthIter<NodeType> breadthIter(NodeType* node) {
  return BreadthIter<NodeType>(node);
}

struct DepthEndIter {
  friend bool operator==(DepthEndIter, DepthEndIter) {
    return true;
  }

  friend bool operator!=(DepthEndIter, DepthEndIter) {
    return false;
  }
};

template <typename NodeType>
class DepthIter {
  public:
    DepthIter(bool postorder):
      _current(nullptr),
      _postorder(postorder)
    {}

    DepthIter(NodeType* start, bool postorder):
      _current(start),
      _postorder(postorder)
    {
      if (_postorder) {
        _current = deepestNode(_current);
      }
    }

    DepthIter(DepthIter&&) = default;

    DepthIter& operator=(DepthIter&&) = default;

    NodeType* operator*()  const { return _current; }
    NodeType* operator->() const { return _current; }

    friend bool operator==(const DepthIter& iter1, const DepthIter& iter2) {
      return iter1._current == iter2._current;
    }

    friend bool operator!=(const DepthIter& iter1, const DepthIter& iter2) {
      return !(iter1 == iter2);
    }

    friend bool operator==(const DepthIter& iter1, DepthEndIter iter2) {
      return !iter1._current;
    }

    friend bool operator==(DepthEndIter iter1, const DepthIter& iter2) {
      return !iter2._current;
    }

    friend bool operator!=(const DepthIter& iter1, DepthEndIter iter2) {
      return !(iter1 == iter2);
    }

    friend bool operator!=(DepthEndIter iter1, const DepthIter& iter2) {
      return !(iter1 == iter2);
    }

    DepthIter& operator++() {
      if (_postorder) {
        return postOrderInc();
      } else {
        return preOrderInc();
      }
    }

    DepthIter& preOrderInc() {
      if (!_current) {
        return *this;
      }

      _visitedNodes.insert(_current);
      _ancestorNodes.push_back(_current);

      do {
        auto first = _current->nodesBegin(), last = _current->nodesEnd();
        for (; first != last; ++first) {
          if (!visitedNode(*first)) {
            break;
          }
        }

        if (first != last) {
          _current = *first;
          break;
        }

        if (!_ancestorNodes.empty()) {
          _current = _ancestorNodes.back();
          _ancestorNodes.pop_back();
        }
      } while (!_ancestorNodes.empty());

      if (_ancestorNodes.empty()) {
        _current = nullptr;
      }

      return *this;
    }

    DepthIter& postOrderInc() {
      if (!_current) {
        return *this;
      }

      _visitedNodes.insert(_current);
      if (_ancestorNodes.empty()) {
        _current = nullptr;
        return *this;
      }

      _current = _ancestorNodes.back();
      _ancestorNodes.pop_back();

      _current = deepestNode(_current);
      return *this;
    }

  private:
    DepthIter(const DepthIter&) = delete;
    DepthIter& operator=(const DepthIter&) = delete;

    bool visitedNode(NodeType* node) const {
      return _visitedNodes.find(node) != _visitedNodes.end();
    }

    bool ancestorNode(NodeType* node) const {
      return std::find(_ancestorNodes.begin(), _ancestorNodes.end(), node)
               != _ancestorNodes.end();
    }

    NodeType* deepestNode(NodeType* node) {
      auto first = node->nodesBegin(), last = node->nodesEnd();
      for (; first != last; ++first) {
        if (!visitedNode(*first) && !ancestorNode(*first)) {
          _ancestorNodes.push_back(node);
          return deepestNode(*first);
        }
      }

      return node;
    }

    std::unordered_set<NodeType*> _visitedNodes;
    std::deque<NodeType*>         _ancestorNodes;
    NodeType*                     _current;
    bool                          _postorder;
};

template <typename NodeType>
DepthIter<NodeType> depthIter(NodeType* node, bool postorder = false) {
  return DepthIter<NodeType>(node, postorder);
}

template <typename EdgeIdType, typename EdgeType, typename NodeType,
          bool MultiGraph>
struct EdgeContainer {
  using type =
    std::unordered_map<EdgeIdType, std::unique_ptr<EdgeType>,
                       EdgeIdHasher<NodeType>>;
};

template <typename EdgeIdType, typename EdgeType, typename NodeType>
struct EdgeContainer<EdgeIdType, EdgeType, NodeType, true> {
  using type =
    std::unordered_multimap<EdgeIdType, std::unique_ptr<EdgeType>,
                            EdgeIdHasher<NodeType>>;
};

template <typename EdgeIdType, typename EdgeType, typename NodeType,
          bool MultiGraph>
using EdgeContainerT = typename EdgeContainer<EdgeIdType, EdgeType,
                                              NodeType, MultiGraph>::type;

template <typename Pair>
struct EdgeRange :
  public std::pair<decltype(valueIter(std::declval<Pair>().first)),
                   decltype(valueIter(std::declval<Pair>().second))> {
  EdgeRange(const Pair& p):
    EdgeRange::pair(valueIter(p.first), valueIter(p.second))
  {}
};

template <typename Pair>
auto edgeRange(const Pair& p) {
  return EdgeRange<Pair>(p);
};

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

    bool directed() const { return Directed; }
    bool multigraph() const { return MultiGraph; }

    auto nodesSize()  { return _nodes.size(); }
    auto nodesBegin() { return valueIter(_nodes.begin());  }
    auto nodesEnd()   { return valueIter(_nodes.end());    }

    auto edgesSize()  { return _edges.size(); }
    auto edgesBegin() { return valueIter(_edges.begin());  }
    auto edgesEnd()   { return valueIter(_edges.end());    }

    auto breadthBegin(NodeId start) {
      assert(hasNode(start));
      return breadthIter(getNode(start));
    }

    auto breadthEnd() {
      return BreadthEndIter();
    }

    auto depthBegin(NodeId start, bool postorder = false) {
      assert(hasNode(start));
      return depthIter(getNode(start), postorder);
    }

    auto depthEnd() {
      return DepthEndIter();
    }

    bool hasNode(NodeId id) const {
      return _nodes.find(id) != _nodes.end();
    }

    NodeType* getNode(NodeId id) const {
      assert(hasNode(id));
      return _nodes.at(id).get();
    }

    bool hasEdge(NodeId startNodeId, NodeId endNodeId) const {
      if (!directed() && endNodeId < startNodeId) {
        std::swap(startNodeId, endNodeId);
      }

      return hasNode(startNodeId) && hasNode(endNodeId) &&
             _edges.find(EdgeIdType(getNode(startNodeId), getNode(endNodeId)))
               != _edges.end();
    }

    EdgeType* getEdge(NodeId startNodeId, NodeId endNodeId) const {
      assert(hasEdge(startNodeId, endNodeId));
      if (!directed() && endNodeId < startNodeId) {
        std::swap(startNodeId, endNodeId);
      }

      return _edges.find(EdgeIdType(getNode(startNodeId),
                                    getNode(endNodeId)))->second.get();
    }

    auto getEdges(NodeId startNodeId, NodeId endNodeId) const {
      assert(hasEdge(startNodeId, endNodeId));
      if (!directed() && endNodeId < startNodeId) {
        std::swap(startNodeId, endNodeId);
      }

      return edgeRange(_edges.equal_range(EdgeIdType(getNode(startNodeId),
                                                     getNode(endNodeId))));
    }

    NodeType* addNode(NodeId id, const NodeData& data = NodeData()) {
      assert(!hasNode(id));

      _nodes[id] = std::unique_ptr<NodeType>(new NodeType(id, data));
      return getNode(id);
    }

    EdgeType* addEdge(NodeId startNodeId, NodeId endNodeId,
                      const EdgeData& edgeData = EdgeData(),
                      const NodeData& startNodeData = NodeData(),
                      const NodeData& endNodeData = NodeData()) {
      bool swapped = !directed() && endNodeId < startNodeId;
      if (swapped) {
        std::swap(startNodeId, endNodeId);
      }

      NodeType* startNode = hasNode(startNodeId)
                              ? getNode(startNodeId)
                              : addNode(startNodeId, swapped ? endNodeData
                                                             : startNodeData);

      NodeType* endNode = hasNode(endNodeId)
                            ? getNode(endNodeId)
                            : addNode(endNodeId, swapped ? startNodeData
                                                         : endNodeData);

      if (!multigraph() && hasEdge(startNodeId, endNodeId)) {
        auto edge = getEdge(startNodeId, endNodeId);
        edge->data() = edgeData;
        return edge;
      }

      EdgeIdType edgeId(startNode, endNode);
      EdgeType* edge = new EdgeType(startNode, endNode, edgeData);
      _edges.emplace(edgeId, std::unique_ptr<EdgeType>(edge));

      startNode->addEdge(edge);
      endNode->incIndegree();

      if (!directed()) {
        endNode->addEdge(edge);
        startNode->incIndegree();
      }

      return edge;
    }

  private:
    using NodeCont = std::unordered_map<NodeId, std::unique_ptr<NodeType>>;

    using EdgeIdType = EdgeId<NodeType>;
    using EdgeCont   = EdgeContainerT<EdgeIdType, EdgeType, NodeType, MultiGraph>;

    NodeCont _nodes;
    EdgeCont _edges;
};

}

#endif // ARTIFACTS_GRAPH_HPP

