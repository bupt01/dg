#ifndef _DG_MARKERSRGBUILDER_H
#define _DG_MARKERSRGBUILDER_H

#include <memory>
#include <vector>
#include <unordered_set>
#include <unordered_map>
#include <map>

#include "analysis/BFS.h"
#include "analysis/ReachingDefinitions/Ssa/SparseRDGraphBuilder.h"

namespace dg {
namespace analysis {
namespace rd {
namespace ssa {

class MarkerSRGBuilder : public SparseRDGraphBuilder
{
    /* see using-s in SparseRDGraphBuilder for reference... */

    SparseRDGraph srg;
    std::vector<std::unique_ptr<NodeT>> phi_nodes;

    /* work structures */
    std::map<DefSite, std::unordered_map<BlockT *, NodeT *>> current_def;
    std::unordered_set<BlockT *> sealed_blocks;
    std::unordered_map<BlockT *, std::map<DefSite, NodeT *>> incomplete_phis;

    void writeVariable(const DefSite& var, NodeT *assignment);
    NodeT *readVariableRecursive(const DefSite& var, BlockT *block);

    NodeT *readVariable(const DefSite& var, BlockT *read);
    void addPhiOperands(const DefSite& var, NodeT *phi);

    void processBlock(BlockT *block) {
        for (NodeT *node : block->getNodes()) {
            if (node->getType() == RDNodeType::PHI)
                continue;

            for (const DefSite& def : node->defs) {
                NodeT *assignment = readVariable(def, block);
                srg[assignment].push_back(std::make_pair(def, node));
                writeVariable(def, node);
            }

            for (const DefSite& use : node->getUses()) {
                NodeT *assignment = readVariable(use, block);
                // add edge from last definition to here
                srg[assignment].push_back(std::make_pair(use, node));
            }
        }
    }

public:

    std::pair<SparseRDGraph, std::vector<std::unique_ptr<NodeT>>>
        build(NodeT *root) override {

        BBlockBFS<NodeT> bfs(BFS_BB_CFG);

        AssignmentFinder af;
        af.populateUnknownMemory(root);

        BlockT *block = root->getBBlock();
        bfs.run(block, [&,this](BlockT *block, void*){
            processBlock(block);
        }, nullptr);

        return std::make_pair<SparseRDGraph, std::vector<std::unique_ptr<NodeT>>>(std::move(srg), std::move(phi_nodes));
    }

};

}
}
}
}

#endif /* _DG_MARKERSRGBUILDER_H */