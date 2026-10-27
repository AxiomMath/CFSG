module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenData2
public import CFSG.Blueprint.ChevalleyRootArtifact

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice

theorem e8t3K_mem_iff {v : Fin Tag.E8.rank → ℤ} :
    v ∈ rootFinset Tag.E8 ↔ List.ofFn v ∈ Tag.E8.artifactRoots :=
  mem_rootFinset.trans isRoot_iff_mem_artifactRoots

@[expose] def e8t3K_vec (l : List ℤ) : Fin Tag.E8.rank → ℤ := fun i => l.getD i.val 0

theorem e8t3K_vec_ofFn (v : Fin Tag.E8.rank → ℤ) : e8t3K_vec (List.ofFn v) = v := by
  funext i
  simp [e8t3K_vec, List.getD_eq_getElem]

theorem e8t3K_forall {Q : (Fin Tag.E8.rank → ℤ) → Prop}
    (h : ∀ l ∈ Tag.E8.artifactRoots, Q (e8t3K_vec l)) : ∀ v ∈ rootFinset Tag.E8, Q v := by
  intro v hv
  have := h _ (e8t3K_mem_iff.1 hv)
  rwa [e8t3K_vec_ofFn] at this

@[expose] def e8t3K_wLit : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
  !![0, 1, 0, 0, -1, 0, 0, 2;
    1, 0, 0, 0, -1, 0, 0, 3;
    0, 0, 0, 1, -2, 0, 0, 4;
    0, 0, 1, 0, -2, 0, 0, 6;
    0, 0, 0, 0, -1, 0, 0, 5;
    0, 0, 0, 0, -1, 0, 1, 3;
    0, 0, 0, 0, -1, 1, 0, 2;
    0, 0, 0, 0, 0, 0, 0, 1]

theorem e8t3K_wm : wm = e8t3K_wLit := by decide +kernel

@[expose] def e8t3K_νLit : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
  !![2, 0, 0, 0, -1, 0, 0, 1;
    3, 0, 0, 0, -1, 0, 0, 0;
    4, 0, 0, 0, -2, 0, 1, 0;
    6, 0, 0, 0, -3, 1, 0, 0;
    5, 0, 0, 0, -2, 0, 0, 0;
    3, 0, 1, 0, -2, 0, 0, 0;
    2, 0, 0, 1, -2, 0, 0, 0;
    1, 1, 0, 0, -1, 0, 0, 0]

theorem e8t3K_wordν : wordMat Tag.E8
    [4, 5, 6, 7, 3, 4, 5, 6, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 1, 3, 4, 2, 3, 0, 2, 1,
      3, 4, 5, 6, 4, 3, 2, 1, 3, 4, 5, 4, 3, 2, 1, 3, 4] = e8t3K_νLit := by
  decide +kernel

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux

end
