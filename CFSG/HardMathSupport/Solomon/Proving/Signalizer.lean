module

public import CFSG.HardMathSupport.Solomon.Coordinator.Defs

public section

namespace CFSG.HardMathSupport.Solomon.Proving

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

variable {G : Type*} [Group G]

theorem le_coreIn [Finite G] {p k : ℕ} {P X Q : Subgroup G} (hQP : Q ≤ P)
    (hk : k ≤ pRank p Q) : X ⊓ Subgroup.normalizer (Q : Set G) ≤ coreIn p k P X :=
  le_iSup₂_of_le Q ⟨hQP, hk⟩ le_rfl

end CFSG.HardMathSupport.Solomon.Proving

end
