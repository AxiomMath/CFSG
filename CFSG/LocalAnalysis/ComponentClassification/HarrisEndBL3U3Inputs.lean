module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Inputs

public section

namespace CFSG.ComponentClassification.HarrisLit.EndB

open CFSG Subgroup

@[expose] def L3U3InvolutionSL2Fact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (E : Subgroup G) (p m : ℕ), p.Prime → p ≠ 2 → 1 ≤ m →
    (Blueprint.LieModel ↥E .PSL 3 p m ∨ Blueprint.LieModel ↥E .PSU 3 p m) →
    ∀ e ∈ E, orderOf e = 2 →
      ∃ Y : Subgroup G, Y ≤ E ⊓ centralizer {e} ∧
        (Y.subgroupOf (E ⊓ centralizer {e})).IsSubnormal ∧ IsSLTwoOver (p ^ m) ↥Y ∧ e ∈ Y

end CFSG.ComponentClassification.HarrisLit.EndB
