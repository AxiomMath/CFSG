module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5CompCent
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5CompK2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5CompK45

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Tab5_i4m_of_comp_of (hS : Asc82SchurU43) (hM : Asc82Tab6M) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6Z2 L →
      ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
        ∀ J : Subgroup G, IsComponentIn J (L ⊓ centralizer ({s} : Set G)) → IsL29 J →
          (∀ u ∈ J, orderOf u = 2 → ¬ IsI4PlusIn L u) → Kind5 L s 1
  := by
  intro G _ _ L hL s hs2 hs J hJ h29 hnp
  rcases asc82Tab5_classify_of hM G L hL s hs2 hs with hc | h0 | h1 | h2 | h3 | h4 | h5
  · exact (t5_comp_not_central hL hc hJ h29).elim
  · exact (t5_comp_kind03_false hM hL hs2 hs (Or.inl h0) hJ h29).elim
  · exact h1
  · exact (t5_comp_kind2_false hM hL hs2 hs h2 hJ h29).elim
  · exact (t5_comp_kind03_false hM hL hs2 hs (Or.inr h3) hJ h29).elim
  · exact (t5_comp_cplx_false hS hL (Or.inl h4) hJ h29 hnp).elim
  · exact (t5_comp_cplx_false hS hL (Or.inr h5) hJ h29 hnp).elim

end CFSG.OddStandard.SmallF3.Omega
