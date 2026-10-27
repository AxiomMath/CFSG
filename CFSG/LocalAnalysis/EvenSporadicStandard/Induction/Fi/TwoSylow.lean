module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FiTwoSylowFinkelstein
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Open

public section

namespace CFSG.EvenSporadicStandard.Induction.Fi

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977
  CFSG.EvenSporadicStandard.Solomon78

theorem twoSylowStd_fi22 (h25 : Finkelstein77.Asc76Lemma25)
    (hr : ∀ (X : Type) [Group X], IsLS [.Fi22] X → 3 ≤ CFSG.pRank 2 X)
    (hI : ∀ (Y : Type) [Group Y], IsSporadic Y .Fi22 → HypothesisOne Y) :
    TwoSylowStd [.Fi22] := by
  intro s hs H _ _ N M hN hidx _ hcov hstd hcyc P
  obtain rfl := List.mem_singleton.1 hs
  obtain ⟨t, ht2, hcomp⟩ := hstd.exists_involution
  have htC : t ∈ centralizer (M : Set H) := mem_centralizer_iff.2 fun m hm =>
    mem_centralizer_singleton_iff.1 (hcomp.1 hm)
  exact card_sylow_eq_two_of_finkelstein_of_lemma25_of_pRank h25 hN hidx hstd hcov.1
    hcov.odd_center hcyc (hI _ hcov.2.2) (hr _ (isLS_iff.2 ⟨_, List.mem_singleton_self _, hcov⟩))
    htC ht2 P

end CFSG.EvenSporadicStandard.Induction.Fi
