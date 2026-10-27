module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.HNRow
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.HSFix

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.TwoHS

theorem hnFixesElem_of_mult
    (hmult : OddMultTrivial .HN) : HNFixesElem := by
  intro H _ _ L K u hcov hQ
  have hL : IsSporadic L .HN := hcov.isSporadic_of_mult hmult
  obtain ⟨huL, hu2, hKL, hKu, hcard⟩ := hQ
  obtain ⟨hcovS, -⟩ := hn_pair_cover hL huL hu2 hKL hKu hcard
  have hKC : K ≤ L ⊓ centralizer ({u} : Set H) := fun k hk =>
    ⟨hKL hk, mem_centralizer_singleton_iff.2 (hKu k hk)⟩
  obtain ⟨M⟩ := exists_coverModel hcovS.perfect hcovS.card_center hcovS.quotient
  exact (involutionFixesElem_of_coverModel hcovS.perfect M).of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe hKC)

end CFSG.EvenSporadicStandard.Induction
