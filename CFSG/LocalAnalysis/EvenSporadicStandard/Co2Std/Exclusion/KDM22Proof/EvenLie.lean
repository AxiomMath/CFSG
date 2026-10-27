module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafEvenNoComponent
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenOuter
public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupFix
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5112NotLieOrd
public import CFSG.Adapters.LieModelSmallOrders

public section

namespace CFSG.EvenSporadicStandard.Co2Std.Exclusion.KDM22Proof

open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section Inner


theorem false_of_evenLie_inner {K : Type} [Group K] [Finite K] (hs : IsSimpleGroup K)
    (hna : ∃ a b : K, a * b ≠ b * a) (hK : CFSG.Blueprint.EvenLieType K) {α : MulAut K}
    (hα : orderOf α = 2) (hin : α ∈ (MulAut.conj : K →* MulAut K).range)
    {B : Subgroup (fixedSubgroup α)} (hB : CFSG.IsComponent B) : False := by
  have hα2 : α * α = 1 := by rw [← sq, ← hα, pow_orderOf_eq_one]
  have hα1 : α ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hα
    exact absurd hα (by decide)
  obtain ⟨t, ht⟩ := hin
  have ht' : α = MulAut.conj t := ht.symm
  have ht2 : orderOf t = 2 :=
    CFSG.OddStandard.AltStdSec.lookup_orderOf_eq_two_of_conj hna hα2 hα1 ht'
  obtain ⟨B', hB', -⟩ :=
    CFSG.OddStandard.AltStdSec.isComponent_map_fixedSubgroup_conj ht' hB
  exact CFSG.ComponentClassification.CatLeaf.involutionCentralizersComponentFree_of_evenLieType
    hK t ht2 B' hB'

end Inner

section Outer


theorem false_of_evenLie_outer {K : Type} [Group K]
    {τ : CFSG.Assembly.LowTwoRank.StatedLieTag} {n f : ℕ}
    (hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible τ n 2 f)
    (hK : CFSG.Blueprint.LieModel K τ n 2 f) {α : MulAut K} (hα : orderOf α = 2)
    (hout : α ∉ (MulAut.conj : K →* MulAut K).range) {P : Subgroup (fixedSubgroup α)}
    (hP : CFSG.IsPComponent 2 P)
    (hcard : Nat.card (P ⧸ CFSG.Open.fusionZStar P) = 443520) : False := by
  have hEO := CFSG.ComponentClassification.CatLeafProof.evenLieOuterTwoComponentsInput_holds
  rcases hEO K τ n f hadm hK α hα hout P hP with
    ⟨τ', n', f', hadm', hmod'⟩ | hA | hU
  · exact CFSG.Quasithin.H13.EvenOrd.card_ne_of_evenLieType
      CFSG.Quasithin.H13.EvenOrd.excl_443520
      (X := P ⧸ CFSG.Open.fusionZStar P) ⟨τ', n', f', hadm', hmod'⟩ hcard
  · obtain ⟨e⟩ := hA
    have h360 : Nat.card (P ⧸ CFSG.Open.fusionZStar P) = 360 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      rfl
    omega
  · have h6048 := CFSG.Blueprint.LieModel.card_psu_three_three hU
    omega

end Outer

end CFSG.EvenSporadicStandard.Co2Std.Exclusion.KDM22Proof
