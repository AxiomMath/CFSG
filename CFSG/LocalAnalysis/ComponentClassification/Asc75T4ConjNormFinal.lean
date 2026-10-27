module

public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4ConjNormDiag
public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4ConjNormTop
public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4Main

public section

namespace CFSG.ComponentClassification.Asc75T4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type} [Group G] [Finite G]

theorem normalIn_inf_normalizer_of_le_sup {Q : Subgroup G} (hM : MainCounterexample G Q)
    (hS : MainSetting Q) (j : G)
    (hcover : twoPrimeLayerIn (rightConjugate Q j) ≤
      (twoPrimeLayerIn (rightConjugate Q j) ⊓ normalizer (linkedLayer Q : Set G)) ⊔
        oddCoreIn (rightConjugate Q j)) :
    NormalIn (twoPrimeLayerIn (rightConjugate Q j) ⊓ normalizer (linkedLayer Q : Set G))
      (twoPrimeLayerIn (normalizer (linkedLayer Q : Set G))) := by
  set J := rightConjugate Q j with hJdef
  set D := linkedLayer Q
  set N := normalizer (D : Set G)
  set X := twoPrimeLayerIn J ⊓ N
  have htJ : TightlyEmbedded J := rightConjugate_tightlyEmbedded Q hS.tight j
  have h4J : HasFourGroup (twoPrimeLayerIn J) := hS.four_rightConjugate j
  have hXs : IsSemisimpleQ X := isSemisimpleQ_of_le_twoPrimeLayerIn inf_le_left hcover
  have hX4 : HasFourGroup X := hasFourGroup_of_le_sup h4J inf_le_left hcover
  by_cases hJ : J ∈ linkedClass Q
  · have hX : X = twoPrimeLayerIn J :=
      inf_of_le_left ((twoPrimeLayerIn_le_linkedLayer hJ).trans le_normalizer)
    rw [hX]
    exact normalIn_twoPrimeLayerIn_of_normalIn htJ h4J (hS.normalIn_linkedLayer hJ)
      (normalIn_of_le_normalizer le_normalizer le_rfl)
  have hND : N ≠ ⊤ := fun h => hM.not_case1 (hS.thm4Case1_of_normalizer_eq_top h)
  set Y := J ⊓ N
  have hXY : X ≤ Y := inf_le_inf_right _ (twoPrimeLayerIn_le J)
  have hYN : Y ≤ N := inf_le_right
  have hNJ : N ⊓ normalizer (J : Set G) ≤ normalizer (Y : Set G) := fun m hm =>
    inf_normalizer_le_normalizer_inf J N (mem_inf.mpr ⟨(mem_inf.mp hm).2,
      le_normalizer (mem_inf.mp hm).1⟩)
  have hNX : N ⊓ normalizer (J : Set G) ≤ normalizer (X : Set G) := fun m hm =>
    inf_normalizer_le_normalizer_inf _ N (mem_inf.mpr
      ⟨normalizer_le_normalizer_twoPrimeLayerIn J (mem_inf.mp hm).2,
        le_normalizer (mem_inf.mp hm).1⟩)
  have hYX : Y ≤ normalizer (X : Set G) := fun y hy =>
    hNX (mem_inf.mpr ⟨(mem_inf.mp hy).2, le_normalizer (mem_inf.mp hy).1⟩)
  have hXn : NormalIn X Y := normalIn_of_le_normalizer hXY hYX
  have hCL : X ≤ twoPrimeLayerIn Y := le_twoPrimeLayerIn_of_normalIn hXn hXs
  have hL4 := hX4.mono hCL
  have hYe : Even (Nat.card Y) := (hX4.mono hXY).even_card
  have htY := tightlyEmbedded_subgroupOf htJ inf_le_left hYN hYe hNJ
  have hne : twoPrimeLayerIn (Y.subgroupOf N) ≠ oddCoreIn (Y.subgroupOf N) := by
    intro h
    have h1 := congrArg (Subgroup.map N.subtype) h
    rw [twoPrimeLayerIn_subgroupOf_map hYN, oddCoreIn_subgroupOf_map hYN] at h1
    have h2 := odd_card_oddCoreIn Y
    rw [← h1] at h2
    exact Nat.not_even_iff_odd.mpr h2 hL4.even_card
  have hcard : Nat.card N < Nat.card G := by
    rw [← card_top (G := G)]
    exact card_lt_of_lt (lt_top_iff_ne_top.mpr hND)
  rcases hM.ih _ hcard _ htY hne with h1 | h2 | h3
  ·
    have h := (normalIn_map_iff N.subtype_injective).mpr h1
    rw [twoPrimeLayerIn_subgroupOf_map hYN, twoPrimeLayerIn_top_map] at h
    refine normalIn_of_le_normalizer (hCL.trans h.1) fun x hx => ?_
    have hxJ : x ∈ normalizer (J : Set G) := normalizer_le_of_even htJ
      ((twoPrimeLayerIn_le _).trans inf_le_left) hL4.even_card (normalIn_le_normalizer h hx)
    exact hNX (mem_inf.mpr ⟨twoPrimeLayerIn_le N hx, hxJ⟩)
  ·
    exfalso
    have h : CFSG.Open.pRank 2 (twoPrimeLayerIn (Y.subgroupOf N)) = 1 := h2
    rw [← pRank_map_subtype, twoPrimeLayerIn_subgroupOf_map hYN] at h
    have := hL4.two_le_pRank
    omega
  ·
    exfalso
    obtain ⟨h, -, -, T, hTN, -, hTY, n, hn, φ, hφ, hker⟩ := thm4Case3_subgroupOf hYN h3
    have hTJ : T ≤ normalizer (J : Set G) :=
      hTY.trans (normalizer_le_of_even htJ inf_le_left hYe)
    have hTX : T ≤ normalizer (X : Set G) := fun t ht => hNX (mem_inf.mpr ⟨hTN ht, hTJ ht⟩)
    have hLV : oUpperTwoPrime X ≤ oUpperTwoPrime (Y ⊔ T) :=
      oUpperTwoPrime_mono (hXY.trans le_sup_left)
    obtain ⟨hrange, hβker⟩ :=
      range_comp_inclusion_eq_prod hXn hTX hXs hX4.even_card hn φ hφ hker hLV
    obtain ⟨hψ, hψker⟩ := snd_comp_of_range_eq_prod _ hrange
    exact hJ (hS.mem_linkedClass_of_sl2 ⟨j, rfl⟩ rfl hcover hn hψ (hψker.trans hβker))

theorem stepConjNormalizer : StepConjNormalizer := by
  intro G _ _ Q hM hS g A hA hcover
  obtain ⟨⟨a, rfl⟩, -⟩ := hA
  set N := normalizer (linkedLayer Q : Set G)
  have hJ : rightConjugate (rightConjugate Q a) g⁻¹ = rightConjugate Q (a * g⁻¹) :=
    rightConjugate_mul Q a g⁻¹
  have hNg : rightConjugate (rightConjugate N g) g⁻¹ = N := by
    rw [rightConjugate_mul, mul_inv_cancel, rightConjugate_one]
  have hcov : twoPrimeLayerIn (rightConjugate Q (a * g⁻¹)) ≤
      (twoPrimeLayerIn (rightConjugate Q (a * g⁻¹)) ⊓ N) ⊔
        oddCoreIn (rightConjugate Q (a * g⁻¹)) := by
    have h := AschbacherTheorem3.rightConjugate_le_rightConjugate hcover g⁻¹
    rw [show rightConjugate ((twoPrimeLayerIn (rightConjugate Q a) ⊓ rightConjugate N g) ⊔
        oddCoreIn (rightConjugate Q a)) g⁻¹ =
        rightConjugate (twoPrimeLayerIn (rightConjugate Q a) ⊓ rightConjugate N g) g⁻¹ ⊔
          rightConjugate (oddCoreIn (rightConjugate Q a)) g⁻¹ from Subgroup.map_sup _ _ _,
      AschbacherTheorem3.rightConjugate_inf, hNg, ← twoPrimeLayerIn_rightConjugate,
      ← oddCoreIn_rightConjugate, hJ] at h
    exact h
  have key := normalIn_inf_normalizer_of_le_sup hM hS (a * g⁻¹) hcov
  have h := (normalIn_map_iff (f := (MulAut.conj g⁻¹).toMonoidHom)
    (MulAut.conj g⁻¹).injective).mpr key
  change NormalIn (rightConjugate (twoPrimeLayerIn (rightConjugate Q (a * g⁻¹)) ⊓ N) g)
    (rightConjugate (twoPrimeLayerIn N) g) at h
  rwa [AschbacherTheorem3.rightConjugate_inf, ← twoPrimeLayerIn_rightConjugate,
    ← twoPrimeLayerIn_rightConjugate, rightConjugate_mul, inv_mul_cancel_right] at h

end CFSG.ComponentClassification.Asc75T4
