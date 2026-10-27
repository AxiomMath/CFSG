module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.InspectionArms
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.InspectionCommon
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.InvolutionCentralizers
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.OutSmallSporadic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.CenterFree

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem inspectionArm_m22 :
    InspectionArm fun N _ => IsSporadic N .M22 := by
  intro Y _ _ N hN hC hQ P _ _ _ _ hw
  haveI := hN
  exfalso
  have hZ : center ↥N = ⊥ := center_eq_bot_of_isSporadic_m22 hQ
  have hidx : N.index ≤ 2 :=
    index_le_of_card_mulAut_le hC hZ (card_mulAut_le_of_isSporadic_m22 hQ)
  obtain ⟨w, hw2, H, A, hH, _, _, _, hAH, hAN, hA, _, _, _⟩ :=
    exists_simple_le_of_pgl29 (Y := Y) (N := N) (by omega) hw
  have hAw : A ≤ centralizer ({w} : Set Y) := hAH.trans hH
  by_cases hwN : w ∈ N
  · have hwN2 : orderOf (⟨w, hwN⟩ : ↥N) = 2 := (Subgroup.orderOf_mk w hwN).trans hw2
    have hdvd : Nat.card A ∣ Nat.card (centralizer ({(⟨w, hwN⟩ : ↥N)} : Set ↥N)) :=
      card_dvd_card_centralizer_of_le hAN hwN hAw
    rw [hA, card_centralizer_of_involution_of_isSporadic_m22 hQ (⟨w, hwN⟩ : ↥N) hwN2]
      at hdvd
    exact absurd hdvd (by norm_num)
  · have hα2 := orderOf_conjNormal_eq_two hC hw2 hwN
    have hout := conjNormal_not_mem_inner hC hwN
    have hdvd : Nat.card A ∣
        Nat.card {x : ↥N // (MulAut.conjNormal w : MulAut ↥N) x = x} :=
      card_dvd_card_fixed_of_le hAN hAw
    rw [hA] at hdvd
    rcases card_fixed_of_outer_involution_of_isSporadic_m22 hQ (MulAut.conjNormal w) hα2 hout
      with h | h
    · rw [h] at hdvd
      exact absurd hdvd (by norm_num)
    · rw [h] at hdvd
      exact absurd hdvd (by norm_num)

theorem inspectionArm_m23 :
    InspectionArm fun N _ => IsSporadic N .M23 := by
  intro Y _ _ N hN hC hQ P _ _ _ _ hw
  haveI := hN
  exfalso
  have hZ : center ↥N = ⊥ := center_eq_bot_of_isSporadic_m23 hQ
  have hidx : N.index ≤ 1 :=
    index_le_of_card_mulAut_le hC hZ (card_mulAut_le_of_isSporadic_m23 hQ)
  obtain ⟨w, hw2, H, A, hH, _, _, _, hAH, hAN, hA, _, _, _⟩ :=
    exists_simple_le_of_pgl29 (Y := Y) (N := N) (by omega) hw
  have hAw : A ≤ centralizer ({w} : Set Y) := hAH.trans hH
  by_cases hwN : w ∈ N
  · have hwN2 : orderOf (⟨w, hwN⟩ : ↥N) = 2 := (Subgroup.orderOf_mk w hwN).trans hw2
    have hdvd : Nat.card A ∣ Nat.card (centralizer ({(⟨w, hwN⟩ : ↥N)} : Set ↥N)) :=
      card_dvd_card_centralizer_of_le hAN hwN hAw
    rw [hA, card_centralizer_of_involution_of_isSporadic_m23 hQ (⟨w, hwN⟩ : ↥N) hwN2]
      at hdvd
    exact absurd hdvd (by norm_num)
  · have h1 : N.index = 1 := by
      have hne : N.index ≠ 0 := Subgroup.index_ne_zero_of_finite
      omega
    exact hwN (by simp [Subgroup.index_eq_one.mp h1])

theorem inspectionArm_m24 :
    InspectionArm fun N _ => IsSporadic N .M24 := by
  intro Y _ _ N hN hC hQ P _ _ _ _ hw
  haveI := hN
  exfalso
  have hZ : center ↥N = ⊥ := center_eq_bot_of_isSporadic_m24 hQ
  have hidx : N.index ≤ 1 :=
    index_le_of_card_mulAut_le hC hZ (card_mulAut_le_of_isSporadic_m24 hQ)
  obtain ⟨w, hw2, H, A, hH, _, _, _, hAH, hAN, hA, _, _, _⟩ :=
    exists_simple_le_of_pgl29 (Y := Y) (N := N) (by omega) hw
  have hAw : A ≤ centralizer ({w} : Set Y) := hAH.trans hH
  by_cases hwN : w ∈ N
  · have hwN2 : orderOf (⟨w, hwN⟩ : ↥N) = 2 := (Subgroup.orderOf_mk w hwN).trans hw2
    have hdvd : Nat.card A ∣ Nat.card (centralizer ({(⟨w, hwN⟩ : ↥N)} : Set ↥N)) :=
      card_dvd_card_centralizer_of_le hAN hwN hAw
    rw [hA] at hdvd
    rcases card_centralizer_of_involution_of_isSporadic_m24 hQ (⟨w, hwN⟩ : ↥N) hwN2
      with h | h
    · rw [h] at hdvd
      exact absurd hdvd (by norm_num)
    · rw [h] at hdvd
      exact absurd hdvd (by norm_num)
  · have h1 : N.index = 1 := by
      have hne : N.index ≠ 0 := Subgroup.index_ne_zero_of_finite
      omega
    exact hwN (by simp [Subgroup.index_eq_one.mp h1])

theorem inspectionArm_ru :
    InspectionArm fun N _ => IsSporadic N .Ru := by
  intro Y _ _ N hN hC hQ P _ _ _ _ hw
  haveI := hN
  exfalso
  have hZ : center ↥N = ⊥ := center_eq_bot_of_isSporadic_ru hQ
  have hidx : N.index ≤ 1 :=
    index_le_of_card_mulAut_le hC hZ (card_mulAut_le_of_isSporadic_ru hQ)
  obtain ⟨w, hw2, H, A, hH, _, _, _, hAH, hAN, hA, _, _, _⟩ :=
    exists_simple_le_of_pgl29 (Y := Y) (N := N) (by omega) hw
  have hAw : A ≤ centralizer ({w} : Set Y) := hAH.trans hH
  by_cases hwN : w ∈ N
  · have hwN2 : orderOf (⟨w, hwN⟩ : ↥N) = 2 := (Subgroup.orderOf_mk w hwN).trans hw2
    have hdvd : Nat.card A ∣ Nat.card (centralizer ({(⟨w, hwN⟩ : ↥N)} : Set ↥N)) :=
      card_dvd_card_centralizer_of_le hAN hwN hAw
    rw [hA] at hdvd
    rcases card_centralizer_of_involution_of_isSporadic_ru hQ (⟨w, hwN⟩ : ↥N) hwN2
      with h | h
    · rw [h] at hdvd
      exact absurd hdvd (by norm_num)
    · rw [h] at hdvd
      exact absurd hdvd (by norm_num)
  · have h1 : N.index = 1 := by
      have hne : N.index ≠ 0 := Subgroup.index_ne_zero_of_finite
      omega
    exact hwN (by simp [Subgroup.index_eq_one.mp h1])

theorem inspectionArm_j2 :
    InspectionArm fun N _ => IsSporadic N .J2 := by
  intro Y _ _ N hN hC hQ P _ _ _ _ hw
  haveI := hN
  exfalso
  have hZ : center ↥N = ⊥ := center_eq_bot_of_isSporadic_j2 hQ
  have hidx : N.index ≤ 2 :=
    index_le_of_card_mulAut_le hC hZ (card_mulAut_le_of_isSporadic_j2 hQ)
  obtain ⟨w, hw2, H, A, hH, _, _, _, hAH, hAN, hA, _, _, _⟩ :=
    exists_simple_le_of_pgl29 (Y := Y) (N := N) (by omega) hw
  have hAw : A ≤ centralizer ({w} : Set Y) := hAH.trans hH
  by_cases hwN : w ∈ N
  · have hwN2 : orderOf (⟨w, hwN⟩ : ↥N) = 2 := (Subgroup.orderOf_mk w hwN).trans hw2
    have hdvd : Nat.card A ∣ Nat.card (centralizer ({(⟨w, hwN⟩ : ↥N)} : Set ↥N)) :=
      card_dvd_card_centralizer_of_le hAN hwN hAw
    rw [hA] at hdvd
    rcases card_centralizer_of_involution_of_isSporadic_j2 hQ (⟨w, hwN⟩ : ↥N) hwN2
      with h | h
    · rw [h] at hdvd
      exact absurd hdvd (by norm_num)
    · rw [h] at hdvd
      exact absurd hdvd (by norm_num)
  · have hα2 := orderOf_conjNormal_eq_two hC hw2 hwN
    have hout := conjNormal_not_mem_inner hC hwN
    have hdvd : Nat.card A ∣
        Nat.card {x : ↥N // (MulAut.conjNormal w : MulAut ↥N) x = x} :=
      card_dvd_card_fixed_of_le hAN hAw
    rw [hA, card_fixed_of_outer_involution_of_isSporadic_j2 hQ (MulAut.conjNormal w) hα2 hout]
      at hdvd
    exact absurd hdvd (by norm_num)

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan
