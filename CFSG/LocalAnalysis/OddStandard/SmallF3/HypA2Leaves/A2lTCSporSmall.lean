module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lTCBasic
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpP1SporSmall
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitFixedHe
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixA
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixB
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1SporLie

public section

set_option linter.unusedSectionVars false

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG.Blueprint CFSG.ComponentClassification CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.GS82PumpInputs
open CFSG.ComponentClassification.HarrisLit.T1.SporRow
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section Numerics

theorem a2l_not_dvd_of_tcSmall {Q : Type} [Group Q] (hS : TCSmall Q) {N : ℕ}
    (hN : N ∈ ({48, 120, 192, 240, 320, 336, 384, 1344, 1920, 2448, 2688, 7680, 21504} :
      Finset ℕ)) : ¬ Nat.card Q ∣ N := by
  have key : ∀ c ∈ ({360, 6048, 25920} : Finset ℕ),
      ∀ N ∈ ({48, 120, 192, 240, 320, 336, 384, 1344, 1920, 2448, 2688, 7680, 21504} :
        Finset ℕ), ¬ c ∣ N := by decide
  rcases a2l_card_tcSmall hS with h | h | h <;> rw [h] <;> exact key _ (by simp) N hN

end Numerics

section OddOrder


theorem a2l_oddLieOrder_of_tcSmall {Q : Type} [Group Q] (hS : TCSmall Q) :
    OddLieOrder (Nat.card Q) := by
  rcases hS with h | h | h <;> exact oddLieOrder_of_lieModel Nat.prime_three (by norm_num) h

end OddOrder

section M11


theorem a2l_false_of_m11 {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (e : S ≃* NativeSporadic.M11) {σ : MulAut S} {P : Subgroup S}
    (h : ProperFixedComponent σ P) (hS : TCSmall (↥P ⧸ Open.fusionZStar ↥P)) : False := by
  have hd := SporSmall.card_dvd_fixed h
  rw [CatFC.card_fixedSubgroup_m11 e (SporSmall.orderOf_eq_two h)] at hd
  exact a2l_not_dvd_of_tcSmall hS (by decide) hd

end M11

section M12


theorem a2l_false_of_m12 {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (e : S ≃* NativeSporadic.M12) {σ : MulAut S} {P : Subgroup S}
    (h : ProperFixedComponent σ P) (hS : TCSmall (↥P ⧸ Open.fusionZStar ↥P)) : False := by
  have hd := SporSmall.card_dvd_fixed h
  rcases CatFC.card_fixedSubgroup_m12 e (SporSmall.orderOf_eq_two h) with hc | hc | hc <;>
    (rw [hc] at hd; exact a2l_not_dvd_of_tcSmall hS (by decide) hd)

end M12

section M22


theorem a2l_false_of_m22 {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (e : S ≃* NativeSporadic.M22) {σ : MulAut S} {P : Subgroup S}
    (h : ProperFixedComponent σ P) (hS : TCSmall (↥P ⧸ Open.fusionZStar ↥P)) : False := by
  have hd := SporSmall.card_dvd_fixed h
  rcases SporFix.card_fixedSubgroup_m22 e (SporSmall.orderOf_eq_two h) with hc | hc | hc <;>
    (rw [hc] at hd; exact a2l_not_dvd_of_tcSmall hS (by decide) hd)

end M22

section M23


theorem a2l_false_of_m23 {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (e : S ≃* NativeSporadic.M23) {σ : MulAut S} {P : Subgroup S}
    (h : ProperFixedComponent σ P) (hS : TCSmall (↥P ⧸ Open.fusionZStar ↥P)) : False := by
  have hd := SporSmall.card_dvd_fixed h
  rw [SporFix.card_fixedSubgroup_m23 e (SporSmall.orderOf_eq_two h)] at hd
  exact a2l_not_dvd_of_tcSmall hS (by decide) hd

end M23

section M24


theorem a2l_false_of_m24 {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (e : S ≃* NativeSporadic.M24) {σ : MulAut S} {P : Subgroup S}
    (h : ProperFixedComponent σ P) (hS : TCSmall (↥P ⧸ Open.fusionZStar ↥P)) : False := by
  have hd := SporSmall.card_dvd_fixed h
  rcases SporFix.card_fixedSubgroup_m24 e (SporSmall.orderOf_eq_two h) with hc | hc <;>
    (rw [hc] at hd; exact a2l_not_dvd_of_tcSmall hS (by decide) hd)

end M24

section J1


theorem a2l_false_of_j1 {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a)
    (e : S ≃* NativeSporadic.J1) {σ : MulAut S} {P : Subgroup S}
    (h : ProperFixedComponent σ P) (hS : TCSmall (↥P ⧸ Open.fusionZStar ↥P)) : False := by
  have hd := SporSmall.card_dvd_fixed h
  rw [SporFix.card_fixedSubgroup_j1 hna e h] at hd
  exact a2l_not_dvd_of_tcSmall hS (by decide) hd

end J1

section J2


theorem a2l_false_of_j2 {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (e : S ≃* NativeSporadic.J2) {σ : MulAut S} {P : Subgroup S}
    (h : ProperFixedComponent σ P) (hS : TCSmall (↥P ⧸ Open.fusionZStar ↥P)) : False := by
  have hd := SporSmall.card_dvd_fixed h
  rcases SporFix.card_fixedSubgroup_j2 e (SporSmall.orderOf_eq_two h) with hc | hc | hc <;>
    (rw [hc] at hd; exact a2l_not_dvd_of_tcSmall hS (by decide) hd)

end J2

section J3


theorem a2l_false_of_j3 {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (e : S ≃* NativeSporadic.J3) {σ : MulAut S} {P : Subgroup S}
    (h : ProperFixedComponent σ P) (hS : TCSmall (↥P ⧸ Open.fusionZStar ↥P)) : False := by
  have hd := SporSmall.card_dvd_fixed h
  rcases CatFC.card_fixedSubgroup_j3 e (SporSmall.orderOf_eq_two h) with hc | hc <;>
    (rw [hc] at hd; exact a2l_not_dvd_of_tcSmall hS (by decide) hd)

end J3

section HE


theorem a2l_false_of_he {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.He) {σ : MulAut S}
    {P : Subgroup S} (h : ProperFixedComponent σ P)
    (hS : TCSmall (↥P ⧸ Open.fusionZStar ↥P)) : False := by
  rcases GrSLit.simpleFixedComponents_held GrSLit.HeldFix.isL34Type_of_isPComponent_centralizer_heA0
      GrSLit.HeldFix.not_isPComponent_centralizer_heT1P S
      inferInstance hna ⟨e⟩ σ h.1 P h.2.1 h.2.2.1 h.2.2.2 with hL34 | hA7
  · have hc := GH74.card_of_lieModel_PSL (G := ↥P ⧸ Open.fusionZStar ↥P) (n := 3) (p := 2)
      (f := 2) (by norm_num) hL34
    have h20160 : Nat.card (↥P ⧸ Open.fusionZStar ↥P) = 20160 := by rw [hc]; decide
    rcases a2l_card_tcSmall hS with h | h | h <;> omega
  · obtain ⟨eA⟩ := hA7
    have h2520 : Nat.card (↥P ⧸ Open.fusionZStar ↥P) = 2520 := by
      rw [ComponentClassification.SolMax.card_of_mulEquiv_alt (by norm_num) eA]
      decide
    rcases a2l_card_tcSmall hS with h | h | h <;> omega

end HE

end CFSG.OddStandard.SmallF3.HypA2Leaves
