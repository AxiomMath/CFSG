module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

import CFSG.GroupTheory.SubgroupCardMul
import CFSG.GroupTheory.Commutator.SupNormalizer

public section

set_option autoImplicit false

open scoped commutatorElement Pointwise

namespace CFSG.GroupTheory

theorem inf_centralizer_eq_zpowers_of_rank_three
    {X : Type*} [Group X] [Finite X]
    {E F L : Subgroup X} {e : X}
    (hE : CFSG.IsElementaryAbelian 2 ↥E)
    (hE8 : Nat.card ↥E = 8)
    (heE : e ∈ E)
    (he2 : orderOf e = 2)
    (heL : e ∈ Subgroup.centralizer (L : Set X))
    (hFE : F ≤ E)
    (hFne : F ≠ ⊥)
    (hFC : F ⊓ Subgroup.centralizer (L : Set X) = ⊥)
    (hcase : 4 ≤ Nat.card ↥F ∨
      ∃ Y : Subgroup X,
        Y ≤ Subgroup.normalizer (L : Set X) ∧
        Y ≤ Subgroup.centralizer (F : Set X) ∧
        ¬ ⁅Y, E⁆ ≤ Subgroup.centralizer (L : Set X)) :
    E ⊓ Subgroup.centralizer (L : Set X) = Subgroup.zpowers e := by
  let C : Subgroup X := Subgroup.centralizer (L : Set X)
  let B : Subgroup X := E ⊓ C
  let D : Subgroup X := Subgroup.zpowers e
  have hDleE : D ≤ E := Subgroup.zpowers_le.mpr heE
  have hDleC : D ≤ C := Subgroup.zpowers_le.mpr heL
  have hDleB : D ≤ B := le_inf hDleE hDleC
  have hDcard : Nat.card D = 2 := by
    rw [show D = Subgroup.zpowers e from rfl, Nat.card_zpowers, he2]
  have h2dvdB : 2 ∣ Nat.card B := by
    simpa [hDcard] using Subgroup.card_dvd_of_le hDleB
  have hFB : F ⊓ B = ⊥ := by
    change F ⊓ (E ⊓ C) = ⊥
    rw [← inf_assoc]
    change (F ⊓ E) ⊓ C = ⊥
    rw [inf_eq_left.mpr hFE]
    change F ⊓ Subgroup.centralizer (L : Set X) = ⊥
    exact hFC
  have hBleE : B ≤ E := inf_le_left
  have hprodE : Nat.card F * Nat.card B ≤ Nat.card E :=
    CFSG.card_mul_card_le_of_inf_eq_bot hFE hBleE hFB
  have hprodE8 : Nat.card F * Nat.card B ≤ 8 := by
    simpa [hE8] using hprodE
  have hBD : B = D := by
    by_contra hne
    have h4B : 4 ≤ Nat.card B := by
      by_cases hBle2 : Nat.card B ≤ 2
      · have hDB : D = B :=
          Subgroup.eq_of_le_of_card_ge hDleB (by rwa [hDcard])
        exact absurd hDB.symm hne
      · have h2lt : 2 < Nat.card B := Nat.lt_of_not_ge hBle2
        obtain ⟨k, hk⟩ := h2dvdB
        have hk2 : 2 ≤ k := by
          by_contra hk2
          have hk1 : k ≤ 1 := Nat.le_of_lt_succ (Nat.lt_of_not_ge hk2)
          have h2kle : 2 * k ≤ 2 := by
            simpa using Nat.mul_le_mul_left 2 hk1
          have h2k : 2 < 2 * k := by rwa [hk] at h2lt
          exact absurd (lt_of_lt_of_le h2k h2kle) (lt_irrefl 2)
        have h4 : 4 ≤ 2 * k := by
          calc 4 = 2 * 2 := rfl
            _ ≤ 2 * k := Nat.mul_le_mul_left 2 hk2
        simpa [hk] using h4
    rcases hcase with hF4 | ⟨Y, hYNL, hYCF, hYnot⟩
    · have h16 : 16 ≤ Nat.card F * Nat.card B := by
        calc 16 = 4 * 4 := rfl
          _ ≤ Nat.card F * Nat.card B := Nat.mul_le_mul hF4 h4B
      linarith
    · have hF2 : 2 ≤ Nat.card F := by
        have h : 1 < Nat.card F := (Subgroup.one_lt_card_iff_ne_bot F).mpr hFne
        exact Nat.succ_le_of_lt h
      have hBF : B ⊓ F = ⊥ := by rwa [inf_comm]
      have hprodBF : Nat.card B * Nat.card F ≤ Nat.card ↥(B ⊔ F) :=
        CFSG.card_mul_card_le_of_inf_eq_bot (A := B ⊔ F) (D := B) (D' := F)
          le_sup_left le_sup_right hBF
      have h8le : 8 ≤ Nat.card ↥(B ⊔ F) := by
        calc 8 = 4 * 2 := rfl
          _ ≤ Nat.card B * Nat.card F := Nat.mul_le_mul h4B hF2
          _ ≤ Nat.card ↥(B ⊔ F) := hprodBF
      have hBFleE : B ⊔ F ≤ E := sup_le hBleE hFE
      have hBFE : B ⊔ F = E :=
        Subgroup.eq_of_le_of_card_ge hBFleE (by simpa [hE8] using h8le)
      have hNCN : Subgroup.normalizer (L : Set X) ≤ Subgroup.normalizer (C : Set X) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer
          (Subgroup.centralizer_le_normalizer (L : Set X))).mp
          (Subgroup.normal_subgroupOf_centralizer_normalizer (L : Set X))
      have hYNC : Y ≤ Subgroup.normalizer (C : Set X) := le_trans hYNL hNCN
      have hCY : ⁅C, Y⁆ ≤ C :=
        (Subgroup.le_normalizer_iff_commutator_le_left).mp hYNC
      have hBY : ⁅B, Y⁆ ≤ C :=
        le_trans (Subgroup.commutator_mono inf_le_right le_rfl) hCY
      have hFBcent : F ≤ Subgroup.centralizer (B : Set X) := by
        intro f hf
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        have hbE : b ∈ E := (Subgroup.mem_inf.mp hb).1
        have : IsMulCommutative ↥E := hE.toIsMulCommutative
        have hc := congrArg Subtype.val
          (mul_comm' (⟨f, hFE hf⟩ : E) (⟨b, hbE⟩ : E))
        simpa using hc.symm
      have hFN : F ≤ Subgroup.normalizer (B : Set X) :=
        le_trans hFBcent (Subgroup.centralizer_le_normalizer (B : Set X))
      have hFY : F ≤ Subgroup.centralizer (Y : Set X) :=
        (Subgroup.le_centralizer_iff).mp hYCF
      have hcomm := CFSG.commutator_sup_eq_commutator_left
        (A := B) (B := F) (U := Y) hFN hFY
      have hEY : ⁅E, Y⁆ ≤ C := by
        rw [← hBFE, hcomm]
        exact hBY
      have hYE : ⁅Y, E⁆ ≤ C := by
        rw [Subgroup.commutator_comm Y E]
        exact hEY
      exact absurd hYE hYnot
  change B = D
  exact hBD

end CFSG.GroupTheory
