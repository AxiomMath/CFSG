module

public import CFSG.LocalAnalysis.ComponentInitial.SLTwoInvolution

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S1IdentSl2

open CFSG Subgroup CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

theorem sl2_card_mono {a b : ℕ} (h : a ≤ b) : a * (a ^ 2 - 1) ≤ b * (b ^ 2 - 1) := by
  apply Nat.mul_le_mul h
  apply Nat.sub_le_sub_right
  exact Nat.pow_le_pow_left h 2

theorem le_card_sl2 {q : ℕ} (h : 5 ≤ q) : 120 ≤ q * (q ^ 2 - 1) :=
  calc 120 = 5 * (5 ^ 2 - 1) := by norm_num
    _ ≤ q * (q ^ 2 - 1) := sl2_card_mono h

theorem not_sl2_dvd_5616 (q : ℕ) (hq5 : 5 ≤ q) : ¬ q * (q ^ 2 - 1) ∣ 5616 := by
  intro hdvd
  by_cases hq : q ≤ 17
  · interval_cases q <;> norm_num at hdvd
  · have h1 : 5814 ≤ q * (q ^ 2 - 1) :=
      calc 5814 = 18 * (18 ^ 2 - 1) := by norm_num
        _ ≤ q * (q ^ 2 - 1) := sl2_card_mono (by omega)
    have h2 := Nat.le_of_dvd (by norm_num) hdvd
    omega

theorem card_sl2 {F : Type} [Field F] [Finite F] :
    Nat.card SL(2, F) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  rw [Matrix.card_SL_field, Fin.prod_univ_two, ← Nat.card_eq_fintype_card]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  set q := Nat.card F with hq
  have hq1 : 2 ≤ q := by
    have := Fintype.one_lt_card (α := F)
    rw [← Nat.card_eq_fintype_card] at this
    omega
  have h1 : q ^ 2 - q = q * (q - 1) := by
    rw [Nat.mul_sub_one, sq]
  rw [h1, show (q ^ 2 - 1) * (q * (q - 1)) = q * (q ^ 2 - 1) * (q - 1) by ring,
    Nat.mul_div_cancel _ (by omega)]

theorem ringChar_ne_two {F : Type} [Field F] [Fintype F] (hodd : Odd (Fintype.card F)) :
    ringChar F ≠ 2 := by
  rw [Ne, FiniteField.even_card_iff_char_two]
  have := Nat.odd_iff.1 hodd
  omega

theorem exists_quaternion_hom {G : Type} [Group G] {F : Type} [Field F] [Finite F]
    (hk : ringChar F ≠ 2) (ι : SL(2, F) →* G) (hι : Function.Injective ι) :
    ∃ τ : QuaternionGroup 2 →* G, Function.Injective τ := by
  obtain ⟨-, -, -, H, -, -, ⟨e⟩⟩ := sl2_exists_quaternion_subgroup hk
  exact ⟨ι.comp (H.subtype.comp e.toMonoidHom),
    hι.comp (H.subtype_injective.comp e.injective)⟩

end S1IdentSl2

end CFSG.GH74.Generic.BProg.B3
