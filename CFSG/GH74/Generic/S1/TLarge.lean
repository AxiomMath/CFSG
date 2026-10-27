module

public import CFSG.GH74.Generic.S1.RCard
public import CFSG.GH74.Generic.S1.SymNbhd

public section

namespace CFSG.GH74.Generic.S1

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Subgroup CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

theorem card_statedSL_four (F : Type) [Field F] [Finite F] :
    Nat.card ↥(StatedSL 4 F) = Nat.card F ^ 6 *
      ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 4 - 1)) := by
  rw [← Nat.card_congr (specialLinearGroupEquivStatedSL 4 F).toEquiv,
    CFSG.OrderReductions.LinearOrders.card_specialLinear F 4 (by norm_num)]
  rw [show Finset.Icc 2 4 = {2, 3, 4} by decide]
  simp [Finset.prod_insert, mul_assoc]

theorem card_statedSL_four_three {F : Type} [Field F] [Finite F] (hF : Nat.card F = 3) :
    Nat.card ↥(StatedSL 4 F) = 12130560 := by
  rw [card_statedSL_four, hF]
  norm_num

theorem lt_card_statedSL_four {F : Type} [Field F] [Finite F] (hF : 4 ≤ Nat.card F) :
    12130560 < Nat.card ↥(StatedSL 4 F) := by
  rw [card_statedSL_four]
  set q := Nat.card F with hq
  have h1 : 4 ^ 6 ≤ q ^ 6 := Nat.pow_le_pow_left hF 6
  have h2 : 4 ^ 2 - 1 ≤ q ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hF 2) 1
  have h3 : 4 ^ 3 - 1 ≤ q ^ 3 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hF 3) 1
  have h4 : 4 ^ 4 - 1 ≤ q ^ 4 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hF 4) 1
  calc 12130560 < 4 ^ 6 * ((4 ^ 2 - 1) * (4 ^ 3 - 1) * (4 ^ 4 - 1)) := by norm_num
    _ ≤ q ^ 6 * ((q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1)) :=
      Nat.mul_le_mul h1 (Nat.mul_le_mul (Nat.mul_le_mul h2 h3) h4)

theorem lt_card_statedSU_four {F : Type} [Field F] [Finite F] {q : ℕ} (hF : Nat.card F = q ^ 2)
    (hq : 5 ≤ q) : 12130560 < Nat.card ↥(StatedSU 4 q F) := by
  obtain ⟨p, f, h, rfl⟩ := rcard_exists_unitaryFieldData hF
  have hform := rcard_card_statedSU h (n := 4) (by norm_num)
  rw [show Finset.Icc 2 4 = {2, 3, 4} by decide, Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton] at hform
  set Q : ℕ := p ^ f with hQ
  have hform' : (Nat.card ↥(StatedSU 4 Q F) : ℤ) =
      (Q : ℤ) ^ 6 * (((Q : ℤ) ^ 2 - 1) * (((Q : ℤ) ^ 3 + 1) * ((Q : ℤ) ^ 4 - 1))) := by
    rw [hform]
    norm_num
  have hQz : (5 : ℤ) ≤ (Q : ℤ) := by exact_mod_cast hq
  have h6 : (5 : ℤ) ^ 6 ≤ (Q : ℤ) ^ 6 := pow_le_pow_left₀ (by norm_num) hQz 6
  have h2 : (24 : ℤ) ≤ (Q : ℤ) ^ 2 - 1 := by nlinarith
  have h3 : (126 : ℤ) ≤ (Q : ℤ) ^ 3 + 1 := by
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℤ) ≤ 5) hQz 3]
  have h4 : (624 : ℤ) ≤ (Q : ℤ) ^ 4 - 1 := by
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℤ) ≤ 5) hQz 4]
  have hprod : (24 : ℤ) * (126 * 624) ≤
      ((Q : ℤ) ^ 2 - 1) * (((Q : ℤ) ^ 3 + 1) * ((Q : ℤ) ^ 4 - 1)) :=
    mul_le_mul h2 (mul_le_mul h3 h4 (by norm_num) (by linarith)) (by norm_num) (by linarith)
  have hlt : (12130560 : ℤ) < (Nat.card ↥(StatedSU 4 Q F) : ℤ) := by
    rw [hform']
    have := mul_le_mul h6 hprod (by norm_num) (by positivity)
    norm_num at this ⊢
    linarith
  exact_mod_cast hlt

theorem three_lt_card_of_largeModel {C : Type} [Group C] {K : Subgroup C}
    (hbig : S1LargeModel K) {F : Type} [Field F] [Finite F] (hF4 : Nat.card F % 4 = 3)
    (hFK : Nonempty (↥K ≃* ↥(StatedSL 4 F))) : 3 < Nat.card F := by
  by_contra hle
  obtain ⟨eF⟩ := hFK
  have hcardF : Nat.card ↥K = Nat.card ↥(StatedSL 4 F) := Nat.card_congr eF.toEquiv
  have hF3 : Nat.card F = 3 := by omega
  rw [card_statedSL_four_three hF3] at hcardF
  rcases hbig with ⟨F', _, _, hF'4, hF'3, ⟨e'⟩⟩ | ⟨q, F', _, _, hF', hq, ⟨e'⟩⟩
  · have hc := Nat.card_congr e'.toEquiv
    have := lt_card_statedSL_four (F := F') (by omega)
    omega
  · have hc := Nat.card_congr e'.toEquiv
    have hq5 : 5 ≤ q := by
      have h1 : 1 < Nat.card F' := Finite.one_lt_card
      rw [hF'] at h1
      have hq1 : 1 < q := by
        by_contra hle'
        have hle'' : q ≤ 1 := by omega
        interval_cases q <;> simp at h1
      omega
    have := lt_card_statedSU_four hF' hq5
    omega

end CFSG.GH74.Generic.S1
