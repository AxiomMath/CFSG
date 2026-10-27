module

public import CFSG.LocalAnalysis.GLTheoremA.S10.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K148Inner

open CFSG.LocalAnalysis.GLTheoremA.S10

theorem natCard_SL3 (F : Type) [Field F] [Finite F] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) =
      Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1) := by
  haveI : Fintype F := Fintype.ofFinite F
  have hq : 2 ≤ Fintype.card F := Fintype.one_lt_card
  rw [Matrix.card_SL_field, Nat.card_eq_fintype_card, Fin.prod_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
  generalize Fintype.card F = q at hq ⊢
  have key : (q ^ 3 - 1) * (q ^ 3 - q) * (q ^ 3 - q ^ 2) =
      (q - 1) * (q ^ 3 * (q ^ 3 - 1) * (q ^ 2 - 1)) := by
    have h1 : 1 ≤ q := by omega
    have h2 : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
    have h3 : q ^ 2 ≤ q ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have h4 : q ≤ q ^ 3 := le_trans h2 h3
    have h5 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
    have h6 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [h1, h2, h3, h4, h5, h6]
    ring
  rw [key, Nat.mul_div_cancel_left _ (by omega)]

theorem two_pow_three_le_twoPart {f n : ℕ} (hn : n ≠ 0) (h : (2 ^ f) ^ 3 ∣ n) :
    (2 ^ f) ^ 3 ≤ twoPart n := by
  rw [← pow_mul] at h
  have h' : f * 3 ≤ n.factorization 2 := (Nat.prime_two.pow_dvd_iff_le_factorization hn).1 h
  unfold twoPart
  rw [← pow_mul]
  exact Nat.pow_le_pow_right (by norm_num) h'

theorem natCard_centralizer_conj {G : Type*} [Group G] (g x : G) :
    Nat.card (Subgroup.centralizer ({g * x * g⁻¹} : Set G)) =
      Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  refine Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj g⁻¹).toEquiv (fun y => ?_))
  show y ∈ Subgroup.centralizer ({g * x * g⁻¹} : Set G) ↔
    g⁻¹ * y * g⁻¹⁻¹ ∈ Subgroup.centralizer ({x} : Set G)
  simp only [Subgroup.mem_centralizer_singleton_iff, inv_inv]
  constructor
  · intro h
    have h' : g⁻¹ * (y * (g * x * g⁻¹)) * g = g⁻¹ * ((g * x * g⁻¹) * y) * g := by rw [h]
    calc g⁻¹ * y * g * x = g⁻¹ * (y * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * y) * g := h'
      _ = x * (g⁻¹ * y * g) := by group
  · intro h
    have h' : g * (g⁻¹ * y * g * x) * g⁻¹ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [h]
    calc y * (g * x * g⁻¹) = g * (g⁻¹ * y * g * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := h'
      _ = g * x * g⁻¹ * y := by group

theorem two_pow_mod_three_of_even {f : ℕ} (h : f % 2 = 0) : 2 ^ f % 3 = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, f = 2 * m := ⟨f / 2, by omega⟩
  rw [pow_mul, Nat.pow_mod]
  norm_num

theorem two_pow_mod_three_of_odd {f : ℕ} (h : f % 2 = 1) : 2 ^ f % 3 = 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, f = 2 * m + 1 := ⟨f / 2, by omega⟩
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

end CFSG.LocalAnalysis.GLTheoremA.K148Inner

end
