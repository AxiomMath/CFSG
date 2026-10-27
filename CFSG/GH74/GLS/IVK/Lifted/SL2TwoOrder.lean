module

public import CFSG.GH74.GLS.IVK.Lifted.SL2Aut

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup Matrix CFSG CFSG.GorensteinWalter CFSG.ABGLocalTools

theorem orderOf_dihedral_le {n : ℕ} [NeZero n] (hn : 2 ≤ n) (y : DihedralGroup n) : orderOf y ≤ n := by
  cases y with
  | r i =>
    rw [DihedralGroup.orderOf_r]
    exact Nat.div_le_self _ _
  | sr i =>
    rw [DihedralGroup.orderOf_sr]
    exact hn

variable {F : Type} [Field F] [Finite F]

theorem card_sl2_eq_two_mul_card_psl2 (hodd : Odd (Nat.card F)) :
    Nat.card (SpecialLinearGroup (Fin 2) F) = 2 * Nat.card (PSL2 F) := by
  rw [psl2_card_formula F (isOddPrimePower_card_of_odd hodd),
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
  have h := even_card_sl2 hodd
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two] at h
  exact (Nat.mul_div_cancel' (even_iff_two_dvd.1 h)).symm

theorem two_power_order_sl2_le (hodd : Odd (Nat.card F)) (c : SpecialLinearGroup (Fin 2) F) {k : ℕ}
    (hc : orderOf c = 2 ^ k) :
    2 ^ (k + 1) ≤ 2 ^ (Nat.card (SpecialLinearGroup (Fin 2) F)).factorization 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOdd := isOddPrimePower_card_of_odd hodd
  set Z := Subgroup.center (SpecialLinearGroup (Fin 2) F) with hZ
  let π : SpecialLinearGroup (Fin 2) F →* PSL2 F := QuotientGroup.mk' Z
  have hdih := psl2_odd_hasDihedralSylowTwo_model F hOdd
  have hcard := card_sl2_eq_two_mul_card_psl2 hodd
  have hpsl0 : Nat.card (PSL2 F) ≠ 0 := Nat.card_pos.ne'
  have hfac : (Nat.card (SpecialLinearGroup (Fin 2) F)).factorization 2 =
      (Nat.card (PSL2 F)).factorization 2 + 1 := by
    rw [hcard, Nat.factorization_mul (by norm_num) hpsl0]
    simp only [Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_two]
    ring
  set cb : PSL2 F := π c with hcb
  have h1 : orderOf cb ∣ 2 ^ k := hc ▸ orderOf_map_dvd π c
  have h2 : 2 ^ k ∣ 2 * orderOf cb := by
    rw [← hc]
    apply orderOf_dvd_of_pow_eq_one
    have hmem : c ^ orderOf cb ∈ Z := by
      rw [← QuotientGroup.eq_one_iff]
      change π (c ^ orderOf cb) = 1
      rw [map_pow]
      exact pow_orderOf_eq_one cb
    have hsq := sq_eq_one_of_mem_center_sl2 hmem
    calc c ^ (2 * orderOf cb) = (c ^ orderOf cb) * (c ^ orderOf cb) := by rw [two_mul, pow_add]
      _ = 1 := hsq
  obtain ⟨i, hi, hti⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  have hP2 : IsPGroup 2 ↥(zpowers cb) :=
    IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hti])
  obtain ⟨S₀, hS₀⟩ := hP2.exists_le_sylow
  obtain ⟨m, hm1, ⟨d⟩⟩ := hdih S₀
  have : NeZero (2 ^ m) := ⟨by positivity⟩
  have hSc : Nat.card (S₀ : Subgroup (PSL2 F)) = 2 ^ (m + 1) := by
    rw [Nat.card_congr d.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card, pow_succ]
    ring
  have hSm := Sylow.card_eq_multiplicity S₀
  have hv : (Nat.card (PSL2 F)).factorization 2 = m + 1 :=
    Nat.pow_right_injective (le_refl 2) (hSm.symm.trans hSc)
  have hmem : cb ∈ (S₀ : Subgroup (PSL2 F)) := hS₀ (mem_zpowers cb)
  have hord : orderOf cb ≤ 2 ^ m := by
    have h3 := orderOf_dihedral_le (n := 2 ^ m)
      (by calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm1)
      (d ⟨cb, hmem⟩)
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk] at h3
    exact h3
  rw [hfac, hv]
  have hk : k ≤ m + 1 := by
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · omega
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have h4 : 2 ^ k' ∣ orderOf cb := by
        have : 2 * 2 ^ k' ∣ 2 * orderOf cb := by
          rw [← pow_succ']
          exact h2
        exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
      have h5 : 2 ^ k' ≤ orderOf cb := Nat.le_of_dvd (orderOf_pos cb) h4
      have h6 : 2 ^ k' ≤ 2 ^ m := h5.trans hord
      have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h6
      omega
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

end CFSG.GH74.GLS.IVK.Lifted
