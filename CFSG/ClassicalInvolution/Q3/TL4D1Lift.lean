module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

variable {A B : Type} [Group A] [Group B] [Finite A] (φ : A →* B)

theorem exists_lift_odd {b : B} (hb : b ∈ φ.range) (hodd : Odd (orderOf b)) :
    ∃ a : A, φ a = b ∧ Odd (orderOf a) := by
  obtain ⟨a₀, rfl⟩ := hb
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos a₀).ne'
  rcases Nat.lt_or_ge 1 (orderOf (φ a₀)) with h1 | h1
  · have hcop : Nat.Coprime (2 ^ k) (orderOf (φ a₀)) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
    obtain ⟨t, -, ht⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop h1
    refine ⟨(a₀ ^ 2 ^ k) ^ t, ?_, ?_⟩
    · rw [map_pow, map_pow, ← pow_mul, ← pow_mod_orderOf, ht, pow_one]
    · have h1 : orderOf (a₀ ^ 2 ^ k) ∣ m := by
        apply orderOf_dvd_of_pow_eq_one
        rw [← pow_mul, ← hkm, pow_orderOf_eq_one]
      exact hm.of_dvd_nat ((orderOf_pow_dvd t).trans h1)
  · have hb1 : φ a₀ = 1 := by
      obtain ⟨t, ht⟩ := hodd
      exact orderOf_eq_one_iff.mp (by omega)
    exact ⟨1, by rw [map_one, hb1], by rw [orderOf_one]; exact odd_one⟩

omit [Finite A] in
theorem conj_eq_mul_of_map_comm {x w : A} (h : φ x * φ w = φ w * φ x) :
    ∃ c ∈ φ.ker, x * w * x⁻¹ = w * c :=
  ⟨w⁻¹ * (x * w * x⁻¹), by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_inv, h]
    group, by group⟩

omit [Finite A] in
theorem comm_of_odd_of_map_comm (hk : φ.ker ≤ Subgroup.center A) (hk2 : IsPGroup 2 φ.ker)
    {y w : A} (hy : Odd (orderOf y)) (h : φ y * φ w = φ w * φ y) : y * w = w * y := by
  obtain ⟨c, hcker, hyw⟩ := conj_eq_mul_of_map_comm φ h
  have hpow : ∀ k : ℕ, y ^ k * w * (y ^ k)⁻¹ = w * c ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hck : y * c ^ k * y⁻¹ = c ^ k := by
        have := Subgroup.mem_center_iff.mp (hk (Subgroup.pow_mem _ hcker k)) y
        rw [this]
        group
      calc y ^ (k + 1) * w * (y ^ (k + 1))⁻¹ = y * (y ^ k * w * (y ^ k)⁻¹) * y⁻¹ := by
            rw [pow_succ']
            group
        _ = (y * w * y⁻¹) * (y * c ^ k * y⁻¹) := by rw [ih]; group
        _ = w * c ^ (k + 1) := by rw [hyw, hck, pow_succ', mul_assoc]
  have hco : c ^ orderOf y = 1 := by
    have := hpow (orderOf y)
    rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at this
    exact mul_left_cancel (this.symm.trans (mul_one w).symm)
  obtain ⟨j, hj⟩ := hk2 ⟨c, hcker⟩
  have hj' : c ^ 2 ^ j = 1 := by
    have := congrArg Subtype.val hj
    rwa [Subgroup.coe_pow] at this
  have h1 : orderOf c = 1 := Nat.eq_one_of_dvd_coprimes
    (Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hy))
    (orderOf_dvd_of_pow_eq_one hco) (orderOf_dvd_of_pow_eq_one hj')
  have hc1 : c = 1 := orderOf_eq_one_iff.mp h1
  calc y * w = (y * w * y⁻¹) * y := by group
    _ = w * y := by rw [hyw, hc1, mul_one]

end CFSG.ClassicalInvolution.Q3.TL4
