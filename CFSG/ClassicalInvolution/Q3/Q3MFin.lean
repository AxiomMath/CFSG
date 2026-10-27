module

public import CFSG.ClassicalInvolution.SolvableCase.SL2Three

public section

namespace CFSG.ClassicalInvolution.Q3.M

open scoped MatrixGroups

theorem sl2_pow_24 : ∀ y : SL(2, ZMod 3), y ^ 24 = 1 := by decide +kernel

theorem sl2_inv_of_ne_one : ∀ y w : SL(2, ZMod 3), y ≠ 1 → w ^ 2 = 1 → w ≠ 1 →
    y = w ∨ y ^ 2 = w ∨ y ^ 3 = w ∨ ∃ a : SL(2, ZMod 3), (a * y * a⁻¹ * y⁻¹) ^ 2 = w := by
  decide +kernel

theorem sl2_order_cases : ∀ y : SL(2, ZMod 3), y ^ 2 ≠ 1 →
    y ^ 4 = 1 ∨ y ^ 3 = 1 ∨ ((y ^ 4) ^ 3 = 1 ∧ y ^ 4 ≠ 1) := by
  decide +kernel

theorem sl2_Q_of_three : ∀ g q : SL(2, ZMod 3), g ^ 3 = 1 → g ≠ 1 → q ^ 4 = 1 →
    ∃ a b : SL(2, ZMod 3), q = (a * g * a⁻¹ * g⁻¹) * (b * g * b⁻¹ * g⁻¹) := by
  decide +kernel

theorem sl2_Q_of_four : ∀ g x q : SL(2, ZMod 3), g ^ 3 = 1 → g ≠ 1 → x ^ 4 = 1 → x ^ 2 ≠ 1 →
    q ^ 4 = 1 → ∃ i j : Fin 4, q = x ^ (i : ℕ) * (g * x * g⁻¹) ^ (j : ℕ) := by
  decide +kernel

theorem sl2_exists_three : ∃ g : SL(2, ZMod 3), g ^ 3 = 1 ∧ g ≠ 1 := by decide +kernel

theorem sl2_three_distinct : ∀ s y : SL(2, ZMod 3), s ^ 3 = 1 → y ^ 3 = 1 → s ≠ 1 → y ≠ 1 →
    y ≠ s → y ≠ s⁻¹ → ¬ ((s * y) ^ 6 = 1 ∧ (s * y⁻¹) ^ 6 = 1) := by
  decide +kernel

theorem sl2_three_not_normal : ∀ s : SL(2, ZMod 3), s ^ 3 = 1 → s ≠ 1 →
    ∃ a : SL(2, ZMod 3), a * s * a⁻¹ ≠ s ∧ a * s * a⁻¹ ≠ s⁻¹ := by
  decide +kernel

theorem sl2_pow_six {y : SL(2, ZMod 3)} {k : ℕ} (h : y ^ (2 * 3 ^ k) = 1) : y ^ 6 = 1 := by
  have h1 := pow_gcd_eq_one.2 ⟨h, sl2_pow_24 y⟩
  have hdvd : Nat.gcd (2 * 3 ^ k) 24 ∣ 6 := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact (Nat.gcd_dvd_left _ _).trans (by norm_num)
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hcop : Nat.Coprime (3 ^ j) 8 := Nat.Coprime.pow_left _ (by norm_num)
      have : Nat.gcd (2 * 3 ^ (j + 1)) 24 = 6 * Nat.gcd (3 ^ j) 4 := by
        have e1 : 2 * 3 ^ (j + 1) = 6 * 3 ^ j := by ring
        rw [e1, show (24 : ℕ) = 6 * 4 by norm_num, Nat.gcd_mul_left]
      rw [this]
      have : Nat.gcd (3 ^ j) 4 = 1 :=
        (Nat.Coprime.pow_left j (by norm_num : Nat.Coprime 3 4))
      rw [this]
  obtain ⟨c, hc⟩ := hdvd
  rw [hc, pow_mul, h1, one_pow]


theorem sl2_normal_inv (K : Subgroup SL(2, ZMod 3)) [K.Normal] {y w : SL(2, ZMod 3)}
    (hy : y ∈ K) (hy1 : y ≠ 1) (hw : w ^ 2 = 1) (hw1 : w ≠ 1) : w ∈ K := by
  rcases sl2_inv_of_ne_one y w hy1 hw hw1 with h | h | h | ⟨a, ha⟩
  · exact h ▸ hy
  · exact h ▸ K.pow_mem hy 2
  · exact h ▸ K.pow_mem hy 3
  · rw [← ha]
    exact K.pow_mem (K.mul_mem (Subgroup.Normal.conj_mem inferInstance y hy a)
      (K.inv_mem hy)) 2

theorem sl2_normal_Q (K : Subgroup SL(2, ZMod 3)) [K.Normal] {y : SL(2, ZMod 3)}
    (hy : y ∈ K) (hy2 : y ^ 2 ≠ 1) : CFSG.ClassicalInvolution.sl2ThreeQ ≤ K := by
  intro q hq
  have hq4 : q ^ 4 = 1 := CFSG.ClassicalInvolution.mem_sl2ThreeQ_iff.mp hq
  obtain ⟨g₀, hg₀3, hg₀1⟩ := sl2_exists_three
  have key3 : ∀ g ∈ K, g ^ 3 = 1 → g ≠ 1 → q ∈ K := by
    intro g hg hg3 hg1
    obtain ⟨a, b, hab⟩ := sl2_Q_of_three g q hg3 hg1 hq4
    rw [hab]
    exact K.mul_mem (K.mul_mem (Subgroup.Normal.conj_mem inferInstance g hg a) (K.inv_mem hg))
      (K.mul_mem (Subgroup.Normal.conj_mem inferInstance g hg b) (K.inv_mem hg))
  rcases sl2_order_cases y hy2 with h4 | h3 | ⟨h43, h41⟩
  · obtain ⟨i, j, hij⟩ := sl2_Q_of_four g₀ y q hg₀3 hg₀1 h4 hy2 hq4
    rw [hij]
    exact K.mul_mem (K.pow_mem hy _)
      (K.pow_mem (Subgroup.Normal.conj_mem inferInstance y hy g₀) _)
  · exact key3 y hy h3 (fun h => hy2 (by simp [h]))
  · exact key3 (y ^ 4) (K.pow_mem hy 4) h43 h41

end CFSG.ClassicalInvolution.Q3.M
