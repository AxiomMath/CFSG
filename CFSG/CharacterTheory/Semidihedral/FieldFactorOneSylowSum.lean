module

public import CFSG.CharacterTheory.Semidihedral.Principal.CyclicMultiplicity
public import CFSG.CharacterTheory.Semidihedral.Principal.PerfectSemidihedralRotationCongruences

public section

open scoped BigOperators

namespace CFSG.Semidihedral.FieldFactorOne

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.Principal
open CFSG.TwoRankLowerBound.Helpers

theorem pow_add_cube_pow_of_sq_eq_neg_one {ω : ℂ} (hω : ω ^ 2 = -1) (j : ℕ) :
    ω ^ j + (ω ^ 3) ^ j = 2 * (if j % 4 = 0 then 1 else if j % 4 = 2 then -1 else 0) := by
  have h4 : ω ^ 4 = 1 := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, hω]
    norm_num
  have h12 : (ω ^ 3) ^ 4 = 1 := by
    rw [← pow_mul, show 3 * 4 = 4 * 3 from rfl, pow_mul, h4, one_pow]
  obtain ⟨q, k, hk, rfl⟩ : ∃ q k, k < 4 ∧ j = 4 * q + k :=
    ⟨j / 4, j % 4, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod j 4).symm⟩
  rw [pow_add, pow_mul, h4, one_pow, one_mul, pow_add, pow_mul, h12, one_pow, one_mul,
    show (4 * q + k) % 4 = k by omega]
  interval_cases k
  · norm_num
  · simp only [pow_one, one_ne_zero, ite_false, OfNat.one_ne_ofNat]
    linear_combination ω * hω
  · simp only [OfNat.ofNat_ne_zero, ite_false, ite_true]
    linear_combination (2 + ω ^ 4 - ω ^ 2) * hω
  · simp only [OfNat.ofNat_ne_zero, ite_false, show (3 : ℕ) ≠ 2 by decide]
    linear_combination ω ^ 3 * (ω ^ 4 - ω ^ 2 + 1) * hω

section Columns

variable {G : Type*} [Group G] [Fintype G]

theorem character_quarter_pow_eq_real_sum (basis : FiniteIrreducibleCharacterBasis G) {g : G}
    {M K : ℕ} (hMK : M = 4 * K) (hK : 0 < K) (hg : g ^ M = 1) (χ : basis.index)
    (hreal : (basis.representation χ).character (g ^ K) =
      (basis.representation χ).character (g ^ (3 * K))) :
    (basis.representation χ).character (g ^ K) =
      ((∑ j ∈ Finset.range M,
        (if j % 4 = 0 then multiplicityColumn basis g M j χ
          else if j % 4 = 2 then -multiplicityColumn basis g M j χ else 0) : ℤ) : ℂ) := by
  have hM : 0 < M := by omega
  set ψ := (basis.representation χ).character with hψ
  set ω := cyclicRoot M ^ K with hωdef
  have hω : ω ^ 2 = -1 := by
    rw [hωdef, ← pow_mul, show K * 2 = M / 2 by omega]
    exact cyclicRoot_pow_half hM ⟨2 * K, by omega⟩
  have hinv1 := cyclicMultiplicity_inversion ψ g hM (show K < M by omega)
  have hinv3 := cyclicMultiplicity_inversion ψ g hM (show 3 * K < M by omega)
  have hterm : ∀ j : ℕ,
      cyclicMultiplicity ψ g M j * cyclicRoot M ^ ((j : ℤ) * (K : ℕ)) +
        cyclicMultiplicity ψ g M j * cyclicRoot M ^ ((j : ℤ) * ((3 * K : ℕ) : ℤ)) =
      2 * (((if j % 4 = 0 then multiplicityColumn basis g M j χ
          else if j % 4 = 2 then -multiplicityColumn basis g M j χ else 0) : ℤ) : ℂ) := by
    intro j
    rw [← multiplicityColumn_cast basis hM hg j χ, mul_comm (j : ℤ), zpow_mul, zpow_natCast,
      zpow_natCast, mul_comm (j : ℤ), zpow_mul, zpow_natCast, zpow_natCast,
      show cyclicRoot M ^ (3 * K) = ω ^ 3 by rw [hωdef, ← pow_mul, mul_comm], ← mul_add,
      pow_add_cube_pow_of_sq_eq_neg_one hω j]
    split_ifs <;> push_cast <;> ring
  have h2 : 2 * ψ (g ^ K) = 2 * ((∑ j ∈ Finset.range M,
        (if j % 4 = 0 then multiplicityColumn basis g M j χ
          else if j % 4 = 2 then -multiplicityColumn basis g M j χ else 0) : ℤ) : ℂ) := by
    calc 2 * ψ (g ^ K) = ψ (g ^ K) + ψ (g ^ (3 * K)) := by rw [← hreal]; ring
      _ = _ := by rw [hinv1, hinv3, ← Finset.sum_add_distrib]
      _ = ∑ j ∈ Finset.range M, 2 * (((if j % 4 = 0 then multiplicityColumn basis g M j χ
          else if j % 4 = 2 then -multiplicityColumn basis g M j χ else 0) : ℤ) : ℂ) :=
        Finset.sum_congr rfl fun j _ => hterm j
      _ = _ := by rw [← Finset.mul_sum, Int.cast_sum]
  exact mul_left_cancel₀ two_ne_zero h2

end Columns

theorem sylow_character_sum_congruence {G : Type} [Group G] [Fintype G]
    (hindex : ∀ V : Subgroup G, V.index ≠ 2) (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (basis : FiniteIrreducibleCharacterBasis G)
    (χ : basis.index) :
    (8 * 2 ^ (n - 3) : ℤ) ∣
      4 * 2 ^ (n - 3) * multiplicityColumn basis (fS (r n) : G) (modulus n) 0 χ +
        2 * 2 ^ (n - 3) *
          (∑ j ∈ Finset.range (4 * 2 ^ (n - 3)),
              (-1) ^ j * multiplicityColumn basis (fS (r n) : G) (modulus n) j χ +
            ∑ j ∈ Finset.range (4 * 2 ^ (n - 3)),
              (if j % 4 = 0 then multiplicityColumn basis (fS (r n) : G) (modulus n) j χ
                else if j % 4 = 2 then -multiplicityColumn basis (fS (r n) : G) (modulus n) j χ
                else 0)) := by
  obtain ⟨hM, -, hK2, -⟩ := modulus_eq_four_mul hn
  have hn3 : 3 ≤ n := by omega
  rw [← hM]
  set K := 2 ^ (n - 3) with hKdef
  set g : G := (fS (r n) : G) with hgdef
  set θ := basis.representation χ with hθ
  have hMpos : 0 < modulus n := by omega
  have hg : g ^ modulus n = 1 := supplied_r_pow_modulus fS
  obtain ⟨m, hm⟩ := RotationCongruence.sum_character_subgroup_eq (S : Subgroup G) θ
  have hcard : Nat.card (S : Subgroup G) = 8 * K := by
    rw [← Nat.card_congr fS.toEquiv, CFSG.Semidihedral.card n hn3, hKdef,
      show 8 * 2 ^ (n - 3) = 2 ^ (n - 3 + 3) by rw [pow_add]; ring, Nat.sub_add_cancel hn3]
  have hdec := RotationCongruence.sylow_character_sum_eq hn S fS hindex θ
  have hrot : ∑ i ∈ Finset.range (modulus n), θ.character (g ^ i) =
      (modulus n : ℂ) * (multiplicityColumn basis g (modulus n) 0 χ : ℂ) := by
    rw [multiplicityColumn_cast basis hMpos hg 0 χ, cyclicMultiplicity, ← mul_assoc,
      mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hMpos.ne'), one_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [zero_mul, neg_zero, zpow_zero, mul_one]
  have ht := character_half_pow_eq_signed_sum basis hMpos ⟨2 * K, by omega⟩ hg χ
  have hreal : θ.character (g ^ K) = θ.character (g ^ (3 * K)) := by
    have hc := (FocalFusion.ambientHom n (S : Subgroup G) fS).map_isConj
      (quarter_inverse_conjugate n hn)
    rw [map_pow, map_zpow] at hc
    change IsConj (g ^ K) (g ^ (-(K : ℤ))) at hc
    have hinv : g ^ (-(K : ℤ)) = g ^ (3 * K) := by
      rw [zpow_neg, zpow_natCast]
      refine (eq_inv_of_mul_eq_one_left ?_).symm
      rw [← pow_add, show 3 * K + K = modulus n by omega, hg]
    rw [← hinv]
    exact RotationCongruence.character_eq_of_isConj θ hc
  have hq := character_quarter_pow_eq_real_sum basis (M := modulus n) hM
    (by omega) hg χ hreal
  have hMc : ((modulus n : ℕ) : ℂ) = ((4 * K : ℕ) : ℂ) := by rw [hM]
  rw [hm, hcard, hrot, ht, show modulus n / 4 = K by omega, hq,
    show modulus n / 2 = 2 * K by omega, hMc, hKdef] at hdec
  refine ⟨m, ?_⟩
  apply Int.cast_injective (α := ℂ)
  push_cast at hdec ⊢
  linear_combination -hdec

end CFSG.Semidihedral.FieldFactorOne
