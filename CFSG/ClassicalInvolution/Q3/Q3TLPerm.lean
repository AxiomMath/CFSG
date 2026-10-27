module

public import CFSG.ClassicalInvolution.Q3.Q3TKMem

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T

open CFSG CFSG.Open CFSG.ClassicalInvolution
open scoped MatrixGroups

theorem perm_pow_three_of_sign {β : Type*} [Fintype β] [DecidableEq β]
    (h3 : Fintype.card β ≤ 3) (σ : Equiv.Perm β) (hσ : Equiv.Perm.sign σ = 1) : σ ^ 3 = 1 := by
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card β = n := ⟨_, rfl⟩
  rw [hn] at h3
  let e := Fintype.equivFinOfCardEq hn
  have key : ∀ τ : Equiv.Perm (Fin n), Equiv.Perm.sign τ = 1 → τ ^ 3 = 1 := by
    interval_cases n <;> decide
  have h1 := key (e.permCongr σ) (by rw [Equiv.Perm.sign_permCongr]; exact hσ)
  apply (Equiv.permCongrHom e).injective
  rw [map_pow, map_one]
  exact h1

theorem perm_eq_one_of_sign_of_pow_four {β : Type*} [Fintype β] [DecidableEq β]
    (h3 : Fintype.card β ≤ 3) {σ : Equiv.Perm β} (hσ : Equiv.Perm.sign σ = 1)
    (h4 : σ ^ 4 = 1) : σ = 1 := by
  have h := perm_pow_three_of_sign h3 σ hσ
  calc σ = σ ^ 4 * (σ ^ 3)⁻¹ := by group
    _ = 1 := by rw [h4, h, inv_one, mul_one]

theorem mul_self_mod_four {m : ℕ} (hm : ¬ 2 ∣ m) : m * m % 4 = 1 := by
  have h : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rw [Nat.mul_mod]
  rcases h with h | h <;> rw [h]

theorem exists_two_pow_lift {G H : Type*} [Group G] [Finite G] [Group H] (ψ : G →* H)
    (hψ : Function.Surjective ψ) {s : H} (hs : s ^ 4 = 1) :
    ∃ x : G, (∃ k : ℕ, orderOf x = 2 ^ k) ∧ ψ x = s := by
  obtain ⟨y, rfl⟩ := hψ s
  have hn : orderOf y ≠ 0 := (orderOf_pos y).ne'
  obtain ⟨a, m, hm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn 2 (by norm_num)
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero 2)
  refine ⟨y ^ (m * m), ⟨a, ?_⟩, ?_⟩
  · have hcop : Nat.Coprime (2 ^ a) m :=
      Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hm)
    rw [orderOf_pow' y (mul_ne_zero hm0 hm0), hnm, Nat.gcd_mul_right, hcop.gcd_eq_one, one_mul,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
  · rw [map_pow, pow_eq_pow_mod (m * m) hs, mul_self_mod_four hm, pow_one]

theorem eq_one_of_sq_of_pow_odd {M : Type*} [Group M] {m : M} (h2 : m ^ 2 = 1) {n : ℕ}
    (hn : Odd n) (h : m ^ n = 1) : m = 1 := by
  obtain ⟨j, rfl⟩ := hn
  have h1 : m ^ (2 * j) = 1 := by rw [pow_mul, h2, one_pow]
  rw [pow_succ, h1, one_mul] at h
  exact h

variable {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} {z : Y}

theorem hom_eq_one_of_sq (hz : IsClassicalMember3 L z) {M : Type*} [Group M] (χ : L →* M)
    (hM : ∀ m : M, m ^ 2 = 1) (y : L) : χ y = 1 := by
  obtain ⟨ψ, hψs, hψk⟩ := hz.exists_hom
  have h3 : ∀ w : L, (∃ k : ℕ, orderOf w = 3 ^ k) → χ w = 1 := by
    rintro w ⟨k, hk⟩
    refine eq_one_of_sq_of_pow_odd (hM _) (n := 3 ^ k) (Odd.pow (by decide : Odd 3)) ?_
    rw [← map_pow, ← hk, pow_orderOf_eq_one, map_one]
  obtain ⟨a, b, ha, hb, hc⟩ := sl2Three_eq_mul_three (ψ y)
  obtain ⟨a', ha', hpa⟩ := exists_three_pow_lift ψ hψs ha
  obtain ⟨b', hb', hpb⟩ := exists_three_pow_lift ψ hψs hb
  obtain ⟨c', hc', hpc⟩ := exists_three_pow_lift ψ hψs hc
  have ho : ψ ((a' * c' * b')⁻¹ * y) = 1 := by
    rw [map_mul, map_inv, map_mul, map_mul, hpa, hpb, hpc]
    group
  have hodd := hz.odd_orderOf_of_mem_oddCore ((hψk _).mp ho)
  have hχo : χ ((a' * c' * b')⁻¹ * y) = 1 := by
    refine eq_one_of_sq_of_pow_odd (hM _) hodd ?_
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  have hy : y = a' * c' * b' * ((a' * c' * b')⁻¹ * y) := by group
  rw [hy, map_mul, map_mul, map_mul, h3 a' ha', h3 c' hc', h3 b' hb', hχo]
  group

end CFSG.ClassicalInvolution.Q3.Q3T
