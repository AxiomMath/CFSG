module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3

theorem fact_A_perm6 : ∀ τ : Equiv.Perm (Fin 6), τ ^ 5 = 1 → τ ≠ 1 →
    ∃ a : Fin 6, τ a = a ∧ ∀ b c : Fin 6, b ≠ a → c ≠ a → ∃ n < 5, (τ ^ n) b = c := by
  decide +kernel

theorem perm6_two_group_trivial (K : Subgroup (Equiv.Perm (Fin 6))) (hK : IsPGroup 2 K)
    (τ : Equiv.Perm (Fin 6)) (hτ5 : τ ^ 5 = 1) (hτ1 : τ ≠ 1)
    (hnorm : ∀ k ∈ K, τ * k * τ⁻¹ ∈ K) : K = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, hτa, hA1⟩ := fact_A_perm6 τ hτ5 hτ1
  have hτa_pow : ∀ n : ℕ, (τ ^ n) a = a := fun n =>
    Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hτa n
  have hB : ∀ x : Fin 6, ∃ n : ℕ, Nat.card (MulAction.orbit K x) = 2 ^ n :=
    fun x => hK.card_orbit x
  have hpow : ∀ n : ℕ, 2 ^ n ≠ 5 ∧ 2 ^ n ≠ 6 := by
    intro n
    rcases Nat.lt_or_ge n 3 with h | h
    · interval_cases n <;> norm_num
    · have h8 : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h
      norm_num at h8
      constructor <;> intro h' <;> omega
  have hC : ∀ x y : Fin 6, y ∈ MulAction.orbit K x → τ y ∈ MulAction.orbit K (τ x) := by
    intro x y hy
    obtain ⟨k, rfl⟩ := MulAction.mem_orbit_iff.1 hy
    refine MulAction.mem_orbit_iff.2 ⟨⟨τ * (k : Equiv.Perm (Fin 6)) * τ⁻¹, hnorm _ k.2⟩, ?_⟩
    simp [Subgroup.smul_def, Equiv.Perm.smul_def, Equiv.Perm.mul_apply]
  have hCpow : ∀ m : ℕ, ∀ x y : Fin 6, y ∈ MulAction.orbit K x →
      (τ ^ m) y ∈ MulAction.orbit K ((τ ^ m) x) := by
    intro m
    induction m with
    | zero => intro x y hy; simpa using hy
    | succ m ih =>
      intro x y hy
      have h1 := hC _ _ (ih x y hy)
      simp only [pow_succ', Equiv.Perm.mul_apply]
      exact h1
  have hstep1 : ∀ k : Equiv.Perm (Fin 6), k ∈ K → k a = a := by
    intro k hk
    by_contra hne
    have hyO : k a ∈ MulAction.orbit K a :=
      MulAction.mem_orbit_iff.2 ⟨⟨k, hk⟩, rfl⟩
    have hall : ∀ c : Fin 6, c ∈ MulAction.orbit K a := by
      intro c
      by_cases hca : c = a
      · rw [hca]; exact MulAction.mem_orbit_self a
      · obtain ⟨n, -, hnc⟩ := hA1 (k a) c hne hca
        have h1 := hCpow n a (k a) hyO
        rw [hτa_pow n, hnc] at h1
        exact h1
    have h6 : Nat.card (MulAction.orbit K a) = 6 := by
      rw [Set.eq_univ_of_forall hall]
      simp
    obtain ⟨m, hm⟩ := hB a
    rw [h6] at hm
    exact (hpow m).2 hm.symm
  have hstep2 : ∀ k : Equiv.Perm (Fin 6), k ∈ K → ∀ x : Fin 6, k x = x := by
    intro k hk x
    by_cases hxa : x = a
    · rw [hxa]; exact hstep1 k hk
    by_contra hne
    have hya : k x ≠ a := by
      intro h
      apply hxa
      apply k.injective
      rw [h, hstep1 k hk]
    have hO : k x ∈ MulAction.orbit K x :=
      MulAction.mem_orbit_iff.2 ⟨⟨k, hk⟩, rfl⟩
    obtain ⟨j, hj5, hjx⟩ := hA1 x (k x) hxa hya
    have hj0 : j ≠ 0 := by
      rintro rfl
      apply hne
      rw [pow_zero, Equiv.Perm.one_apply] at hjx
      exact hjx.symm
    have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
    have hkO : MulAction.orbit K (k x) = MulAction.orbit K x :=
      MulAction.orbit_eq_iff.2 hO
    have hclosed : ∀ i : ℕ, (τ ^ (i * j)) x ∈ MulAction.orbit K x := by
      intro i
      induction i with
      | zero => simpa using MulAction.mem_orbit_self x
      | succ i ih =>
        have h1 := hCpow j x _ ih
        rw [hjx, hkO] at h1
        have e : (τ ^ ((i + 1) * j)) x = (τ ^ j) ((τ ^ (i * j)) x) := by
          rw [show (i + 1) * j = j + i * j by ring, pow_add, Equiv.Perm.mul_apply]
        rw [e]
        exact h1
    have hall_pow : ∀ m : ℕ, (τ ^ m) x ∈ MulAction.orbit K x := by
      intro m
      have hmod : ∀ p : ℕ, τ ^ p = τ ^ (p % 5) := by
        intro p
        conv_lhs => rw [← Nat.div_add_mod p 5]
        rw [pow_add, pow_mul, hτ5, one_pow, one_mul]
      have key : ∃ i : ℕ, (τ ^ (i * j)) x = (τ ^ m) x := by
        interval_cases j
        · exact ⟨m, by simp⟩
        · refine ⟨3 * m, ?_⟩
          rw [hmod (3 * m * 2), hmod m, show 3 * m * 2 % 5 = m % 5 by omega]
        · refine ⟨2 * m, ?_⟩
          rw [hmod (2 * m * 3), hmod m, show 2 * m * 3 % 5 = m % 5 by omega]
        · refine ⟨4 * m, ?_⟩
          rw [hmod (4 * m * 4), hmod m, show 4 * m * 4 % 5 = m % 5 by omega]
      obtain ⟨i, hi⟩ := key
      rw [← hi]
      exact hclosed i
    have hcompl : ({a}ᶜ : Set (Fin 6)) ⊆ MulAction.orbit K x := by
      intro c hc
      have hca : c ≠ a := hc
      obtain ⟨n, -, hnc⟩ := hA1 x c hxa hca
      rw [← hnc]
      exact hall_pow n
    have hna : a ∉ MulAction.orbit K x := by
      intro ha
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1 ha
      have hgx : (g : Equiv.Perm (Fin 6)) x = a := hg
      have hinv : ((g : Equiv.Perm (Fin 6))⁻¹) a = x := by
        rw [← hgx, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
      exact hxa (hinv.symm.trans (hstep1 _ (K.inv_mem g.2)))
    have hsub : MulAction.orbit K x ⊆ ({a}ᶜ : Set (Fin 6)) := by
      intro c hc hca
      rw [Set.mem_singleton_iff] at hca
      rw [hca] at hc
      exact hna hc
    have heq : MulAction.orbit K x = ({a}ᶜ : Set (Fin 6)) :=
      Set.Subset.antisymm hsub hcompl
    have h5 : Nat.card (MulAction.orbit K x) = 5 := by
      rw [heq, Nat.card_coe_set_eq, Set.ncard_compl, Set.ncard_singleton]
      simp
    obtain ⟨m, hm⟩ := hB x
    rw [h5] at hm
    exact (hpow m).1 hm.symm
  rw [Subgroup.eq_bot_iff_forall]
  intro k hk
  refine Equiv.ext fun x => ?_
  rw [Equiv.Perm.one_apply]
  exact hstep2 k hk x

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3
