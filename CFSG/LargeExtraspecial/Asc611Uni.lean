module

public import CFSG.LargeExtraspecial.AS35NFlagD

public section

namespace CFSG.LargeExtraspecial.Asc611

open Subgroup Matrix CFSG.Fischer.Classification.Unitary CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Unitary
open CFSG.Blueprint.Fischer (K)

variable {m : ℕ}

theorem orderOf_tq_mul_tq (hm : 3 ≤ m) {a b : Fin m → K} (ha0 : a ≠ 0)
    (ha : herm frob a a = 0) (hb0 : b ≠ 0) (hb : herm frob b b = 0) (hab : herm frob a b ≠ 0) :
    orderOf (tq a * tq b) = 3 := by
  have h3 : (tq a * tq b) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow, tvU_mul_tvU_pow_three ha hb hab,
      QuotientGroup.mk_one]
  have h1 : tq a * tq b ≠ 1 := by
    intro h
    have hab' : tq a = tq b := by
      calc tq a = tq a * (tq b * tq b) := by rw [tq_mul_self hb, mul_one]
        _ = tq b := by rw [← mul_assoc, h, one_mul]
    obtain ⟨c, hc⟩ := (tq_eq_tq_iff hm ha0 ha hb0 hb).mp hab'
    apply hab
    rw [hc, herm_smul_right, ha, mul_zero]
  have hdvd := orderOf_dvd_of_pow_eq_one h3
  have hpos : orderOf (tq a * tq b) ≠ 1 := fun h => h1 (orderOf_eq_one_iff.mp h)
  have : orderOf (tq a * tq b) ∣ 3 := hdvd
  rcases (Nat.dvd_prime Nat.prime_three).mp this with h | h
  · exact absurd h hpos
  · exact h

theorem not_mem_of_orderOf_three {G : Type*} [Group G] {U : Subgroup G} (hU : IsPGroup 2 U)
    {g : G} (hg : g ∈ U) (h3 : orderOf g = 3) : False := by
  obtain ⟨k, hk⟩ := hU ⟨g, hg⟩
  have h1 : g ^ (2 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have h2 := orderOf_dvd_of_pow_eq_one h1
  rw [h3] at h2
  have h4 := (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2)).eq_one_of_dvd h2
  omega

theorem herm_eq_zero_of_mem (hm : 3 ≤ m) {U : Subgroup (PG m)} (hU : IsPGroup 2 U)
    {a b : Fin m → K} (ha0 : a ≠ 0) (ha : herm frob a a = 0) (hb0 : b ≠ 0)
    (hb : herm frob b b = 0) (hmem : tq a * tq b ∈ U) : herm frob a b = 0 := by
  by_contra hab
  exact not_mem_of_orderOf_three hU hmem (orderOf_tq_mul_tq hm ha0 ha hb0 hb hab)

theorem commutator_mem {G : Type*} [Group G] {U : Subgroup G} {c u : G}
    (hc : ∀ x ∈ U, c * x * c⁻¹ ∈ U) (hu : u ∈ U) : u * c * u⁻¹ * c⁻¹ ∈ U := by
  have h1 := hc u⁻¹ (U.inv_mem hu)
  have h2 := U.mul_mem hu h1
  rwa [show u * (c * u⁻¹ * c⁻¹) = u * c * u⁻¹ * c⁻¹ by group] at h2

theorem mulVec_single_add_single (M : Matrix (Fin m) (Fin m) K) (i j : Fin m) (t : K)
    (k : Fin m) : (M *ᵥ (Pi.single i 1 + Pi.single j t)) k = M k i + M k j * t := by
  simp [mulVec_add, mul_comm]

theorem exists_scalar_of_forall_eigen (M : Matrix (Fin m) (Fin m) K)
    (h : ∀ v : Fin m → K, v ≠ 0 → herm frob v v = 0 → ∃ c : K, M *ᵥ v = c • v) :
    ∃ μ : K, ∀ x : Fin m → K, M *ᵥ x = μ • x := by
  have key : ∀ i j : Fin m, i ≠ j → M j i = 0 ∧ M i i = M j j := by
    intro i j hij
    have hval : ∀ t : K, t ≠ 0 → M j i + M j j * t = t * (M i i + M i j * t) := by
      intro t ht
      have hv0 : (Pi.single i 1 + Pi.single j t : Fin m → K) ≠ 0 := by
        intro h0
        have := congrFun h0 i
        simp [Pi.single_eq_of_ne hij] at this
      have hiso : herm frob (Pi.single i 1 + Pi.single j t : Fin m → K)
          (Pi.single i 1 + Pi.single j t) = 0 := by
        rw [herm_single_add_single hij, frob_mul_self ht, add_self_K]
      obtain ⟨c, hc⟩ := h _ hv0 hiso
      have hi := congrFun hc i
      have hj := congrFun hc j
      rw [mulVec_single_add_single] at hi hj
      simp [Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hij.symm] at hi hj
      linear_combination hj - t * hi
    have h1 := hval 1 one_ne_zero
    have h2 := hval ω omega_ne_zero
    have h3 := hval (ω + 1) (by
      intro h0
      apply omega_ne_one
      calc ω = ω + 1 + 1 := by rw [add_assoc, add_self_K, add_zero]
        _ = 1 := by rw [h0, zero_add])
    have hw := AS35N.omega_sq_add
    have h2' : (2 : K) = 0 := two_eq_zero
    have hA : M j i = 0 := by
      linear_combination h1 + h2 + h3 + (-M j i - (ω + 1) * (M j j - M i i) +
        M i j * (1 + ω + ω * ω)) * h2'
    have hC : M i j = 0 := by
      linear_combination (-ω) * h1 + h2 + (ω - 1) * hA + M i j * hw - M i j * ω * h2'
    exact ⟨hA, by linear_combination -h1 + hA - hC⟩
  rcases Nat.eq_zero_or_pos m with hm0 | hm0
  · subst hm0
    exact ⟨0, fun x => funext fun k => k.elim0⟩
  · set i₀ : Fin m := ⟨0, hm0⟩
    refine ⟨M i₀ i₀, fun x => funext fun k => ?_⟩
    rw [mulVec, dotProduct, Finset.sum_eq_single k (fun l _ hl => by
      rw [(key l k hl).1, zero_mul]) (by simp), Pi.smul_apply, smul_eq_mul]
    by_cases hk : k = i₀
    · rw [hk]
    · rw [(key i₀ k (Ne.symm hk)).2]

end CFSG.LargeExtraspecial.Asc611
