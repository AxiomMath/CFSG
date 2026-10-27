module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5KeySpanDefs
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5KeySpanTrace
public import Mathlib.Algebra.Algebra.ZMod

public section

namespace CFSG.ComponentClassification.GMS78.VLike

variable {K : Type*} [Field K] [Fintype K] [CharP K 2]

section Frob

variable {a : ℕ}

omit [CharP K 2] in
theorem pow_sigma_pow_theta (hK : Fintype.card K = 2 ^ (2 * a + 1)) (y : K) :
    (y ^ 2 ^ a) ^ 2 ^ (a + 1) = y := by
  rw [← pow_mul, ← pow_add, show a + (a + 1) = 2 * a + 1 by ring, ← hK]
  exact FiniteField.pow_card y

omit [CharP K 2] in
theorem pow_theta_pow_sigma (hK : Fintype.card K = 2 ^ (2 * a + 1)) (y : K) :
    (y ^ 2 ^ (a + 1)) ^ 2 ^ a = y := by
  rw [← pow_mul, mul_comm, pow_mul, pow_sigma_pow_theta hK]

omit [CharP K 2] in
theorem pow_theta_pow_theta (hK : Fintype.card K = 2 ^ (2 * a + 1)) (y : K) :
    (y ^ 2 ^ (a + 1)) ^ 2 ^ (a + 1) = y ^ 2 := by
  rw [← pow_mul, ← pow_add, show a + 1 + (a + 1) = (2 * a + 1) + 1 by ring, pow_succ, pow_mul,
    ← hK, FiniteField.pow_card]

theorem trace_mul_pow_sigma [Algebra (ZMod 2) K] (hK : Fintype.card K = 2 ^ (2 * a + 1))
    (γ t : K) : Algebra.trace (ZMod 2) K (γ * t ^ 2 ^ a) =
      Algebra.trace (ZMod 2) K (γ ^ 2 ^ (a + 1) * t) := by
  rw [← trace_pow_two_pow (γ * t ^ 2 ^ a) (a + 1), mul_pow, pow_sigma_pow_theta hK]

theorem trace_mul_pow_theta [Algebra (ZMod 2) K] (hK : Fintype.card K = 2 ^ (2 * a + 1))
    (γ t : K) : Algebra.trace (ZMod 2) K (γ * t ^ 2 ^ (a + 1)) =
      Algebra.trace (ZMod 2) K (γ ^ 2 ^ a * t) := by
  rw [← trace_pow_two_pow (γ * t ^ 2 ^ (a + 1)) a, mul_pow, pow_theta_pow_sigma hK]

end Frob

omit [Fintype K] [CharP K 2] in
theorem exists_mem_ne_ne {Λ : AddSubgroup K} (hΛ : 3 ≤ Nat.card Λ) (s s' : K) :
    ∃ t ∈ Λ, t ≠ s ∧ t ≠ s' := by
  classical
  by_contra h
  push Not at h
  let f : Λ → ({s, s'} : Finset K) := fun t => ⟨t, by
    by_cases ht : (t : K) = s
    · simp [ht]
    · simp [h t t.2 ht]⟩
  have hf : Function.Injective f := fun t t' htt => by
    have := congrArg (fun y : ({s, s'} : Finset K) => (y : K)) htt
    exact Subtype.ext this
  have h1 := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_fintype_card (α := ({s, s'} : Finset K)), Fintype.card_coe] at h1
  have h2 := Finset.card_le_two (a := s) (b := s')
  omega

variable {a : ℕ} {c e : K}

omit [Fintype K] [CharP K 2] in
theorem commMap_of_fst_eq_zero {x : K × K × K} (hu : x.1 = 0) (z : K × K × K) :
    commMap a c x z = c * (z.1 * x.2.1) ^ 2 ^ a + x.2.2 * z.2.1 + z.2.2 * x.2.1 := by
  have h0 : (0 : K) ^ 2 ^ (a + 1) = 0 := zero_pow (by positivity)
  have h0' : (0 : K) ^ 2 ^ a = 0 := zero_pow (by positivity)
  simp only [commMap, hu, zero_mul, h0, h0', zero_add]

omit [Fintype K] [CharP K 2] in
theorem commMap_of_fst_eq_zero_right (x : K × K × K) {z : K × K × K} (hz : z.1 = 0) :
    commMap a c x z = c * (x.1 * z.2.1) ^ 2 ^ a + x.2.2 * z.2.1 + z.2.2 * x.2.1 := by
  have h0 : (0 : K) ^ 2 ^ (a + 1) = 0 := zero_pow (by positivity)
  have h0' : (0 : K) ^ 2 ^ a = 0 := zero_pow (by positivity)
  simp only [commMap, hz, zero_mul, mul_zero, h0, h0', add_zero, zero_add]

theorem closure_eq_top_c_ne_zero_u_eq_zero_s_eq_zero (ha : 1 ≤ a)
    (hK : Fintype.card K = 2 ^ (2 * a + 1)) {Λ : AddSubgroup K} (hΛ : 3 ≤ Nat.card Λ)
    (hc : c ≠ 0) {x : K × K × K} (hu : x.1 = 0) (hs : x.2.2 = 0) (hr : x.2.1 ≠ 0) :
    AddSubgroup.closure (sqMap a c e '' perp a c Λ x) = ⊤ := by
  let _ : Algebra (ZMod 2) K := ZMod.algebra K 2
  by_contra hne
  obtain ⟨β, hβ, hβH⟩ := exists_ne_zero_trace_mul_eq_zero_of_ne_top hne
  have hrσ : x.2.1 ^ 2 ^ a ≠ 0 := pow_ne_zero _ hr
  have key : ∀ s₁ ∈ Λ, s₁ ≠ 0 → β * s₁ * x.2.1 = 1 := by
    intro s₁ hs₁ hs₁0
    obtain ⟨v, hv⟩ : ∃ v : K, v ^ 2 ^ a = s₁ * x.2.1 / (c * x.2.1 ^ 2 ^ a) :=
      ⟨_, pow_theta_pow_sigma hK _⟩
    have hz₁ : ((v, 0, s₁) : K × K × K) ∈ perp a c Λ x := by
      refine ⟨hs₁, ?_⟩
      rw [commMap_of_fst_eq_zero hu]
      dsimp only
      rw [hs, mul_pow, hv, show c * (s₁ * x.2.1 / (c * x.2.1 ^ 2 ^ a) * x.2.1 ^ 2 ^ a) =
        s₁ * x.2.1 by field_simp]
      simpa using CharTwo.add_self_eq_zero (s₁ * x.2.1)
    have hval : ∀ t : K, commMap a c (v, 0, s₁) (0, x.2.1 * t, 0) =
        s₁ * x.2.1 * (t ^ 2 ^ a + t) := by
      intro t
      rw [commMap_of_fst_eq_zero_right _ rfl]
      dsimp only
      rw [mul_pow, mul_pow, hv]
      field_simp
      ring
    have hfix : (β * s₁ * x.2.1) ^ 2 ^ (a + 1) = β * s₁ * x.2.1 := by
      have h0 : ∀ t : K, Algebra.trace (ZMod 2) K
          (((β * s₁ * x.2.1) ^ 2 ^ (a + 1) - β * s₁ * x.2.1) * t) = 0 := by
        intro t
        have hw : ((0, x.2.1 * t, 0) : K × K × K) ∈ perp a c Λ x := by
          refine ⟨Λ.zero_mem, ?_⟩
          rw [commMap_of_fst_eq_zero hu]
          simp [hs]
        have h1 := hβH _ (commMap_mem_closure (e := e) hz₁ hw)
        rw [hval, show β * (s₁ * x.2.1 * (t ^ 2 ^ a + t)) =
          β * s₁ * x.2.1 * t ^ 2 ^ a + β * s₁ * x.2.1 * t by ring, map_add,
          trace_mul_pow_sigma hK] at h1
        rw [sub_mul, map_sub, CharTwo.sub_eq_add]
        exact h1
      exact sub_eq_zero.mp (eq_zero_of_forall_trace_mul_eq_zero h0)
    rcases eq_zero_or_one_of_pow_two_pow_eq hK (by omega) (coprime_a_succ a) hfix with h0 | h1
    · exact absurd h0 (mul_ne_zero (mul_ne_zero hβ hs₁0) hr)
    · exact h1
  obtain ⟨s₁, hs₁, hs₁0, -⟩ := exists_mem_ne_ne hΛ 0 0
  obtain ⟨s₂, hs₂, hs₂0, hs₂₁⟩ := exists_mem_ne_ne hΛ 0 s₁
  have h12 : β * s₁ * x.2.1 = β * s₂ * x.2.1 := by rw [key s₁ hs₁ hs₁0, key s₂ hs₂ hs₂0]
  exact hs₂₁ (mul_left_cancel₀ hβ (mul_right_cancel₀ hr h12)).symm

theorem closure_eq_top_c_ne_zero_u_eq_zero_s_ne_zero (ha : 1 ≤ a)
    (hK : Fintype.card K = 2 ^ (2 * a + 1)) {Λ : AddSubgroup K} (hΛ : 3 ≤ Nat.card Λ)
    (hc : c ≠ 0) {x : K × K × K} (hu : x.1 = 0) (hs : x.2.2 ≠ 0) (hr : x.2.1 ≠ 0) :
    AddSubgroup.closure (sqMap a c e '' perp a c Λ x) = ⊤ := by
  obtain ⟨s₂, hs₂, hs₂0, hs₂s⟩ := exists_mem_ne_ne hΛ 0 x.2.2
  obtain ⟨t, ht⟩ : ∃ t, t = s₂ / x.2.2 := ⟨_, rfl⟩
  have hs₂t : s₂ = t * x.2.2 := by rw [ht]; field_simp
  have hd : t ^ 2 ^ a + t ≠ 0 := by
    intro h
    have hfix : t ^ 2 ^ a = t := by rw [← sub_eq_zero, CharTwo.sub_eq_add]; exact h
    rcases eq_zero_or_one_of_pow_two_pow_eq hK (by omega) (coprime_a a) hfix with h0 | h1
    · exact hs₂0 (by rw [hs₂t, h0, zero_mul])
    · exact hs₂s (by rw [hs₂t, h1, one_mul])
  have hz₂ : ((0, s₂ * x.2.1 / x.2.2, s₂) : K × K × K) ∈ perp a c Λ x := by
    refine ⟨hs₂, ?_⟩
    rw [commMap_of_fst_eq_zero hu]
    dsimp only
    rw [zero_mul, zero_pow (by positivity), mul_zero, zero_add, mul_div_cancel₀ _ hs]
    exact CharTwo.add_self_eq_zero (s₂ * x.2.1)
  have hcr : c * x.2.1 ^ 2 ^ a * (t ^ 2 ^ a + t) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hc (pow_ne_zero _ hr)) hd
  refine eq_top_iff.mpr fun w _ => ?_
  obtain ⟨u₁, hu₁⟩ := pow_two_pow_surjective (K := K) a (w / (c * x.2.1 ^ 2 ^ a * (t ^ 2 ^ a + t)))
  simp only at hu₁
  have hz₁ : ((u₁, c * x.2.1 ^ 2 ^ a * u₁ ^ 2 ^ a / x.2.2, 0) : K × K × K) ∈ perp a c Λ x := by
    refine ⟨Λ.zero_mem, ?_⟩
    rw [commMap_of_fst_eq_zero hu]
    dsimp only
    rw [zero_mul, add_zero, mul_div_cancel₀ _ hs, mul_pow,
      show c * (u₁ ^ 2 ^ a * x.2.1 ^ 2 ^ a) = c * x.2.1 ^ 2 ^ a * u₁ ^ 2 ^ a by ring]
    exact CharTwo.add_self_eq_zero (c * x.2.1 ^ 2 ^ a * u₁ ^ 2 ^ a)
  have h := commMap_mem_closure (e := e) hz₁ hz₂
  have hval : commMap a c (u₁, c * x.2.1 ^ 2 ^ a * u₁ ^ 2 ^ a / x.2.2, 0)
      (0, s₂ * x.2.1 / x.2.2, s₂) = w := by
    rw [commMap_of_fst_eq_zero_right _ rfl]
    dsimp only
    rw [show u₁ * (s₂ * x.2.1 / x.2.2) = u₁ * x.2.1 * t by rw [hs₂t]; field_simp,
      mul_pow, mul_pow, hs₂t, ← div_mul_cancel₀ w hcr, ← hu₁]
    field_simp
    ring
  rwa [hval] at h

end CFSG.ComponentClassification.GMS78.VLike
