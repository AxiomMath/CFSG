module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5KeySpanDefs

public section

namespace CFSG.ComponentClassification.GMS78.VLike

variable {K : Type*} [Field K] [Fintype K] [CharP K 2]

omit [CharP K 2] in
theorem pow_theta_add_one_pow_theta_sub_one {a : ℕ} (hK : Fintype.card K = 2 ^ (2 * a + 1))
    (u : K) : (u ^ (2 ^ (a + 1) + 1)) ^ (2 ^ (a + 1) - 1) = u := by
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ (a + 1) = m + 1 := ⟨2 ^ (a + 1) - 1, by
    have := Nat.one_le_two_pow (n := a + 1); omega⟩
  by_cases hu : u = 0
  · subst hu
    rw [zero_pow (by omega), zero_pow (by omega)]
  have hq : u ^ 2 ^ (2 * a + 1) = u := by rw [← hK]; exact FiniteField.pow_card u
  have he : (2 ^ (a + 1) + 1) * (2 ^ (a + 1) - 1) + 1 = 2 ^ (2 * a + 1) * 2 := by
    have h2 : (2 : ℕ) ^ (2 * a + 1) * 2 = (2 ^ (a + 1)) ^ 2 := by ring
    rw [h2, hm, Nat.add_sub_cancel]
    ring
  have h1 : (u ^ (2 ^ (a + 1) + 1)) ^ (2 ^ (a + 1) - 1) * u = u * u := by
    rw [← pow_mul, ← pow_succ, he, pow_mul, hq, sq]
  exact mul_right_cancel₀ hu h1

omit [CharP K 2] in
theorem pow_theta_add_one_surjective {a : ℕ} (hK : Fintype.card K = 2 ^ (2 * a + 1)) :
    Function.Surjective fun u : K => u ^ (2 ^ (a + 1) + 1) := by
  refine Finite.injective_iff_surjective.mp fun u v huv => ?_
  have h := congrArg (fun w : K => w ^ (2 ^ (a + 1) - 1)) huv
  simpa only [pow_theta_add_one_pow_theta_sub_one hK] using h

omit [CharP K 2] in
theorem exists_ne_zero_ne_one {a : ℕ} (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1)) :
    ∃ t : K, t ≠ 0 ∧ t ≠ 1 := by
  classical
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset K) ⊆ {0, 1} := fun t _ => by
    by_cases ht : t = 0
    · simp [ht]
    · simp [h t ht]
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ, hK] at h1
  have h2 := Finset.card_le_two (a := (0 : K)) (b := 1)
  have h3 : 2 ^ 3 ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

variable {a : ℕ} {e : K}

omit [CharP K 2] in
theorem closure_eq_top_c_eq_zero_u_eq_zero (hK : Fintype.card K = 2 ^ (2 * a + 1))
    {Λ : AddSubgroup K} {x : K × K × K} (hu : x.1 = 0) :
    AddSubgroup.closure (sqMap a 0 e '' perp a 0 Λ x) = ⊤ := by
  refine eq_top_iff.mpr fun w _ => ?_
  obtain ⟨v, hv⟩ := pow_theta_add_one_surjective hK w
  have hmem : ((v, 0, 0) : K × K × K) ∈ perp a 0 Λ x :=
    ⟨Λ.zero_mem, by simp [commMap, hu]⟩
  have h := sqMap_mem_closure (e := e) hmem
  simpa [sqMap, hv] using h

omit [Fintype K] [CharP K 2] in
theorem closure_eq_top_c_eq_zero_s_eq_zero {Λ : AddSubgroup K} {x : K × K × K} (hu : x.1 ≠ 0)
    (hs : x.2.2 = 0) (hQ : sqMap a 0 e x = 0) :
    AddSubgroup.closure (sqMap a 0 e '' perp a 0 Λ x) = ⊤ := by
  have he : e ≠ 0 := by
    rintro rfl
    simp only [sqMap, zero_mul, hs, add_zero] at hQ
    exact hu (pow_eq_zero_iff (by positivity) |>.mp hQ)
  refine eq_top_iff.mpr fun w _ => ?_
  have hmem : ((0, w / e, 0) : K × K × K) ∈ perp a 0 Λ x :=
    ⟨Λ.zero_mem, by simp [commMap, hs]⟩
  have h := sqMap_mem_closure (e := e) hmem
  simpa [sqMap, mul_div_cancel₀ w he] using h

theorem closure_eq_top_c_eq_zero_s_ne_zero (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1))
    {Λ : AddSubgroup K} {x : K × K × K} (hs : x.2.2 ≠ 0) :
    AddSubgroup.closure (sqMap a 0 e '' perp a 0 Λ x) = ⊤ := by
  set z : K → K × K × K := fun v =>
    (v, (x.1 * v ^ 2 ^ (a + 1) + x.1 ^ 2 ^ (a + 1) * v) / x.2.2, 0) with hz
  have hzmem : ∀ v, z v ∈ perp a 0 Λ x := fun v => by
    refine ⟨Λ.zero_mem, ?_⟩
    simp only [hz, commMap, zero_mul, add_zero, mul_div_cancel₀ _ hs]
    exact CharTwo.add_self_eq_zero _
  obtain ⟨t, ht0, ht1⟩ := exists_ne_zero_ne_one ha hK
  have hd : t ^ 2 ^ (a + 1) + t ≠ 0 := by
    intro h
    have hfix : t ^ 2 ^ (a + 1) = t := by
      rw [← sub_eq_zero, CharTwo.sub_eq_add]; exact h
    rcases eq_zero_or_one_of_pow_two_pow_eq hK (by omega) (coprime_a_succ a) hfix with h0 | h1
    · exact ht0 h0
    · exact ht1 h1
  refine eq_top_iff.mpr fun w _ => ?_
  obtain ⟨l, hl⟩ := pow_theta_add_one_surjective hK (w / (t ^ 2 ^ (a + 1) + t))
  have h := commMap_mem_closure (e := e) (hzmem l) (hzmem (l * t))
  have hval : commMap a 0 (z l) (z (l * t)) = w := by
    simp only [hz, commMap, zero_mul, add_zero]
    simp only at hl
    rw [mul_pow, ← div_mul_cancel₀ w hd, ← hl]
    ring
  rwa [hval] at h

end CFSG.ComponentClassification.GMS78.VLike
