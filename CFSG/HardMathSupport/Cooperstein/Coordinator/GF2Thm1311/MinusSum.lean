module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311.FrobSum

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311

section
variable {K : Type*} [Field K] [CharP K 2] [Fintype K]

theorem chi_zero : chi (0 : K) = 1 := by simp [chi]

theorem chi_sum (h : Nat.card K = 4) {ι : Type*} (s : Finset ι) (a : ι → K) :
    chi (∑ i ∈ s, a i) = ∏ i ∈ s, chi (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [chi_zero]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, chi_add h _ _, ih]

theorem sum_chi_eq_zero (h : Nat.card K = 4) : ∑ s : K, chi s = 0 := by
  obtain ⟨ω, hω⟩ := F4_exists_omega h
  have hchω : chi ω = -1 := by simp [chi, hω]
  have hsum := Fintype.sum_bijective (fun s : K => s + ω) (add_left_injective ω |>.bijective_of_finite)
    (fun s => chi (s + ω)) (fun s => chi s) (fun _ => rfl)
  have : ∑ s : K, chi (s + ω) = -∑ s : K, chi s := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [chi_add h, hchω]; ring
  linarith

open scoped Classical in
theorem sum_chi_mul (h : Nat.card K = 4) (a : K) :
    ∑ t : K, chi (a * t) = if a = 0 then 4 else 0 := by
  by_cases ha : a = 0
  · subst ha
    have h' : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card]; exact h
    simp [chi_zero, h']
  · rw [if_neg ha]
    have hb : Function.Bijective (fun t : K => a * t) :=
      (mul_right_injective₀ ha).bijective_of_finite
    rw [Fintype.sum_bijective _ hb (fun t => chi (a * t)) (fun s => chi s) (fun _ => rfl)]
    exact sum_chi_eq_zero h

theorem chi_sq (h : Nat.card K = 4) (x : K) : chi (x ^ 2) = chi x := by
  have h4 : (x ^ 2) ^ 2 = x := by rw [← pow_mul]; exact F4_pow_four h x
  unfold chi
  rw [h4, add_comm]

open scoped Classical in
theorem sum_chi_dot (h : Nat.card K = 4) (m : ℕ) :
    ∑ xy : (Fin m → K) × (Fin m → K), chi (∑ i, xy.1 i * xy.2 i) = 4 ^ m := by
  rw [Fintype.sum_prod_type]
  have h1 : ∀ x : Fin m → K, ∑ y : Fin m → K, chi (∑ i, x i * y i) =
      ∏ i, (if x i = 0 then (4 : ℤ) else 0) := by
    intro x
    simp_rw [chi_sum h]
    have := Finset.prod_univ_sum (fun _ : Fin m => (Finset.univ : Finset K))
      (fun i t => chi (x i * t))
    simp only [Fintype.piFinset_univ] at this
    rw [← this]
    simp [sum_chi_mul h]
  simp_rw [h1]
  have := Finset.prod_univ_sum (fun _ : Fin m => (Finset.univ : Finset K))
    (fun _ (a : K) => if a = 0 then (4 : ℤ) else 0)
  simp only [Fintype.piFinset_univ] at this
  rw [← this]
  simp

theorem chi_norm_pt (h : Nat.card K = 4) (b c u v : K) :
    chi (u ^ 2 + b * u * v + c * v ^ 2) = chi (u * (1 + b * v)) * chi (c * v ^ 2) := by
  rw [chi_add h, chi_add h, chi_sq h]
  congr 1
  rw [← chi_add h]
  congr 1
  ring

open scoped Classical in
theorem sum_chi_norm (h : Nat.card K = 4) (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∑ uv : K × K, chi (uv.1 ^ 2 + b * uv.1 * uv.2 + c * uv.2 ^ 2) = -4 := by
  have h11 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  obtain ⟨ω, hω⟩ := F4_exists_omega h
  have hb : b ≠ 0 := by
    rintro rfl
    apply hirr (c ^ 2)
    have h4 : (c ^ 2) ^ 2 = c := by rw [← pow_mul]; exact F4_pow_four h c
    rw [h4]
    simp [CharTwo.add_self_eq_zero]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  have h1 : ∀ v : K, ∑ u : K, chi (u ^ 2 + b * u * v + c * v ^ 2) =
      chi (c * v ^ 2) * (if 1 + b * v = 0 then 4 else 0) := by
    intro v
    simp_rw [chi_norm_pt h]
    rw [← Finset.sum_mul]
    simp_rw [mul_comm _ (1 + b * v)]
    rw [sum_chi_mul h, mul_comm]
  simp_rw [h1]
  rw [Finset.sum_eq_single b⁻¹]
  · have e : 1 + b * b⁻¹ = 0 := by rw [mul_inv_cancel₀ hb, h11]
    rw [if_pos e]
    set z := c * b⁻¹ ^ 2 with hz
    have hzw : ∀ w : K, w ^ 2 + w ≠ z := by
      intro w hw
      apply hirr (b * w)
      have e1 : (b * w) ^ 2 + b * (b * w) + c = b ^ 2 * (w ^ 2 + w) + c := by ring
      have e2 : b ^ 2 * z = c := by rw [hz]; field_simp
      rw [e1, hw, e2]
      exact CharTwo.add_self_eq_zero c
    have hchi : chi z = -1 := by
      unfold chi
      rw [if_neg]
      intro hz0
      have : z * (z + 1) = 0 := by rw [mul_add, mul_one, ← _root_.sq, hz0]
      rcases mul_eq_zero.mp this with h0 | h0
      · exact hzw 0 (by rw [h0]; simp)
      · have : z = 1 := by
          have := eq_neg_of_add_eq_zero_left h0
          rw [this, CharTwo.neg_eq]
        exact hzw ω (by rw [this]; exact hω)
    rw [hchi]
    ring
  · intro v _ hv
    have : 1 + b * v ≠ 0 := by
      intro h0
      apply hv
      have h1 : b * v = 1 := by
        have := eq_neg_of_add_eq_zero_right h0
        rw [this, CharTwo.neg_eq]
      exact eq_inv_of_mul_eq_one_right h1
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

def minusCoord (m : ℕ) : ((Fin m → K) × (Fin m → K)) × (K × K) → (Fin m ⊕ Fin m ⊕ Fin 2 → K) :=
  fun p => Sum.elim p.1.1 (Sum.elim p.1.2 ![p.2.1, p.2.2])

theorem minusCoord_bijective (m : ℕ) : Function.Bijective (minusCoord (K := K) m) := by
  constructor
  · rintro ⟨⟨x, y⟩, ⟨u, v⟩⟩ ⟨⟨x', y'⟩, ⟨u', v'⟩⟩ h
    simp only [minusCoord] at h
    have hx : x = x' := funext fun i => by simpa using congrFun h (Sum.inl i)
    have hy : y = y' := funext fun i => by simpa using congrFun h (Sum.inr (Sum.inl i))
    have hu : u = u' := by simpa using congrFun h (Sum.inr (Sum.inr 0))
    have hv : v = v' := by simpa using congrFun h (Sum.inr (Sum.inr 1))
    subst hx hy hu hv
    rfl
  · intro w
    refine ⟨⟨⟨fun i => w (Sum.inl i), fun i => w (Sum.inr (Sum.inl i))⟩,
      ⟨w (Sum.inr (Sum.inr 0)), w (Sum.inr (Sum.inr 1))⟩⟩, ?_⟩
    funext i
    rcases i with i | i | i
    · rfl
    · rfl
    · fin_cases i <;> rfl

open scoped Classical in
theorem sum_chi_minus_neg (h : Nat.card K = 4) (m : ℕ) (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∑ v : Fin m ⊕ Fin m ⊕ Fin 2 → K, chi (∑ i, v (Sum.inl i) * v (Sum.inr (Sum.inl i)) +
      v (Sum.inr (Sum.inr 0)) ^ 2 + b * v (Sum.inr (Sum.inr 0)) * v (Sum.inr (Sum.inr 1)) +
      c * v (Sum.inr (Sum.inr 1)) ^ 2) < 0 := by
  rw [← Fintype.sum_bijective (minusCoord (K := K) m) (minusCoord_bijective m)
    (fun p => chi (∑ i, (minusCoord m p) (Sum.inl i) * (minusCoord m p) (Sum.inr (Sum.inl i)) +
      (minusCoord m p) (Sum.inr (Sum.inr 0)) ^ 2 +
      b * (minusCoord m p) (Sum.inr (Sum.inr 0)) * (minusCoord m p) (Sum.inr (Sum.inr 1)) +
      c * (minusCoord m p) (Sum.inr (Sum.inr 1)) ^ 2)) _ (fun _ => rfl)]
  have hpt : ∀ p : ((Fin m → K) × (Fin m → K)) × (K × K),
      chi (∑ i, (minusCoord m p) (Sum.inl i) * (minusCoord m p) (Sum.inr (Sum.inl i)) +
      (minusCoord m p) (Sum.inr (Sum.inr 0)) ^ 2 +
      b * (minusCoord m p) (Sum.inr (Sum.inr 0)) * (minusCoord m p) (Sum.inr (Sum.inr 1)) +
      c * (minusCoord m p) (Sum.inr (Sum.inr 1)) ^ 2) =
      chi (∑ i, p.1.1 i * p.1.2 i) * chi (p.2.1 ^ 2 + b * p.2.1 * p.2.2 + c * p.2.2 ^ 2) := by
    rintro ⟨⟨x, y⟩, ⟨u, v⟩⟩
    simp only [minusCoord, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    rw [← chi_add h, add_assoc, add_assoc, add_assoc]
  simp_rw [hpt]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul, sum_chi_dot h, sum_chi_norm h b c hirr]
  have : (0 : ℤ) < 4 ^ m := by positivity
  linarith

end

end CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311
