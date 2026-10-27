module

public import CFSG.ClassicalInvolution.Phan.PhanS8Q2Basic

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.Q

open CFSG.ClassicalInvolution.PhanB3.S.Std Polynomial

variable {K : Type} [Field K] (M : Model K)

@[expose] def conicPt (c₀ c₁ c₂ : Vec K) (μ : K) : Vec K := c₀ + μ • c₁ + (μ ^ 2) • c₂

@[expose] def cs (c₀ c₁ c₂ : Vec K) : Fin 3 → Vec K := ![c₀, c₁, c₂]

omit [Field K] in
theorem cs_zero (c₀ c₁ c₂ : Vec K) : cs c₀ c₁ c₂ 0 = c₀ := rfl

omit [Field K] in
theorem cs_one (c₀ c₁ c₂ : Vec K) : cs c₀ c₁ c₂ 1 = c₁ := rfl

omit [Field K] in
theorem cs_two (c₀ c₁ c₂ : Vec K) : cs c₀ c₁ c₂ 2 = c₂ := rfl

variable {M}

theorem Sesq.conic_eval {G : Vec K → Vec K → K} (hG : Sesq M G) (c₀ c₁ c₂ : Vec K) (μ : K) :
    G (conicPt c₀ c₁ c₂ μ) (conicPt c₀ c₁ c₂ μ) =
      ∑ i : Fin 3, ∑ j : Fin 3, G (cs c₀ c₁ c₂ i) (cs c₀ c₁ c₂ j) * (μ ^ (i : ℕ) *
        (μ ^ M.q) ^ (j : ℕ)) := by
  have hτ : M.τ μ = μ ^ M.q := M.tau_pow μ
  simp only [conicPt, hG.add_left, hG.add_right, hG.smul_left, hG.smul_right, map_pow, hτ,
    Fin.sum_univ_three, cs_zero, cs_one, cs_two, Fin.val_zero, Fin.val_one, Fin.val_two]
  ring

theorem Sesq.expand_three {G : Vec K → Vec K → K} (hG : Sesq M G) (e : Fin 3 → Vec K)
    (d d' : Fin 3 → K) :
    G (∑ i, d i • e i) (∑ i, d' i • e i) =
      ∑ i : Fin 3, ∑ j : Fin 3, d i * M.τ (d' j) * G (e i) (e j) := by
  simp only [Fin.sum_univ_three, hG.add_left, hG.add_right, hG.smul_left, hG.smul_right]
  ring

variable (M)

@[expose] noncomputable def conicPoly (G : Vec K → Vec K → K) (c₀ c₁ c₂ : Vec K) : K[X] :=
  ∑ i : Fin 3, ∑ j : Fin 3, C (G (cs c₀ c₁ c₂ i) (cs c₀ c₁ c₂ j)) * X ^ ((i : ℕ) + M.q * j)

theorem eval_conicPoly (G : Vec K → Vec K → K) (c₀ c₁ c₂ : Vec K) (μ : K) :
    (conicPoly M G c₀ c₁ c₂).eval μ =
      ∑ i : Fin 3, ∑ j : Fin 3, G (cs c₀ c₁ c₂ i) (cs c₀ c₁ c₂ j) * (μ ^ (i : ℕ) *
        (μ ^ M.q) ^ (j : ℕ)) := by
  simp only [conicPoly, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [pow_add, pow_mul]

theorem natDegree_conicPoly_le (G : Vec K → Vec K → K) (c₀ c₁ c₂ : Vec K) :
    (conicPoly M G c₀ c₁ c₂).natDegree ≤ 2 * M.q + 2 := by
  refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
  refine natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
  refine (natDegree_C_mul_X_pow_le _ _).trans ?_
  have hi := i.2
  have hj : (j : ℕ) ≤ 2 := by omega
  have : M.q * (j : ℕ) ≤ M.q * 2 := Nat.mul_le_mul_left _ hj
  omega

variable {M}

theorem exp_inj (hq : 3 ≤ M.q) {i j i' j' : Fin 3}
    (h : (i : ℕ) + M.q * j = (i' : ℕ) + M.q * j') : i = i' ∧ j = j' := by
  have hi := i.2
  have hi' := i'.2
  have h1 : (i : ℕ) = i' := by
    have := congrArg (· % M.q) h
    simp only [Nat.add_mul_mod_self_left] at this
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  have h2 : (j : ℕ) = j' := by
    rw [h1] at h
    exact Nat.eq_of_mul_eq_mul_left (by omega) (Nat.add_left_cancel h)
  exact ⟨Fin.ext h1, Fin.ext h2⟩

theorem coeff_conicPoly (hq : 3 ≤ M.q) (G : Vec K → Vec K → K) (c₀ c₁ c₂ : Vec K) (i j : Fin 3) :
    (conicPoly M G c₀ c₁ c₂).coeff ((i : ℕ) + M.q * j) =
      G (cs c₀ c₁ c₂ i) (cs c₀ c₁ c₂ j) := by
  simp only [conicPoly, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
  · simp
  · intro j' _ hj'
    refine ite_eq_right_iff.mpr fun h => absurd ?_ hj'
    exact (exp_inj hq h).2.symm
  · simp
  · intro i' _ hi'
    refine Finset.sum_eq_zero fun j' _ => ite_eq_right_iff.mpr fun h => absurd ?_ hi'
    exact (exp_inj hq h).1.symm
  · simp

theorem conicPoly_ne_zero (hq : 3 ≤ M.q) {G : Vec K → Vec K → K} {c₀ c₁ c₂ : Vec K}
    (h : ∃ i j : Fin 3, G (cs c₀ c₁ c₂ i) (cs c₀ c₁ c₂ j) ≠ 0) :
    conicPoly M G c₀ c₁ c₂ ≠ 0 := by
  obtain ⟨i, j, hij⟩ := h
  intro h0
  have := coeff_conicPoly (M := M) hq G c₀ c₁ c₂ i j
  rw [h0, coeff_zero] at this
  exact hij this.symm

variable [Finite K]

theorem card_zeros_le (hq : 3 ≤ M.q) {G : Vec K → Vec K → K} (hG : Sesq M G) {c₀ c₁ c₂ : Vec K}
    (h : ∃ i j : Fin 3, G (cs c₀ c₁ c₂ i) (cs c₀ c₁ c₂ j) ≠ 0) :
    Nat.card {μ : K // G (conicPt c₀ c₁ c₂ μ) (conicPt c₀ c₁ c₂ μ) = 0} ≤ 2 * M.q + 2 := by
  classical
  have := Fintype.ofFinite K
  have hP := conicPoly_ne_zero (M := M) hq h
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  refine (Polynomial.card_le_degree_of_subset_roots (p := conicPoly M G c₀ c₁ c₂) ?_).trans
    (natDegree_conicPoly_le M G c₀ c₁ c₂)
  intro μ hμ
  rw [Finset.mem_val, Finset.mem_filter] at hμ
  rw [mem_roots hP, IsRoot.def, eval_conicPoly, ← hG.conic_eval]
  exact hμ.2

omit [Finite K] in
theorem natDegree_conicPoly_le_pencil {G : Vec K → Vec K → K} (hG : Sesq M G) (c₀ c₁ : Vec K) :
    (conicPoly M G c₀ c₁ 0).natDegree ≤ M.q + 1 := by
  have hG0 : ∀ y, G 0 y = 0 := fun y => by
    have := hG.smul_left 0 0 y
    simpa using this
  have hG0' : ∀ y, G y 0 = 0 := fun y => by
    have := hG.smul_right 0 y 0
    simpa using this
  refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
  refine natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
  by_cases hi : (i : ℕ) = 2
  · have : cs c₀ c₁ 0 i = 0 := by
      have : i = 2 := Fin.ext hi
      subst this; rfl
    rw [this, hG0]
    simp
  by_cases hj : (j : ℕ) = 2
  · have : cs c₀ c₁ 0 j = 0 := by
      have : j = 2 := Fin.ext hj
      subst this; rfl
    rw [this, hG0']
    simp
  refine (natDegree_C_mul_X_pow_le _ _).trans ?_
  have hi' : (i : ℕ) ≤ 1 := by have := i.2; omega
  have hj' : (j : ℕ) ≤ 1 := by have := j.2; omega
  have : M.q * (j : ℕ) ≤ M.q * 1 := Nat.mul_le_mul_left _ hj'
  omega

theorem card_zeros_le_pencil (hq : 3 ≤ M.q) {G : Vec K → Vec K → K} (hG : Sesq M G)
    {c₀ c₁ : Vec K} (h : ∃ i j : Fin 3, G (cs c₀ c₁ 0 i) (cs c₀ c₁ 0 j) ≠ 0) :
    Nat.card {μ : K // G (conicPt c₀ c₁ 0 μ) (conicPt c₀ c₁ 0 μ) = 0} ≤ M.q + 1 := by
  classical
  have := Fintype.ofFinite K
  have hP := conicPoly_ne_zero (M := M) hq h
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  refine (Polynomial.card_le_degree_of_subset_roots (p := conicPoly M G c₀ c₁ 0) ?_).trans
    (natDegree_conicPoly_le_pencil hG c₀ c₁)
  intro μ hμ
  rw [Finset.mem_val, Finset.mem_filter] at hμ
  rw [mem_roots hP, IsRoot.def, eval_conicPoly, ← hG.conic_eval]
  exact hμ.2

theorem exists_nonzero_all {m B : ℕ} (f : Fin m → K → K)
    (hB : ∀ k, Nat.card {μ : K // f k μ = 0} ≤ B) (hcard : m * B < Nat.card K) :
    ∃ μ : K, ∀ k, f k μ ≠ 0 := by
  classical
  have := Fintype.ofFinite K
  by_contra hcon
  push Not at hcon
  have hsub : (Finset.univ : Finset K) ⊆
      Finset.univ.biUnion fun k : Fin m => Finset.univ.filter fun μ => f k μ = 0 := by
    intro μ _
    obtain ⟨k, hk⟩ := hcon μ
    exact Finset.mem_biUnion.2 ⟨k, Finset.mem_univ _, Finset.mem_filter.2 ⟨Finset.mem_univ _, hk⟩⟩
  have h1 := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have h2 : ∑ k : Fin m, (Finset.univ.filter fun μ => f k μ = 0).card ≤ ∑ _k : Fin m, B :=
    Finset.sum_le_sum fun k _ => by
      have := hB k
      rwa [Nat.card_eq_fintype_card, Fintype.card_subtype] at this
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h2
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at h1
  omega

theorem exists_good_param (hq : 3 ≤ M.q) {m : ℕ} {Φ : Fin m → Vec K → Vec K → K}
    (hΦ : ∀ k, Sesq M (Φ k)) {c₀ c₁ c₂ : Vec K}
    (hw : ∀ k, ∃ i j : Fin 3, Φ k (cs c₀ c₁ c₂ i) (cs c₀ c₁ c₂ j) ≠ 0)
    (hcard : m * (2 * M.q + 2) < Nat.card K) :
    ∃ μ : K, ∀ k, Φ k (conicPt c₀ c₁ c₂ μ) (conicPt c₀ c₁ c₂ μ) ≠ 0 :=
  exists_nonzero_all (fun k μ => Φ k (conicPt c₀ c₁ c₂ μ) (conicPt c₀ c₁ c₂ μ))
    (fun k => card_zeros_le hq (hΦ k) (hw k)) hcard

theorem exists_good_pencil (hq : 3 ≤ M.q) {m : ℕ} {Φ : Fin m → Vec K → Vec K → K}
    (hΦ : ∀ k, Sesq M (Φ k)) {c₀ c₁ : Vec K}
    (hw : ∀ k, ∃ i j : Fin 3, Φ k (cs c₀ c₁ 0 i) (cs c₀ c₁ 0 j) ≠ 0)
    (hcard : m * (M.q + 1) < Nat.card K) :
    ∃ μ : K, ∀ k, Φ k (conicPt c₀ c₁ 0 μ) (conicPt c₀ c₁ 0 μ) ≠ 0 :=
  exists_nonzero_all (fun k μ => Φ k (conicPt c₀ c₁ 0 μ) (conicPt c₀ c₁ 0 μ))
    (fun k => card_zeros_le_pencil hq (hΦ k) (hw k)) hcard

end CFSG.ClassicalInvolution.PhanB3.S.Std.Q
