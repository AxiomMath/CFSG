module

public import CFSG.ClassicalInvolution.Phan.PhanS4Std

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.D

open CFSG.ClassicalInvolution.PhanB3.S.Std Polynomial

variable {K : Type} [Field K] (M : Model K)

structure Sesq (G : Vec K → Vec K → K) : Prop where
  add_left : ∀ x x' y, G (x + x') y = G x y + G x' y
  add_right : ∀ x y y', G x (y + y') = G x y + G x y'
  smul_left : ∀ (c : K) x y, G (c • x) y = c * G x y
  smul_right : ∀ (c : K) x y, G x (c • y) = M.τ c * G x y

theorem sesq_her : Sesq M (her M) :=
  ⟨her_add_left M, her_add_right M, her_smul_left M, her_smul_right M⟩

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

@[expose] noncomputable def conicPoly (G : Vec K → Vec K → K) (c₀ c₁ c₂ : Vec K) : K[X] :=
  ∑ i : Fin 3, ∑ j : Fin 3, C (G (cs c₀ c₁ c₂ i) (cs c₀ c₁ c₂ j)) * X ^ ((i : ℕ) + M.q * j)

theorem eval_conicPoly (G : Vec K → Vec K → K) (c₀ c₁ c₂ : Vec K) (μ : K) :
    (conicPoly (M := M) G c₀ c₁ c₂).eval μ =
      ∑ i : Fin 3, ∑ j : Fin 3, G (cs c₀ c₁ c₂ i) (cs c₀ c₁ c₂ j) * (μ ^ (i : ℕ) *
        (μ ^ M.q) ^ (j : ℕ)) := by
  simp only [conicPoly, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [pow_add, pow_mul]

theorem natDegree_conicPoly_le (G : Vec K → Vec K → K) (c₀ c₁ c₂ : Vec K) :
    (conicPoly (M := M) G c₀ c₁ c₂).natDegree ≤ 2 * M.q + 2 := by
  refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
  refine natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
  refine (natDegree_C_mul_X_pow_le _ _).trans ?_
  have hi := i.2
  have hj : (j : ℕ) ≤ 2 := by omega
  have : M.q * (j : ℕ) ≤ M.q * 2 := Nat.mul_le_mul_left _ hj
  omega

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
    (conicPoly (M := M) G c₀ c₁ c₂).coeff ((i : ℕ) + M.q * j) =
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
    conicPoly (M := M) G c₀ c₁ c₂ ≠ 0 := by
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
  refine (Polynomial.card_le_degree_of_subset_roots (p := conicPoly (M := M) G c₀ c₁ c₂) ?_).trans
    (natDegree_conicPoly_le G c₀ c₁ c₂)
  intro μ hμ
  rw [Finset.mem_val, Finset.mem_filter] at hμ
  rw [mem_roots hP, IsRoot.def, eval_conicPoly, ← hG.conic_eval]
  exact hμ.2

theorem exists_mu_ne_zero (hq : 3 ≤ M.q) (hcard : 4 * M.q + 4 < Nat.card K)
    {G₁ G₂ : Vec K → Vec K → K} (h₁ : Sesq M G₁) (h₂ : Sesq M G₂) {c₀ c₁ c₂ : Vec K}
    (w₁ : ∃ i j : Fin 3, G₁ (cs c₀ c₁ c₂ i) (cs c₀ c₁ c₂ j) ≠ 0)
    (w₂ : ∃ i j : Fin 3, G₂ (cs c₀ c₁ c₂ i) (cs c₀ c₁ c₂ j) ≠ 0) :
    ∃ μ : K, G₁ (conicPt c₀ c₁ c₂ μ) (conicPt c₀ c₁ c₂ μ) ≠ 0 ∧
      G₂ (conicPt c₀ c₁ c₂ μ) (conicPt c₀ c₁ c₂ μ) ≠ 0 := by
  classical
  have := Fintype.ofFinite K
  by_contra hcon
  have hcon' : ∀ μ : K, G₁ (conicPt c₀ c₁ c₂ μ) (conicPt c₀ c₁ c₂ μ) ≠ 0 →
      G₂ (conicPt c₀ c₁ c₂ μ) (conicPt c₀ c₁ c₂ μ) = 0 := fun μ h1 => by
    by_contra h2
    exact hcon ⟨μ, h1, h2⟩
  have a1 := card_zeros_le hq h₁ w₁
  have a2 := card_zeros_le hq h₂ w₂
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at a1 a2
  have hsub : (Finset.univ : Finset K) ⊆
      (Finset.univ.filter fun μ => G₁ (conicPt c₀ c₁ c₂ μ) (conicPt c₀ c₁ c₂ μ) = 0) ∪
      (Finset.univ.filter fun μ => G₂ (conicPt c₀ c₁ c₂ μ) (conicPt c₀ c₁ c₂ μ) = 0) := by
    intro μ _
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    by_cases h : G₁ (conicPt c₀ c₁ c₂ μ) (conicPt c₀ c₁ c₂ μ) = 0
    · exact Or.inl ⟨Finset.mem_univ _, h⟩
    · exact Or.inr ⟨Finset.mem_univ _, hcon' μ h⟩
  have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at this
  omega

end CFSG.ClassicalInvolution.PhanB3.S.Std.D
