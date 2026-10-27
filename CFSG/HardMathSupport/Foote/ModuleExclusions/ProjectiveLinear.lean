module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution
public import CFSG.HardMathSupport.Foote.ModuleExclusions.Hilbert90

public section

namespace CFSG.HardMathSupport.Foote.ModuleExclusions

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix
  CFSG.ComponentClassification

variable {n : ℕ} {K : Type} [Field K]

theorem commute_single_of_conjAut_eq_one {A : GL (Fin n) K} (h : conjAut n K A = 1)
    {i j : Fin n} (hij : i ≠ j) :
    Commute (Matrix.single i j (1 : K)) (A : Matrix (Fin n) (Fin n) K) := by
  set g : SpecialLinearGroup (Fin n) K :=
    ⟨Matrix.transvection i j (1 : K), Matrix.det_transvection_of_ne i j hij 1⟩ with hg
  set s := CatalogueBHigherLinearAction.slConjugation n K A g with hs
  have h1 : proj n K s = proj n K g := by rw [hs, ← conjAut_proj, h, MulAut.one_apply]
  obtain ⟨c, hcn, hc⟩ := proj_eq_proj_iff.1 h1.symm
  have hgs : (g : Matrix (Fin n) (Fin n) K) * scalar (Fin n) (c : K) = (s : Matrix (Fin n) (Fin n) K) := by
    calc (g : Matrix (Fin n) (Fin n) K) * scalar (Fin n) (c : K)
        = (g : Matrix (Fin n) (Fin n) K) * ((g⁻¹ * s : SpecialLinearGroup (Fin n) K) :
            Matrix (Fin n) (Fin n) K) := by rw [hc]
      _ = ((g * (g⁻¹ * s) : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
          rfl
      _ = (s : Matrix (Fin n) (Fin n) K) := by rw [mul_inv_cancel_left]
  have hAA : (A : Matrix (Fin n) (Fin n) K) * ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hAA' : ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  set e : Matrix (Fin n) (Fin n) K := Matrix.single i j (1 : K) with he
  set A' : Matrix (Fin n) (Fin n) K := ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hA'
  set M : Matrix (Fin n) (Fin n) K := (A : Matrix (Fin n) (Fin n) K) with hM
  have hgm : (g : Matrix (Fin n) (Fin n) K) = 1 + e := rfl
  have hee : e * e = 0 := by
    rw [he, Matrix.single_mul_single_of_ne _ _ _ _ hij.symm]
  have hconj : M * (1 + e) * A' = (1 + e) * scalar (Fin n) (c : K) := by
    rw [← hgm, hgs, hs, coe_slConjugation]
  have hN : M * e * A' = scalar (Fin n) (c : K) * (1 + e) - 1 := by
    have : M * (1 + e) * A' = 1 + M * e * A' := by
      rw [mul_add, add_mul, mul_one, hAA]
    rw [this] at hconj
    rw [(Matrix.scalar_commute (c : K) (fun r => mul_comm _ r) (1 + e)).eq]
    rw [← hconj]; abel
  have hN2 : (M * e * A') * (M * e * A') = 0 := by
    calc (M * e * A') * (M * e * A') = M * e * (A' * M) * e * A' := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hAA', Matrix.mul_one, Matrix.mul_assoc M e e, hee]; simp
  have hc1 : (c : K) = 1 := by
    rw [hN] at hN2
    have := congrFun (congrFun hN2 i) i
    have hij' : (i : Fin n) ≠ j := hij
    simp [Matrix.mul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply, he,
      Matrix.single_apply, hij.symm, Matrix.scalar_apply, Matrix.diagonal_apply] at this
    rw [Finset.sum_eq_single i] at this
    · have hji : ¬ (j = i) := fun h => hij h.symm
      simpa [hji, sub_eq_zero] using this
    · intro x _ hx
      simp [hx, Ne.symm hx]
    · simp
  have hcomm : M * e = e * M := by
    have h3 : M * (1 + e) = (1 + e) * M := by
      have : M * (1 + e) * A' * M = (1 + e) * scalar (Fin n) (c : K) * M := by rw [hconj]
      rw [hc1] at this
      simpa [Matrix.mul_assoc, hAA', Matrix.mul_one] using this
    simpa [Matrix.mul_add, Matrix.add_mul] using h3
  exact hcomm.symm

theorem exists_scalar_of_conjAut_eq_one {A : GL (Fin n) K} (h : conjAut n K A = 1) :
    ∃ l : K, (A : Matrix (Fin n) (Fin n) K) = Matrix.scalar (Fin n) l := by
  obtain ⟨l, hl⟩ := Matrix.mem_range_scalar_of_commute_single
    (fun i j hij => commute_single_of_conjAut_eq_one h hij)
  exact ⟨l, hl.symm⟩

theorem fieldAut_mul_conjAut (σ : K ≃+* K) (A : GL (Fin n) K) :
    fieldAut n K σ * conjAut n K A =
      conjAut n K (GeneralLinearGroup.map σ.toRingHom A) * fieldAut n K σ :=
  mul_inv_eq_iff_eq_mul.1 ((standard_automorphism_transport (K := K) (n := n)).2.2.1 σ A)

@[expose] noncomputable def AiG (σ : K ≃+* K) (A : GL (Fin n) K) : ℕ → GL (Fin n) K
  | 0 => 1
  | k + 1 => A * GeneralLinearGroup.map σ.toRingHom (AiG σ A k)

theorem coe_AiG (σ : K ≃+* K) (A : GL (Fin n) K) (k : ℕ) :
    ((AiG σ A k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Ai σ (A : Matrix (Fin n) (Fin n) K) k := by
  induction k with
  | zero => simp [AiG, Ai]
  | succ k ih =>
    simp only [AiG, Ai, Units.val_mul]
    rw [← ih]
    rfl

theorem conj_fieldAut_pow (σ : K ≃+* K) (A : GL (Fin n) K) (k : ℕ) :
    (conjAut n K A * fieldAut n K σ) ^ k = conjAut n K (AiG σ A k) * fieldAut n K σ ^ k := by
  induction k with
  | zero => simp [AiG]
  | succ k ih =>
    rw [pow_succ', ih, pow_succ', ← mul_assoc, mul_assoc (conjAut n K A), fieldAut_mul_conjAut]
    simp [AiG, mul_assoc]

theorem exists_conj_fieldAut_of_pow_eq_one [Finite K] [NeZero n] (σ : K ≃+* K) (A : GL (Fin n) K)
    (h : (conjAut n K A * fieldAut n K σ) ^ orderOf σ = 1) :
    ∃ B : GL (Fin n) K, conjAut n K A * fieldAut n K σ =
      conjAut n K B * fieldAut n K σ * (conjAut n K B)⁻¹ := by
  have hσ : fieldAut n K σ ^ orderOf σ = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  rw [conj_fieldAut_pow, hσ, mul_one] at h
  obtain ⟨c, hc⟩ := exists_scalar_of_conjAut_eq_one h
  rw [coe_AiG] at hc
  have hc' : Ai σ (A : Matrix (Fin n) (Fin n) K) (orderOf σ) = c • (1 : Matrix (Fin n) (Fin n) K) := by
    rw [hc]; simp [Matrix.smul_one_eq_diagonal]
  have hA : (A : Matrix (Fin n) (Fin n) K).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 A.isUnit).ne_zero
  obtain ⟨l, B, hl, hB, hAB⟩ := hilbert90_matrix σ (A : Matrix (Fin n) (Fin n) K) hA c hc'
  let B' : GL (Fin n) K := GeneralLinearGroup.mkOfDetNeZero B hB
  have hmap : ∀ C : GL (Fin n) K,
      ((GeneralLinearGroup.map σ.toRingHom C : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        (C : Matrix (Fin n) (Fin n) K).map σ := fun C => rfl
  have hU : GeneralLinearGroup.scalar (Fin n) (Units.mk0 l hl) * A =
      B' * (GeneralLinearGroup.map σ.toRingHom B')⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hmap, GeneralLinearGroup.coe_scalar]
    show Matrix.scalar (Fin n) l * (A : Matrix (Fin n) (Fin n) K) * B.map σ = B
    have hsc : Matrix.scalar (Fin n) l * (A : Matrix (Fin n) (Fin n) K) =
        l • (A : Matrix (Fin n) (Fin n) K) := by
      simp [Matrix.smul_eq_diagonal_mul, Matrix.scalar_apply]
    rw [hsc, hAB]
  refine ⟨B', ?_⟩
  have hcA : conjAut n K A = conjAut n K B' * (conjAut n K (GeneralLinearGroup.map σ.toRingHom B'))⁻¹ := by
    have := congrArg (conjAut n K) hU
    rw [map_mul, conjAut_scalar, one_mul, map_mul, map_inv] at this
    exact this
  have hf := fieldAut_mul_conjAut σ B'
  rw [hcA]
  have : (conjAut n K (GeneralLinearGroup.map σ.toRingHom B'))⁻¹ * fieldAut n K σ =
      fieldAut n K σ * (conjAut n K B')⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc]
    exact eq_mul_inv_of_mul_eq hf
  calc conjAut n K B' * (conjAut n K (GeneralLinearGroup.map σ.toRingHom B'))⁻¹ * fieldAut n K σ
      = conjAut n K B' * ((conjAut n K (GeneralLinearGroup.map σ.toRingHom B'))⁻¹ * fieldAut n K σ) := by
        rw [mul_assoc]
    _ = _ := by rw [this, mul_assoc]

theorem exists_semilinear_of_cube_eq_one [Finite K] (hn : 3 ≤ n) {α : MulAut (projectiveSL n K)}
    (h3 : α ^ 3 = 1) :
    ∃ (A : GL (Fin n) K) (σ : K ≃+* K), α = conjAut n K A * fieldAut n K σ ∧ σ ^ 3 = 1 := by
  have hE : α ∈ semilinearAutGroup n K := by
    have hR : α ∈ standardAutGroup n K := by
      rw [(automorphism_generation hn).1]; trivial
    rcases mem_or_mul_dualAut_mem hR with h | h
    · exact h
    · have hδδ := (standard_automorphism_transport (K := K) (n := n)).2.2.2.1
      have he : α = (α * dualAut n K) * dualAut n K := by
        rw [mul_assoc, hδδ, mul_one]
      have hα2 : α ^ 2 ∈ semilinearAutGroup n K := by
        have : α ^ 2 = (α * dualAut n K) * (dualAut n K * (α * dualAut n K) * dualAut n K) := by
          generalize α * dualAut n K = e at he ⊢
          rw [he, pow_two]
          group
        rw [this]
        exact mul_mem h (dualAut_mul_mul_dualAut_mem h)
      have : α = (α ^ 2)⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, ← pow_succ']
        exact h3
      rw [this]
      exact inv_mem hα2
  obtain ⟨A, σ, hα⟩ := mem_semilinearAutGroup_iff.mp hE
  refine ⟨A, σ, hα, ?_⟩
  have h1 : conjAut n K (AiG σ A 3) * fieldAut n K (σ ^ 3) = 1 := by
    rw [map_pow, ← conj_fieldAut_pow, ← hα]
    exact h3
  exact (eq_one_of_conjAut_mul_fieldAut_eq_one hn _ _ h1).1

theorem exists_conj_fieldAut_of_cube_eq_one [Finite K] (hn : 3 ≤ n) {α : MulAut (projectiveSL n K)}
    (h3 : α ^ 3 = 1) (σ : K ≃+* K) (A : GL (Fin n) K) (hα : α = conjAut n K A * fieldAut n K σ)
    (hσ : σ ≠ 1) (hσ3 : σ ^ 3 = 1) :
    orderOf σ = 3 ∧ ∃ B : GL (Fin n) K, α = conjAut n K B * fieldAut n K σ * (conjAut n K B)⁻¹ := by
  have hord : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ
  have : NeZero n := ⟨by omega⟩
  refine ⟨hord, ?_⟩
  rw [hα]
  exact exists_conj_fieldAut_of_pow_eq_one σ A (by rw [hord, ← hα]; exact h3)

end CFSG.HardMathSupport.Foote.ModuleExclusions
