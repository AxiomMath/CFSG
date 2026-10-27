module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4TwoComp
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4TypeOne

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsSp4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag Subgroup

variable {K : Type} [Field K]

variable (K) in
@[expose] def ωJ : (Fin 2 ⊕ Fin 2 → K) →ₗ[K] (Fin 2 ⊕ Fin 2 → K) →ₗ[K] K :=
  Matrix.toBilin' (formJ 2 K)

theorem ωJ_apply (x y : Fin 2 ⊕ Fin 2 → K) : ωJ K x y = x ⬝ᵥ (formJ 2 K *ᵥ y) :=
  Matrix.toBilin'_apply' _ _ _

theorem ωJ_self (x : Fin 2 ⊕ Fin 2 → K) : ωJ K x x = 0 := by
  rw [ωJ_apply]
  simp [dotProduct, Matrix.mulVec, Fintype.sum_sum_type, formJ, mul_comm]
  ring

theorem ωJ_comm (x y : Fin 2 ⊕ Fin 2 → K) : ωJ K x y = -ωJ K y x := by
  have h := ωJ_self (K := K) (x + y)
  simp only [map_add, LinearMap.add_apply, ωJ_self x, ωJ_self y, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_right h

theorem ωJ_nondeg {x : Fin 2 ⊕ Fin 2 → K} (h : ∀ y, ωJ K x y = 0) : x = 0 := by
  have h1 : x ᵥ* formJ 2 K = 0 := by
    refine dotProduct_eq_zero _ fun w => ?_
    rw [← Matrix.dotProduct_mulVec]
    exact (ωJ_apply x w).symm.trans (h w)
  calc x = x ᵥ* (formJ 2 K * -(formJ 2 K)) := by
        rw [Matrix.mul_neg, formJ_mul_formJ, neg_neg, Matrix.vecMul_one]
    _ = 0 := by rw [← Matrix.vecMul_vecMul, h1, Matrix.zero_vecMul]

theorem ωJ_mulVec {A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (hA : Aᵀ * formJ 2 K * A = formJ 2 K) (x y : Fin 2 ⊕ Fin 2 → K) :
    ωJ K (A *ᵥ x) (A *ᵥ y) = ωJ K x y := by
  rw [ωJ_apply, ωJ_apply, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose,
    Matrix.vecMul_vecMul, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hA,
    ← Matrix.dotProduct_mulVec]

@[expose] def frameMat (e f : Fin 2 → (Fin 2 ⊕ Fin 2 → K)) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  Matrix.of fun r k => Sum.elim e f k r

theorem transpose_mul_mul_apply' {ι : Type*} [Fintype ι] (A J : Matrix ι ι K) (k l : ι) :
    (Aᵀ * J * A) k l = (fun r => A r k) ⬝ᵥ (J *ᵥ fun s => A s l) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec, Finset.sum_mul,
    Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem frameMat_symplectic {e f : Fin 2 → (Fin 2 ⊕ Fin 2 → K)}
    (hee : ∀ i j, ωJ K (e i) (e j) = 0) (hff : ∀ i j, ωJ K (f i) (f j) = 0)
    (hef : ∀ i j, ωJ K (e i) (f j) = if i = j then 1 else 0) :
    (frameMat e f)ᵀ * formJ 2 K * frameMat e f = formJ 2 K := by
  ext k l
  rw [transpose_mul_mul_apply']
  have key : ∀ k l, ((fun r => frameMat e f r k) ⬝ᵥ
      (formJ 2 K *ᵥ fun s => frameMat e f s l)) = ωJ K (Sum.elim e f k) (Sum.elim e f l) :=
    fun k l => (ωJ_apply _ _).symm
  rw [key]
  rcases k with i | i <;> rcases l with j | j
  · simp [formJ, hee]
  · simp [formJ, hef, Matrix.one_apply]
  · rw [ωJ_comm]
    simp [formJ, hef, Matrix.one_apply, eq_comm]
  · simp [formJ, hff]

theorem mul_eq_of_mulVec_col {ι : Type*} [Fintype ι] {N A N' : Matrix ι ι K}
    (h : ∀ k, N *ᵥ (fun r => A r k) = A *ᵥ (fun s => N' s k)) : N * A = A * N' := by
  ext r k
  have := congrFun (h k) r
  simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using this

theorem exists_sq_add_sq_eq [Finite K] (h2 : (2 : K) ≠ 0) (c : K) :
    ∃ s t : K, s ^ 2 + t ^ 2 = c := by
  have : Fintype K := Fintype.ofFinite K
  have hodd : Fintype.card K % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one (Fintype.card K) with h | h
    · exfalso
      have hc := FiniteField.even_card_iff_char_two.mpr h
      apply h2
      have := (ringChar.spec K 2).mpr (by rw [hc])
      exact_mod_cast this
    · exact h
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic (R := K)
    (f := Polynomial.X ^ 2) (g := Polynomial.X ^ 2 - Polynomial.C c)
    (Polynomial.degree_X_pow 2) (Polynomial.degree_X_pow_sub_C (by norm_num) _) hodd
  refine ⟨a, b, ?_⟩
  simp only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_C]
    at hab
  linear_combination hab

theorem conj_eq_of_mul_eq {T g N : StatedSp 2 K}
    (h : ((T : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((N : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) :
    g⁻¹ * T * g = N := by
  have h' : T * g = g * N := sp_ext (by
    simp only [Subgroup.coe_mul, Units.val_mul]
    exact h)
  rw [mul_assoc, h', ← mul_assoc, inv_mul_cancel, one_mul]

theorem mulVec_frameMat_single (e f : Fin 2 → (Fin 2 ⊕ Fin 2 → K)) (k : Fin 2 ⊕ Fin 2) (c : K) :
    frameMat e f *ᵥ Pi.single k c = c • Sum.elim e f k := by
  ext r
  rw [mulVec_single]
  simp [frameMat, mul_comm]

theorem mulVec_single_one_apply' (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
    (i j : Fin 2 ⊕ Fin 2) : (A *ᵥ Pi.single j 1) i = A i j := by
  simp [mulVec, dotProduct, Pi.single_apply]

theorem eq_neg_one_of_forall {A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (h : ∀ v, v + A *ᵥ v = 0) : A = -1 := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  rw [Pi.add_apply, mulVec_single_one_apply'] at this
  by_cases hij : i = j
  · subst hij
    simp only [Pi.single_eq_same, Pi.zero_apply] at this
    simp only [Matrix.neg_apply, one_apply_eq]
    linear_combination this
  · simp only [Pi.single_eq_of_ne hij, zero_add, Pi.zero_apply] at this
    simp [Matrix.neg_apply, one_apply_ne hij, this]

theorem eq_one_of_forall {A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (h : ∀ v, v - A *ᵥ v = 0) : A = 1 := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  rw [Pi.sub_apply, mulVec_single_one_apply'] at this
  by_cases hij : i = j
  · subst hij
    simp only [Pi.single_eq_same, Pi.zero_apply] at this
    simp only [one_apply_eq]
    linear_combination -this
  · simp only [Pi.single_eq_of_ne hij, zero_sub, neg_eq_zero, Pi.zero_apply] at this
    simp [one_apply_ne hij, this]

theorem ωJ_add_mulVec {A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (hA : Aᵀ * formJ 2 K * A = formJ 2 K) {x : Fin 2 ⊕ Fin 2 → K} (hx : A *ᵥ x = x)
    (w : Fin 2 ⊕ Fin 2 → K) : ωJ K x (w + A *ᵥ w) = 2 * ωJ K x w := by
  have e1 : ωJ K x (A *ᵥ w) = ωJ K x w := by
    conv_lhs => rw [← hx]
    exact ωJ_mulVec hA x w
  rw [map_add, e1]
  ring

theorem ωJ_sub_mulVec {A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (hA : Aᵀ * formJ 2 K * A = formJ 2 K) {x : Fin 2 ⊕ Fin 2 → K} (hx : A *ᵥ x = -x)
    (w : Fin 2 ⊕ Fin 2 → K) : ωJ K x (w - A *ᵥ w) = 2 * ωJ K x w := by
  have e1 : ωJ K x (A *ᵥ w) = -ωJ K x w := by
    have h := ωJ_mulVec hA x w
    rw [hx, map_neg, LinearMap.neg_apply] at h
    linear_combination -h
  rw [map_sub, e1]
  ring

theorem ωJ_eq_zero_of_eig (h2 : (2 : K) ≠ 0) {A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (hA : Aᵀ * formJ 2 K * A = formJ 2 K) {a b : Fin 2 ⊕ Fin 2 → K} (ha : A *ᵥ a = a)
    (hb : A *ᵥ b = -b) : ωJ K a b = 0 := by
  have h := ωJ_mulVec hA a b
  rw [ha, hb, map_neg] at h
  exact (mul_eq_zero.mp (by linear_combination -h : (2 : K) * ωJ K a b = 0)).resolve_left h2

theorem exists_conj_T1 (h2 : (2 : K) ≠ 0) (T : StatedSp 2 K)
    (hTT : ((T : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((T : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1)
    (h1 : ((T : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ≠ 1)
    (hm : ((T : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ≠ -1) :
    ∃ g : StatedSp 2 K, g⁻¹ * T * g = T1 K := by
  set A := ((T : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) with hAdef
  have hA := symplectic_of_mem T
  have hplus : ∀ v, A *ᵥ (v + A *ᵥ v) = v + A *ᵥ v := fun v => by
    rw [mulVec_add, mulVec_mulVec, hTT, one_mulVec, add_comm]
  have hminus : ∀ v, A *ᵥ (v - A *ᵥ v) = -(v - A *ᵥ v) := fun v => by
    rw [mulVec_sub, mulVec_mulVec, hTT, one_mulVec, neg_sub]
  obtain ⟨v, hv⟩ : ∃ v, v + A *ᵥ v ≠ 0 := by
    by_contra h
    push Not at h
    exact hm (eq_neg_one_of_forall h)
  obtain ⟨v', hv'⟩ : ∃ v, v - A *ᵥ v ≠ 0 := by
    by_contra h
    push Not at h
    exact h1 (eq_one_of_forall h)
  set x₁ := v + A *ᵥ v with hx₁
  set x₂ := v' - A *ᵥ v' with hx₂
  have hAx₁ : A *ᵥ x₁ = x₁ := hplus v
  have hAx₂ : A *ᵥ x₂ = -x₂ := hminus v'
  obtain ⟨w, hw⟩ : ∃ w, ωJ K x₁ w ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (ωJ_nondeg h)
  obtain ⟨w', hw'⟩ : ∃ w, ωJ K x₂ w ≠ 0 := by
    by_contra h
    push Not at h
    exact hv' (ωJ_nondeg h)
  set y₀ := w + A *ᵥ w with hy₀
  set y₀' := w' - A *ᵥ w' with hy₀'
  have hAy₀ : A *ᵥ y₀ = y₀ := hplus w
  have hAy₀' : A *ᵥ y₀' = -y₀' := hminus w'
  have hxy : ωJ K x₁ y₀ ≠ 0 := by
    rw [hy₀, ωJ_add_mulVec hA hAx₁]
    exact mul_ne_zero h2 hw
  have hxy' : ωJ K x₂ y₀' ≠ 0 := by
    rw [hy₀', ωJ_sub_mulVec hA hAx₂]
    exact mul_ne_zero h2 hw'
  set y₁ := (ωJ K x₁ y₀)⁻¹ • y₀ with hy₁
  set y₂ := (ωJ K x₂ y₀')⁻¹ • y₀' with hy₂
  have hAy₁ : A *ᵥ y₁ = y₁ := by rw [hy₁, mulVec_smul, hAy₀]
  have hAy₂ : A *ᵥ y₂ = -y₂ := by rw [hy₂, mulVec_smul, hAy₀', smul_neg]
  have hx₁y₁ : ωJ K x₁ y₁ = 1 := by rw [hy₁, map_smul, smul_eq_mul, inv_mul_cancel₀ hxy]
  have hx₂y₂ : ωJ K x₂ y₂ = 1 := by rw [hy₂, map_smul, smul_eq_mul, inv_mul_cancel₀ hxy']
  have orth : ∀ {a b}, A *ᵥ a = a → A *ᵥ b = -b → ωJ K a b = 0 := fun ha hb =>
    ωJ_eq_zero_of_eig h2 hA ha hb
  have orth' : ∀ {a b}, A *ᵥ a = -a → A *ᵥ b = b → ωJ K a b = 0 := fun ha hb => by
    rw [ωJ_comm, orth hb ha, neg_zero]
  let e : Fin 2 → (Fin 2 ⊕ Fin 2 → K) := ![x₁, x₂]
  let f : Fin 2 → (Fin 2 ⊕ Fin 2 → K) := ![y₁, y₂]
  have hsym : (frameMat e f)ᵀ * formJ 2 K * frameMat e f = formJ 2 K := by
    refine frameMat_symplectic ?_ ?_ ?_ <;> intro i j <;> fin_cases i <;> fin_cases j <;>
      simp [e, f, ωJ_self, orth hAx₁ hAx₂, orth' hAx₂ hAx₁, orth hAy₁ hAy₂, orth' hAy₂ hAy₁,
        orth hAx₁ hAy₂, orth' hAx₂ hAy₁, hx₁y₁, hx₂y₂]
  refine ⟨toSp (frameMat e f) hsym, conj_eq_of_mul_eq ?_⟩
  rw [coe_toSp, coe_T1, blk_one_neg_one_eq_diagonal, ← hAdef]
  apply mul_eq_of_mulVec_col
  intro k
  have hcol : ∀ k, (fun r => frameMat e f r k) = Sum.elim e f k := fun k => rfl
  rw [hcol, show (fun s => diagonal (Sum.elim ![(1 : K), -1] ![1, -1]) s k) =
    Pi.single k (Sum.elim ![(1 : K), -1] ![1, -1] k) from by
      ext s
      by_cases hsk : s = k
      · subst hsk
        simp
      · simp [diagonal_apply_ne _ hsk, Pi.single_eq_of_ne hsk], mulVec_frameMat_single]
  rcases k with (k | k) <;> fin_cases k <;> simp [e, f, hAx₁, hAx₂, hAy₁, hAy₂]

theorem β_scale {A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (hAA : ∀ v, A *ᵥ (A *ᵥ v) = -v)
    (x : Fin 2 ⊕ Fin 2 → K) (s t : K) :
    ωJ K (s • x + t • A *ᵥ x) (A *ᵥ (s • x + t • A *ᵥ x)) = (s ^ 2 + t ^ 2) * ωJ K x (A *ᵥ x) := by
  have e1 : ωJ K (A *ᵥ x) (A *ᵥ x) = 0 := ωJ_self _
  have e2 : ωJ K (A *ᵥ x) x = -ωJ K x (A *ᵥ x) := ωJ_comm _ _
  have e3 : ωJ K x x = 0 := ωJ_self _
  rw [mulVec_add, mulVec_smul, mulVec_smul, hAA]
  simp only [map_add, map_smul, map_neg, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, e1, e2, e3]
  ring

theorem exists_mul_eq_negJ [Finite K] (h2 : (2 : K) ≠ 0) (T : StatedSp 2 K)
    (hTT : ((T : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((T : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = -1) :
    ∃ g : StatedSp 2 K,
      ((T : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * -formJ 2 K := by
  set A := ((T : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) with hAdef
  have hA := symplectic_of_mem T
  have hAA : ∀ v, A *ᵥ (A *ᵥ v) = -v := fun v => by
    rw [mulVec_mulVec, hTT, neg_mulVec, one_mulVec]
  have hβsymm : ∀ x y, ωJ K y (A *ᵥ x) = ωJ K x (A *ᵥ y) := by
    intro x y
    rw [ωJ_comm, ← ωJ_mulVec hA (A *ᵥ x) y, hAA, map_neg, LinearMap.neg_apply, neg_neg]
  have hβ0 : ∃ x, ωJ K x (A *ᵥ x) ≠ 0 := by
    by_contra h
    push Not at h
    have hpol : ∀ x y, ωJ K x (A *ᵥ y) = 0 := by
      intro x y
      have h1 := h (x + y)
      rw [mulVec_add] at h1
      simp only [map_add, LinearMap.add_apply] at h1
      rw [h x, h y, hβsymm x y] at h1
      exact (mul_eq_zero.mp (by linear_combination h1 :
        (2 : K) * ωJ K x (A *ᵥ y) = 0)).resolve_left h2
    have he : (Pi.single (Sum.inl 0) (1 : K) : Fin 2 ⊕ Fin 2 → K) = 0 := by
      apply ωJ_nondeg
      intro y
      have := hpol (Pi.single (Sum.inl 0) 1) (-(A *ᵥ y))
      rwa [mulVec_neg, hAA, neg_neg] at this
    have := congrFun he (Sum.inl 0)
    simp at this
  obtain ⟨x, hx⟩ := hβ0
  obtain ⟨s, t, hst⟩ := exists_sq_add_sq_eq h2 (ωJ K x (A *ᵥ x))⁻¹
  set x₁ := s • x + t • A *ᵥ x with hx₁
  have hβx₁ : ωJ K x₁ (A *ᵥ x₁) = 1 := by
    rw [hx₁, β_scale hAA, hst, inv_mul_cancel₀ hx]
  let InW : (Fin 2 ⊕ Fin 2 → K) → Prop := fun w => ωJ K w x₁ = 0 ∧ ωJ K w (A *ᵥ x₁) = 0
  have hWadd : ∀ w z, InW w → InW z → InW (w + z) := fun w z hw hz => by
    simp only [InW, map_add, LinearMap.add_apply, hw.1, hz.1, hw.2, hz.2, add_zero, and_self]
  have hWsmul : ∀ (c : K) w, InW w → InW (c • w) := fun c w hw => by
    simp only [InW, map_smul, LinearMap.smul_apply, hw.1, hw.2, smul_zero, and_self]
  have hWA : ∀ w, InW w → InW (A *ᵥ w) := fun w hw => by
    refine ⟨?_, ?_⟩
    · rw [← ωJ_mulVec hA (A *ᵥ w) x₁, hAA, map_neg, LinearMap.neg_apply, hw.2, neg_zero]
    · rw [ωJ_mulVec hA w x₁]
      exact hw.1
  obtain ⟨w₀, hw₀, hw₀ne⟩ : ∃ w ∈ LinearMap.ker (((ωJ K).flip x₁).prod ((ωJ K).flip (A *ᵥ x₁))),
      w ≠ 0 := by
    apply Submodule.exists_mem_ne_zero_of_ne_bot
    apply LinearMap.ker_ne_bot_of_finrank_lt
    simp
  have hInW₀ : InW w₀ := by
    have := LinearMap.mem_ker.mp hw₀
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  have hβW : ∃ x' : Fin 2 ⊕ Fin 2 → K, InW x' ∧ ωJ K x' (A *ᵥ x') ≠ 0 := by
    by_contra h
    push Not at h
    have hpol : ∀ w z, InW w → InW z → ωJ K w (A *ᵥ z) = 0 := by
      intro w z hw hz
      have h1 := h (w + z) (hWadd w z hw hz)
      rw [mulVec_add] at h1
      simp only [map_add, LinearMap.add_apply] at h1
      rw [h w hw, h z hz, hβsymm w z] at h1
      exact (mul_eq_zero.mp (by linear_combination h1 :
        (2 : K) * ωJ K w (A *ᵥ z) = 0)).resolve_left h2
    apply hw₀ne
    apply ωJ_nondeg
    intro v
    set a := ωJ K v (A *ᵥ x₁)
    set b := -ωJ K v x₁
    set w' := v - a • x₁ - b • A *ᵥ x₁ with hw'
    have hx₁x₁ : ωJ K x₁ x₁ = 0 := ωJ_self _
    have hAx₁x₁ : ωJ K (A *ᵥ x₁) x₁ = -1 := by rw [ωJ_comm, hβx₁]
    have hAx₁Ax₁ : ωJ K (A *ᵥ x₁) (A *ᵥ x₁) = 0 := ωJ_self _
    have hInW' : InW w' := by
      refine ⟨?_, ?_⟩
      · simp only [hw', map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
          hx₁x₁, hAx₁x₁, b]
        ring
      · simp only [hw', map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
          hβx₁, hAx₁Ax₁, a]
        ring
    have hv : v = a • x₁ + b • A *ᵥ x₁ + w' := by rw [hw']; abel
    have hww' : ωJ K w₀ w' = 0 := by
      have hz : InW (-(A *ᵥ w')) := by
        simpa using hWsmul (-1) _ (hWA w' hInW')
      have hAz : A *ᵥ (-(A *ᵥ w')) = w' := by rw [mulVec_neg, hAA, neg_neg]
      have h3 := hpol w₀ _ hInW₀ hz
      rwa [hAz] at h3
    rw [hv, map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hInW₀.1, hInW₀.2,
      hww']
    ring
  obtain ⟨x', hx'W, hx'⟩ := hβW
  obtain ⟨s', t', hst'⟩ := exists_sq_add_sq_eq h2 (ωJ K x' (A *ᵥ x'))⁻¹
  set x₂ := s' • x' + t' • A *ᵥ x' with hx₂
  have hβx₂ : ωJ K x₂ (A *ᵥ x₂) = 1 := by
    rw [hx₂, β_scale hAA, hst', inv_mul_cancel₀ hx']
  have hx₂W : InW x₂ := hWadd _ _ (hWsmul _ _ hx'W) (hWsmul _ _ (hWA _ hx'W))
  let e : Fin 2 → (Fin 2 ⊕ Fin 2 → K) := ![x₁, x₂]
  let f : Fin 2 → (Fin 2 ⊕ Fin 2 → K) := ![A *ᵥ x₁, A *ᵥ x₂]
  have h12 : ωJ K x₁ x₂ = 0 := by rw [ωJ_comm, hx₂W.1, neg_zero]
  have h21 : ωJ K x₂ x₁ = 0 := hx₂W.1
  have hA12 : ωJ K (A *ᵥ x₁) (A *ᵥ x₂) = 0 := by rw [ωJ_mulVec hA, h12]
  have hA21 : ωJ K (A *ᵥ x₂) (A *ᵥ x₁) = 0 := by rw [ωJ_mulVec hA, h21]
  have hx₁Ax₂ : ωJ K x₁ (A *ᵥ x₂) = 0 := by rw [← hβsymm, hx₂W.2]
  have hx₂Ax₁ : ωJ K x₂ (A *ᵥ x₁) = 0 := hx₂W.2
  have hsym : (frameMat e f)ᵀ * formJ 2 K * frameMat e f = formJ 2 K := by
    refine frameMat_symplectic ?_ ?_ ?_ <;> intro i j <;> fin_cases i <;> fin_cases j <;>
      simp [e, f, ωJ_self, h12, h21, hA12, hA21, hx₁Ax₂, hx₂Ax₁, hβx₁, hβx₂]
  refine ⟨toSp (frameMat e f) hsym, ?_⟩
  rw [coe_toSp]
  apply mul_eq_of_mulVec_col
  intro k
  have hcol : ∀ k, (fun r => frameMat e f r k) = Sum.elim e f k := fun k => rfl
  rw [hcol]
  rcases k with (k | k)
  · have hJ : (fun s => (-formJ 2 K) s (Sum.inl k)) = Pi.single (Sum.inr k) (1 : K) := by
      ext s
      rcases s with (s | s) <;> by_cases hsk : s = k <;>
        simp [formJ, hsk, one_apply]
    rw [hJ, mulVec_frameMat_single, one_smul]
    fin_cases k <;> simp [e, f]
  · have hJ : (fun s => (-formJ 2 K) s (Sum.inr k)) = Pi.single (Sum.inl k) (-1 : K) := by
      ext s
      rcases s with (s | s) <;> by_cases hsk : s = k <;>
        simp [formJ, hsk, one_apply]
    rw [hJ, mulVec_frameMat_single, neg_one_smul]
    fin_cases k <;> simp [e, f, hAA]

theorem T2_mul_T2 : (((T2 K : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * (((T2 K : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = -1 := by
  rw [coe_T2, kron_mul, Matrix.one_mul, J₁_mul_J₁, zero_smul, add_zero, neg_one_smul,
    ← neg_one_smul K (1 : Matrix (Fin 2) (Fin 2) K), ← kron_smul_left, neg_one_smul,
    kron_neg_one_one]

theorem exists_conj_T2 [Finite K] (h2 : (2 : K) ≠ 0) (T : StatedSp 2 K)
    (hTT : ((T : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((T : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = -1) :
    ∃ g : StatedSp 2 K, g⁻¹ * T * g = T2 K := by
  have hJ : (-formJ 2 K)ᵀ * formJ 2 K * -formJ 2 K = formJ 2 K := by
    simp only [transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
    rw [formJ, fromBlocks_transpose]
    simp [fromBlocks_multiply]
  obtain ⟨g, hg⟩ := exists_mul_eq_negJ h2 T hTT
  obtain ⟨g₀, hg₀⟩ := exists_mul_eq_negJ h2 (T2 K) T2_mul_T2
  have e1 : g⁻¹ * T * g = toSp (-formJ 2 K) hJ := conj_eq_of_mul_eq (by rw [coe_toSp]; exact hg)
  have e2 : g₀⁻¹ * T2 K * g₀ = toSp (-formJ 2 K) hJ :=
    conj_eq_of_mul_eq (by rw [coe_toSp]; exact hg₀)
  refine ⟨g * g₀⁻¹, ?_⟩
  calc (g * g₀⁻¹)⁻¹ * T * (g * g₀⁻¹) = g₀ * (g⁻¹ * T * g) * g₀⁻¹ := by group
    _ = g₀ * (g₀⁻¹ * T2 K * g₀) * g₀⁻¹ := by rw [e1, e2]
    _ = T2 K := by group

theorem exists_conj_of_orderOf_eq_two [Finite K] (hodd : Odd (Nat.card K))
    {u : StatedProj (StatedSp 2 K)} (hu : orderOf u = 2) :
    ∃ g : StatedProj (StatedSp 2 K), g⁻¹ * u * g = u1 K ∨ g⁻¹ * u * g = u2 K := by
  have h2 := two_ne_zero_of_odd_card hodd
  obtain ⟨T, rfl⟩ := proj_surjective u
  have hT1 : proj 2 K T ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hu
    norm_num at hu
  have hT2 : T * T ∈ spScalars 2 K := by
    have h1 := pow_orderOf_eq_one (proj 2 K T)
    rw [hu] at h1
    rw [← ker_proj, MonoidHom.mem_ker, map_mul, ← pow_two]
    exact h1
  rw [mem_spScalars_iff, Subgroup.coe_mul, Units.val_mul] at hT2
  have hne : ((T : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ≠ 1 ∧
      ((T : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ≠ -1 := by
    constructor <;> intro h <;> apply hT1 <;>
      rw [← MonoidHom.mem_ker, ker_proj, mem_spScalars_iff] <;> simp [h]
  rcases hT2 with h | h
  · obtain ⟨g, hg⟩ := exists_conj_T1 h2 T h hne.1 hne.2
    exact ⟨proj 2 K g, Or.inl (by rw [← map_inv, ← map_mul, ← map_mul, hg]; rfl)⟩
  · obtain ⟨g, hg⟩ := exists_conj_T2 h2 T h
    exact ⟨proj 2 K g, Or.inr (by rw [← map_inv, ← map_mul, ← map_mul, hg]; rfl)⟩

end CFSG.ComponentClassification.CatFactsSp4
