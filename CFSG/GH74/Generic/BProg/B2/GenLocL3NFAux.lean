module

public import CFSG.GH74.Generic.BProg.B2.GenLocDiag
public import CFSG.GH74.Generic.BProg.B2.GenLocL3NFLin
public import CFSG.GH74.KGroups.L3EpsLin
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedGraphTools

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix

@[expose] def frameStab (n : ℕ) (K : Type) [Field K] : Subgroup (MulAut (LinearFlag.projectiveSL n K)) :=
  Subgroup.closure ((Set.range fun x : {x : GL (Fin n) K // ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).IsDiag} =>
      LinearFlag.conjAut n K x.1) ∪ Set.range (LinearFlag.fieldAut n K) ∪ {LinearFlag.dualAut n K})

namespace GenLocL3NFAux

section Matrix

variable {F : Type} [Field F]

theorem eq_one_of_map_eq_smul {φ : F ≃+* F} (R : Matrix (Fin 3) (Fin 3) F) (hR : R * R = 1) {lam : F}
    (h : R.map φ = lam • R) : lam = 1 := by
  have h1 : (R.map φ) * (R.map φ) = 1 := by
    rw [← Matrix.map_mul, hR]
    exact Matrix.map_one _ (map_zero φ) (map_one φ)
  rw [h, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hR] at h1
  have hl2 : lam * lam = 1 := by
    have := congrFun (congrFun h1 0) 0
    simpa using this
  have hdet : R.det * R.det = 1 := by
    rw [← det_mul, hR, det_one]
  have hdφ : φ R.det = R.det := by
    rcases mul_self_eq_one_iff.mp hdet with h' | h'
    · rw [h', map_one]
    · rw [h', map_neg, map_one]
  have h3 : lam ^ 3 * R.det = R.det := by
    have := congrArg Matrix.det h
    rw [det_smul, Fintype.card_fin] at this
    have h4 : (R.map φ).det = φ R.det := (RingHom.map_det (φ : F →+* F) R).symm
    rw [h4, hdφ] at this
    exact this.symm
  have hd0 : R.det ≠ 0 := by
    intro h0
    rw [h0] at hdet
    simp at hdet
  have h5 : lam ^ 3 = 1 := mul_right_cancel₀ hd0 (h3.trans (one_mul _).symm)
  calc lam = lam * (lam * lam) := by rw [hl2, mul_one]
    _ = lam ^ 3 := by ring
    _ = 1 := h5

theorem eq_one_of_sandwich (R B : Matrix (Fin 3) (Fin 3) F) (hR : R * R = 1) (hB : B.det ≠ 0) {lam : F}
    (h : R * B * Rᵀ = lam • B) : lam = 1 := by
  have hRt : Rᵀ * Rᵀ = 1 := by rw [← transpose_mul, hR, transpose_one]
  have h1 : B = (lam * lam) • B := by
    have e1 : R * (R * B * Rᵀ) * Rᵀ = B := by
      calc R * (R * B * Rᵀ) * Rᵀ = (R * R) * B * (Rᵀ * Rᵀ) := by simp only [Matrix.mul_assoc]
        _ = B := by rw [hR, hRt, Matrix.one_mul, Matrix.mul_one]
    rw [h, Matrix.mul_smul, Matrix.smul_mul, h, smul_smul] at e1
    exact e1.symm
  have hBne : B ≠ 0 := fun h0 => hB (by rw [h0]; simp)
  obtain ⟨i, j, hij⟩ : ∃ i j, B i j ≠ 0 := by
    by_contra! hc
    exact hBne (Matrix.ext fun i j => by simpa using hc i j)
  have hl2 : lam * lam = 1 := by
    have := congrFun (congrFun h1 i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    have h3 : ((lam * lam) - 1) * B i j = 0 := by linear_combination -this
    exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right hij)
  have hdet : R.det * R.det = 1 := by rw [← det_mul, hR, det_one]
  have h3 : lam ^ 3 = 1 := by
    have := congrArg Matrix.det h
    rw [det_mul, det_mul, det_transpose, det_smul, Fintype.card_fin] at this
    have h4 : (R.det * R.det) * B.det = lam ^ 3 * B.det := by linear_combination this
    rw [hdet, one_mul] at h4
    exact mul_right_cancel₀ hB (h4.symm.trans (one_mul _).symm)
  calc lam = lam * (lam * lam) := by rw [hl2, mul_one]
    _ = lam ^ 3 := by ring
    _ = 1 := h3

end Matrix

section Hilbert

variable {F : Type} [Field F]

theorem exists_mu {φ : F ≃+* F} (hφ : ∀ x, φ (φ x) = x) (hφ1 : φ ≠ 1) {lam : F}
    (hlam : lam * φ lam = 1) : ∃ μ : F, μ ≠ 0 ∧ φ μ * lam = μ := by
  obtain ⟨w, hw⟩ : ∃ w, φ w ≠ w := by
    by_contra! h
    exact hφ1 (RingEquiv.ext h)
  have key : ∀ x : F, x + lam * φ x ≠ 0 → ∃ μ : F, μ ≠ 0 ∧ φ μ * lam = μ := fun x hx =>
    ⟨x + lam * φ x, hx, by
      rw [map_add, map_mul, hφ]
      linear_combination x * hlam⟩
  by_cases h1 : (1 : F) + lam * φ 1 = 0
  · by_cases h2 : w + lam * φ w = 0
    · exfalso
      rw [map_one, mul_one] at h1
      have : lam = -1 := by linear_combination h1
      rw [this] at h2
      apply hw
      linear_combination -h2
    · exact key w h2
  · exact key 1 h1

theorem isDiag_of_mul_eq_one {n : ℕ} {Y Z : Matrix (Fin n) (Fin n) F} (hZ : Z.IsDiag) (h : Y * Z = 1) :
    Y.IsDiag := by
  have h1 : Z⁻¹ = Y := Matrix.inv_eq_left_inv h
  rw [← h1, ← hZ.diagonal_diag, Matrix.inv_diagonal]
  exact isDiag_diagonal _

end Hilbert

section Basic

variable {K : Type} [Field K] [Finite K]

theorem scalar_of_conjAut_eq (X Y : GL (Fin 3) K) (h : LinearFlag.conjAut 3 K X = LinearFlag.conjAut 3 K Y) :
    ∃ c : K, c ≠ 0 ∧ (Y : Matrix (Fin 3) (Fin 3) K) = c • (X : Matrix (Fin 3) (Fin 3) K) := by
  have h1 : LinearFlag.conjAut 3 K (X⁻¹ * Y) * LinearFlag.fieldAut 3 K 1 = 1 := by
    rw [map_one, mul_one, map_mul, map_inv, h, inv_mul_cancel]
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (by norm_num) _ _ h1
  refine ⟨c, c.ne_zero, ?_⟩
  have hY : Y = X * GeneralLinearGroup.scalar (Fin 3) c := by rw [hc]; group
  have hscal : ((GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (c : K) • (1 : Matrix (Fin 3) (Fin 3) K) := by
    rw [smul_one_eq_diagonal]
    rfl
  rw [hY, Units.val_mul, hscal, Matrix.mul_smul, Matrix.mul_one]

theorem transpose_eq_of_sq (h2 : (2 : K) ≠ 0) (A : GL (Fin 3) K)
    (hα : (LinearFlag.conjAut 3 K A * LinearFlag.dualAut 3 K) ^ 2 = 1) : (A : Matrix (Fin 3) (Fin 3) K)ᵀ = A := by
  rcases transpose_eq_or_eq_neg_of_sq_conjAut_dualAut (by norm_num) A hα with h | h
  · exact h
  · exfalso
    have h3 := congrArg Matrix.det h
    rw [det_transpose, det_neg, Fintype.card_fin] at h3
    have hd : (A : Matrix (Fin 3) (Fin 3) K).det ≠ 0 := (Matrix.isUnits_det_units A).ne_zero
    apply hd
    have : (2 : K) * (A : Matrix (Fin 3) (Fin 3) K).det = 0 := by linear_combination h3
    exact (mul_eq_zero.mp this).resolve_left h2

theorem conj_injective : Function.Injective
    (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)) := by
  rw [injective_iff_map_eq_one]
  intro s hs
  obtain ⟨g, rfl⟩ := LinearFlag.proj_surjective 3 K s
  rw [← conjAut_toGL] at hs
  have h1 : LinearFlag.conjAut 3 K (SpecialLinearGroup.toGL g) * LinearFlag.fieldAut 3 K 1 = 1 := by
    rw [map_one, mul_one]; exact hs
  obtain ⟨-, u, hu⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (by norm_num) _ _ h1
  have hgu : (g : Matrix (Fin 3) (Fin 3) K) = scalar (Fin 3) (u : K) := by
    have h2 := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K)) hu
    simpa [GeneralLinearGroup.coe_scalar] using h2.symm
  have hun : u ^ 3 = 1 := by
    apply Units.ext
    have h3 := g.2
    rw [hgu, scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at h3
    rw [Units.val_pow_eq_pow_val, h3, Units.val_one]
  exact (QuotientGroup.eq_one_iff g).2 ⟨u, hun, hgu⟩

theorem exists_lift_inner (hK2 : ringChar K ≠ 2) {D : Subgroup (MulAut (projectiveSL 3 K))}
    (hD : CFSG.IsElementaryAbelian 2 ↥D) :
    ∃ (E : Subgroup (projectiveSL 3 K)) (ρ : ↥E →* GL (Fin 3) K),
      (∀ e, ρ e * ρ e = 1) ∧ (∀ e, LinearFlag.conjAut 3 K (ρ e) = MulAut.conj (e : projectiveSL 3 K)) ∧
      (∀ e : E, MulAut.conj (e : projectiveSL 3 K) ∈ D) ∧
      (∀ x ∈ D, (∃ A, x = LinearFlag.conjAut 3 K A) → ∃ e : E, x = MulAut.conj (e : projectiveSL 3 K)) ∧
      (∀ e e' : E, ρ e * ρ e' = ρ e' * ρ e) := by
  obtain ⟨hcomm, hsq⟩ := WeakSigGen.forall_of_isElementaryAbelian hD
  let E : Subgroup (projectiveSL 3 K) := D.comap (MulAut.conj : projectiveSL 3 K →* MulAut _)
  have hinj := conj_injective (K := K)
  have hEc : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e := fun e he e' he' =>
    hinj (by rw [map_mul, map_mul]; exact hcomm _ he _ he')
  have hEs : ∀ e ∈ E, e * e = 1 := fun e he =>
    hinj (by rw [map_mul, map_one]; exact hsq _ he)
  have hE : CFSG.IsElementaryAbelian 2 ↥E := WeakSigGen.isElementaryAbelian_of_forall hEc hEs
  obtain ⟨B, ρ, hρ, hρc⟩ := exists_diag_lift_of_odd (n := 3) ⟨1, rfl⟩ hK2 E hE
  refine ⟨E, ρ, fun e => (hρ e).2, hρc, fun e => e.2, ?_, fun e e' => ?_⟩
  · rintro x hx ⟨A, rfl⟩
    have hx2 : LinearFlag.conjAut 3 K A ^ 2 ^ 1 = 1 := by rw [pow_one, sq]; exact hsq _ hx
    obtain ⟨g, hg⟩ := CFSG.GH74.KGroups.L3Eps.conj_pow_inner A hx2
    exact ⟨⟨LinearFlag.proj 3 K g, by show MulAut.conj (LinearFlag.proj 3 K g) ∈ D; rw [← hg]; exact hx⟩, hg⟩
  · rw [← map_mul, ← map_mul]
    exact congrArg ρ (Subtype.ext (hEc _ e.2 _ e'.2))

theorem rep_of_mem {D : Subgroup (MulAut (projectiveSL 3 K))} (hD : CFSG.IsElementaryAbelian 2 ↥D)
    {x : MulAut (projectiveSL 3 K)} (hx : x ∈ D) :
    ∃ (A : GL (Fin 3) K) (σ : K ≃+* K) (ε : ℕ), ε ≤ 1 ∧ σ * σ = 1 ∧
      x = LinearFlag.conjAut 3 K A * LinearFlag.fieldAut 3 K σ * LinearFlag.dualAut 3 K ^ ε := by
  obtain ⟨-, hsq⟩ := WeakSigGen.forall_of_isElementaryAbelian hD
  have hx2 := hsq x hx
  obtain ⟨A, σ, ε, hε, rfl⟩ := ((LinearFlag.automorphism_generation (K := K) (n := 3) (by norm_num)).2 x)
  refine ⟨A, σ, ε, hε, ?_, rfl⟩
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hε with rfl | rfl
  · rw [pow_zero, mul_one, conjAut_mul_fieldAut_mul] at hx2
    exact (eq_one_of_conjAut_mul_fieldAut_eq_one (by norm_num) _ _ hx2).1
  · rw [pow_one, ← sq, sq_conjAut_fieldAut_dualAut] at hx2
    exact (eq_one_of_conjAut_mul_fieldAut_eq_one (by norm_num) _ _ hx2).1

theorem shape4 {φ : K ≃+* K} (huniq : ∀ σ : K ≃+* K, σ * σ = 1 → σ = 1 ∨ σ = φ)
    {D : Subgroup (MulAut (projectiveSL 3 K))} (hD : CFSG.IsElementaryAbelian 2 ↥D)
    {x : MulAut (projectiveSL 3 K)} (hx : x ∈ D) :
    (∃ A, x = LinearFlag.conjAut 3 K A) ∨ (∃ A, x = LinearFlag.conjAut 3 K A * LinearFlag.dualAut 3 K) ∨
      (∃ A, x = LinearFlag.conjAut 3 K A * LinearFlag.fieldAut 3 K φ) ∨
      (∃ A, x = LinearFlag.conjAut 3 K A * LinearFlag.fieldAut 3 K φ * LinearFlag.dualAut 3 K) := by
  obtain ⟨A, σ, ε, hε, hσ, rfl⟩ := rep_of_mem hD hx
  rcases huniq σ hσ with rfl | rfl <;> rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hε with rfl | rfl
  · exact Or.inl ⟨A, by rw [map_one, mul_one, pow_zero, mul_one]⟩
  · exact Or.inr (Or.inl ⟨A, by rw [map_one, mul_one, pow_one]⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨A, by rw [pow_zero, mul_one]⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨A, by rw [pow_one]⟩))

end Basic

section Ok

variable {K : Type} [Field K]

theorem conjAut_mem_frameStab {x : GL (Fin 3) K}
    (hx : ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag) :
    LinearFlag.conjAut 3 K x ∈ frameStab 3 K :=
  Subgroup.subset_closure (Or.inl (Or.inl ⟨⟨x, hx⟩, rfl⟩))

theorem fieldAut_mem_frameStab (σ : K ≃+* K) : LinearFlag.fieldAut 3 K σ ∈ frameStab 3 K :=
  Subgroup.subset_closure (Or.inl (Or.inr ⟨σ, rfl⟩))

theorem dualAut_mem_frameStab : LinearFlag.dualAut 3 K ∈ frameStab 3 K :=
  Subgroup.subset_closure (Or.inr rfl)

@[expose] def OkC (C : GL (Fin 3) K) (x : MulAut (projectiveSL 3 K)) : Prop :=
  (LinearFlag.conjAut 3 K C)⁻¹ * x * LinearFlag.conjAut 3 K C ∈ frameStab 3 K

theorem OkC.mul {C : GL (Fin 3) K} {x y : MulAut (projectiveSL 3 K)} (hx : OkC C x) (hy : OkC C y) :
    OkC C (x * y) := by
  have : (LinearFlag.conjAut 3 K C)⁻¹ * (x * y) * LinearFlag.conjAut 3 K C =
      ((LinearFlag.conjAut 3 K C)⁻¹ * x * LinearFlag.conjAut 3 K C) *
        ((LinearFlag.conjAut 3 K C)⁻¹ * y * LinearFlag.conjAut 3 K C) := by group
  unfold OkC
  rw [this]
  exact mul_mem hx hy

theorem OkC.inv {C : GL (Fin 3) K} {x : MulAut (projectiveSL 3 K)} (hx : OkC C x) : OkC C x⁻¹ := by
  have : (LinearFlag.conjAut 3 K C)⁻¹ * x⁻¹ * LinearFlag.conjAut 3 K C =
      ((LinearFlag.conjAut 3 K C)⁻¹ * x * LinearFlag.conjAut 3 K C)⁻¹ := by group
  unfold OkC
  rw [this]
  exact inv_mem hx

theorem okC_conjAut (C R : GL (Fin 3) K)
    (h : ((C⁻¹ * R * C : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag) :
    OkC C (LinearFlag.conjAut 3 K R) := by
  have : (LinearFlag.conjAut 3 K C)⁻¹ * LinearFlag.conjAut 3 K R * LinearFlag.conjAut 3 K C =
      LinearFlag.conjAut 3 K (C⁻¹ * R * C) := by rw [map_mul, map_mul, map_inv]
  unfold OkC
  rw [this]
  exact conjAut_mem_frameStab h

theorem okC_graph (C A : GL (Fin 3) K)
    (h : ((C⁻¹ * A * GeneralLinearGroup.inverseTranspose C : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K).IsDiag) :
    OkC C (LinearFlag.conjAut 3 K A * LinearFlag.dualAut 3 K) := by
  have : (LinearFlag.conjAut 3 K C)⁻¹ * (LinearFlag.conjAut 3 K A * LinearFlag.dualAut 3 K) *
      LinearFlag.conjAut 3 K C =
      LinearFlag.conjAut 3 K (C⁻¹ * A * GeneralLinearGroup.inverseTranspose C) *
        LinearFlag.dualAut 3 K := by
    rw [map_mul, map_mul, map_inv]
    calc _ = (LinearFlag.conjAut 3 K C)⁻¹ * LinearFlag.conjAut 3 K A *
          (LinearFlag.dualAut 3 K * LinearFlag.conjAut 3 K C) := by simp only [mul_assoc]
      _ = _ := by rw [LinearFlag.dualAut_mul_conjAut]; simp only [mul_assoc]
  unfold OkC
  rw [this]
  exact mul_mem (conjAut_mem_frameStab h) dualAut_mem_frameStab

theorem okC_of_comm {C : GL (Fin 3) K} {x : MulAut (projectiveSL 3 K)}
    (h : x * LinearFlag.conjAut 3 K C = LinearFlag.conjAut 3 K C * x) (hx : x ∈ frameStab 3 K) :
    OkC C x := by
  unfold OkC
  rw [mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]
  exact hx

theorem ok_of_shapes {φ : K ≃+* K} (hφφ : φ * φ = 1) {D : Subgroup (MulAut (projectiveSL 3 K))}
    {C : GL (Fin 3) K} (hfD : LinearFlag.fieldAut 3 K φ ∈ D)
    (hshape : ∀ x ∈ D, (∃ A, x = LinearFlag.conjAut 3 K A) ∨
      (∃ A, x = LinearFlag.conjAut 3 K A * LinearFlag.dualAut 3 K) ∨
      (∃ A, x = LinearFlag.conjAut 3 K A * LinearFlag.fieldAut 3 K φ) ∨
      (∃ A, x = LinearFlag.conjAut 3 K A * LinearFlag.fieldAut 3 K φ * LinearFlag.dualAut 3 K))
    (h1 : ∀ x ∈ D, (∃ A, x = LinearFlag.conjAut 3 K A) → OkC C x)
    (hf : OkC C (LinearFlag.fieldAut 3 K φ))
    (hw : (∃ w ∈ D, ∃ A, w = LinearFlag.conjAut 3 K A * LinearFlag.dualAut 3 K) →
      ∃ w ∈ D, (∃ A, w = LinearFlag.conjAut 3 K A * LinearFlag.dualAut 3 K) ∧ OkC C w) :
    ∀ x ∈ D, OkC C x := by
  have hff : LinearFlag.fieldAut 3 K φ * LinearFlag.fieldAut 3 K φ = 1 := by
    rw [← map_mul, hφφ, map_one]
  have hδδ : LinearFlag.dualAut 3 K * LinearFlag.dualAut 3 K = 1 :=
    (LinearFlag.standard_automorphism_transport (K := K) (n := 3)).2.2.2.1
  have hii : ∀ y ∈ D, (∃ A, y = LinearFlag.conjAut 3 K A * LinearFlag.dualAut 3 K) → OkC C y := by
    rintro y hy ⟨A, rfl⟩
    obtain ⟨w, hwD, ⟨A', rfl⟩, hok⟩ := hw ⟨_, hy, A, rfl⟩
    have hyw : LinearFlag.conjAut 3 K A * LinearFlag.dualAut 3 K *
        (LinearFlag.conjAut 3 K A' * LinearFlag.dualAut 3 K) =
        LinearFlag.conjAut 3 K (A * GeneralLinearGroup.inverseTranspose A') := by
      calc _ = LinearFlag.conjAut 3 K A * (LinearFlag.dualAut 3 K * LinearFlag.conjAut 3 K A') *
            LinearFlag.dualAut 3 K := by simp only [mul_assoc]
        _ = LinearFlag.conjAut 3 K A * (LinearFlag.conjAut 3 K (GeneralLinearGroup.inverseTranspose A') *
            LinearFlag.dualAut 3 K) * LinearFlag.dualAut 3 K := by rw [LinearFlag.dualAut_mul_conjAut]
        _ = LinearFlag.conjAut 3 K A * LinearFlag.conjAut 3 K (GeneralLinearGroup.inverseTranspose A') *
            (LinearFlag.dualAut 3 K * LinearFlag.dualAut 3 K) := by simp only [mul_assoc]
        _ = _ := by rw [hδδ, mul_one, map_mul]
    have h2 : OkC C (LinearFlag.conjAut 3 K A * LinearFlag.dualAut 3 K *
        (LinearFlag.conjAut 3 K A' * LinearFlag.dualAut 3 K)) := by
      rw [hyw]
      exact h1 _ (by rw [← hyw]; exact mul_mem hy hwD) ⟨_, rfl⟩
    have e : LinearFlag.conjAut 3 K A * LinearFlag.dualAut 3 K =
        (LinearFlag.conjAut 3 K A * LinearFlag.dualAut 3 K *
          (LinearFlag.conjAut 3 K A' * LinearFlag.dualAut 3 K)) *
        (LinearFlag.conjAut 3 K A' * LinearFlag.dualAut 3 K)⁻¹ := by group
    rw [e]
    exact h2.mul hok.inv
  intro x hx
  rcases hshape x hx with ⟨A, rfl⟩ | ⟨A, rfl⟩ | ⟨A, rfl⟩ | ⟨A, rfl⟩
  · exact h1 _ hx ⟨A, rfl⟩
  · exact hii _ hx ⟨A, rfl⟩
  · have hxf : LinearFlag.conjAut 3 K A * LinearFlag.fieldAut 3 K φ * LinearFlag.fieldAut 3 K φ =
        LinearFlag.conjAut 3 K A := by rw [mul_assoc, hff, mul_one]
    have e : LinearFlag.conjAut 3 K A * LinearFlag.fieldAut 3 K φ =
        (LinearFlag.conjAut 3 K A * LinearFlag.fieldAut 3 K φ * LinearFlag.fieldAut 3 K φ) *
          (LinearFlag.fieldAut 3 K φ)⁻¹ := by group
    rw [e, hxf]
    exact (h1 _ (hxf ▸ mul_mem hx hfD) ⟨A, rfl⟩).mul hf.inv
  · have hxf : LinearFlag.conjAut 3 K A * LinearFlag.fieldAut 3 K φ * LinearFlag.dualAut 3 K *
        LinearFlag.fieldAut 3 K φ = LinearFlag.conjAut 3 K A * LinearFlag.dualAut 3 K := by
      calc _ = LinearFlag.conjAut 3 K A * LinearFlag.fieldAut 3 K φ *
            (LinearFlag.dualAut 3 K * LinearFlag.fieldAut 3 K φ) := by simp only [mul_assoc]
        _ = LinearFlag.conjAut 3 K A * LinearFlag.fieldAut 3 K φ *
            (LinearFlag.fieldAut 3 K φ * LinearFlag.dualAut 3 K) := by
          rw [LinearFlag.dualAut_mul_fieldAut]
        _ = LinearFlag.conjAut 3 K A * (LinearFlag.fieldAut 3 K φ * LinearFlag.fieldAut 3 K φ) *
            LinearFlag.dualAut 3 K := by simp only [mul_assoc]
        _ = _ := by rw [hff, mul_one]
    have e : LinearFlag.conjAut 3 K A * LinearFlag.fieldAut 3 K φ * LinearFlag.dualAut 3 K =
        (LinearFlag.conjAut 3 K A * LinearFlag.fieldAut 3 K φ * LinearFlag.dualAut 3 K *
          LinearFlag.fieldAut 3 K φ) * (LinearFlag.fieldAut 3 K φ)⁻¹ := by group
    rw [e, hxf]
    exact (hii _ (hxf ▸ mul_mem hx hfD) ⟨A, rfl⟩).mul hf.inv

end Ok

section Comm

variable {K : Type} [Field K] [Finite K]

theorem map_eq_of_comm_field {φ : K ≃+* K} (R : GL (Fin 3) K) (hRR : R * R = 1)
    (hc : LinearFlag.conjAut 3 K R * LinearFlag.fieldAut 3 K φ =
      LinearFlag.fieldAut 3 K φ * LinearFlag.conjAut 3 K R) :
    ((R : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map φ = (R : Matrix (Fin 3) (Fin 3) K) := by
  rw [LinearFlag.fieldAut_mul_conjAut] at hc
  have h1 : LinearFlag.conjAut 3 K R = LinearFlag.conjAut 3 K (GeneralLinearGroup.map (φ : K →+* K) R) :=
    mul_right_cancel hc
  obtain ⟨c, -, hc'⟩ := scalar_of_conjAut_eq _ _ h1
  have hRm : (R : Matrix (Fin 3) (Fin 3) K) * R = 1 := by
    have := congrArg Units.val hRR
    simpa using this
  have hc1 : c = 1 := eq_one_of_map_eq_smul (φ := φ) _ hRm hc'
  rw [hc1, one_smul] at hc'
  exact hc'

theorem map_eq_smul_of_comm_graph {φ : K ≃+* K} (A : GL (Fin 3) K)
    (hc : LinearFlag.conjAut 3 K A * LinearFlag.dualAut 3 K * LinearFlag.fieldAut 3 K φ =
      LinearFlag.fieldAut 3 K φ * (LinearFlag.conjAut 3 K A * LinearFlag.dualAut 3 K)) :
    ∃ lam : K, lam ≠ 0 ∧ (A : Matrix (Fin 3) (Fin 3) K).map φ = lam • (A : Matrix (Fin 3) (Fin 3) K) := by
  have h1 : LinearFlag.conjAut 3 K A * (LinearFlag.fieldAut 3 K φ * LinearFlag.dualAut 3 K) =
      LinearFlag.conjAut 3 K (GeneralLinearGroup.map (φ : K →+* K) A) *
        (LinearFlag.fieldAut 3 K φ * LinearFlag.dualAut 3 K) := by
    calc _ = LinearFlag.conjAut 3 K A * (LinearFlag.dualAut 3 K * LinearFlag.fieldAut 3 K φ) := by
          rw [LinearFlag.dualAut_mul_fieldAut]
      _ = LinearFlag.conjAut 3 K A * LinearFlag.dualAut 3 K * LinearFlag.fieldAut 3 K φ := by
          simp only [mul_assoc]
      _ = LinearFlag.fieldAut 3 K φ * (LinearFlag.conjAut 3 K A * LinearFlag.dualAut 3 K) := hc
      _ = (LinearFlag.fieldAut 3 K φ * LinearFlag.conjAut 3 K A) * LinearFlag.dualAut 3 K := by
          simp only [mul_assoc]
      _ = _ := by rw [LinearFlag.fieldAut_mul_conjAut]; simp only [mul_assoc]
  exact scalar_of_conjAut_eq _ _ (mul_right_cancel h1)

theorem sandwich_of_comm (R B : GL (Fin 3) K) (hRR : R * R = 1)
    (hc : LinearFlag.conjAut 3 K R * (LinearFlag.conjAut 3 K B * LinearFlag.dualAut 3 K) =
      LinearFlag.conjAut 3 K B * LinearFlag.dualAut 3 K * LinearFlag.conjAut 3 K R) :
    (R : Matrix (Fin 3) (Fin 3) K) * B * (R : Matrix (Fin 3) (Fin 3) K)ᵀ = B := by
  have h1 : LinearFlag.conjAut 3 K (R * B) * LinearFlag.dualAut 3 K =
      LinearFlag.conjAut 3 K (B * GeneralLinearGroup.inverseTranspose R) * LinearFlag.dualAut 3 K := by
    calc _ = LinearFlag.conjAut 3 K R * (LinearFlag.conjAut 3 K B * LinearFlag.dualAut 3 K) := by
          rw [map_mul]; simp only [mul_assoc]
      _ = LinearFlag.conjAut 3 K B * LinearFlag.dualAut 3 K * LinearFlag.conjAut 3 K R := hc
      _ = LinearFlag.conjAut 3 K B * (LinearFlag.dualAut 3 K * LinearFlag.conjAut 3 K R) := by
          simp only [mul_assoc]
      _ = _ := by rw [LinearFlag.dualAut_mul_conjAut, map_mul]; simp only [mul_assoc]
  obtain ⟨c, -, hcm⟩ := scalar_of_conjAut_eq _ _ (mul_right_cancel h1).symm
  have hRm : (R : Matrix (Fin 3) (Fin 3) K) * R = 1 := by
    have := congrArg Units.val hRR
    simpa using this
  have hRi : ((R⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = R := by
    have : R⁻¹ = R := by
      rw [inv_eq_iff_mul_eq_one]; exact hRR
    rw [this]
  simp only [Units.val_mul, GeneralLinearGroup.coe_inverseTranspose, hRi] at hcm
  have hRt : (R : Matrix (Fin 3) (Fin 3) K)ᵀ * (R : Matrix (Fin 3) (Fin 3) K)ᵀ = 1 := by
    rw [← transpose_mul, hRm, transpose_one]
  have h2 : (R : Matrix (Fin 3) (Fin 3) K) * B * (R : Matrix (Fin 3) (Fin 3) K)ᵀ =
      c • (B : Matrix (Fin 3) (Fin 3) K) := by
    calc (R : Matrix (Fin 3) (Fin 3) K) * B * (R : Matrix (Fin 3) (Fin 3) K)ᵀ
        = (c • ((B : Matrix (Fin 3) (Fin 3) K) * (R : Matrix (Fin 3) (Fin 3) K)ᵀ)) *
            (R : Matrix (Fin 3) (Fin 3) K)ᵀ := by rw [hcm]
      _ = c • (B : Matrix (Fin 3) (Fin 3) K) := by
          rw [Matrix.smul_mul, Matrix.mul_assoc, hRt, Matrix.mul_one]
  have hc1 : c = 1 := eq_one_of_sandwich _ _ hRm (Matrix.isUnits_det_units B).ne_zero h2
  rw [h2, hc1, one_smul]

end Comm

section CaseF

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem mul_map_eq_one_of_map_eq_smul {φ : K ≃+* K} (hφ : ∀ x, φ (φ x) = x)
    (A : Matrix (Fin 3) (Fin 3) K) (hA : A.det ≠ 0) {lam : K} (h : A.map φ = lam • A) :
    lam * φ lam = 1 := by
  obtain ⟨i, j, hij⟩ : ∃ i j, A i j ≠ 0 := by
    by_contra! hc
    have hA0 : A = 0 := Matrix.ext fun i j => by simpa using hc i j
    exact hA (by rw [hA0]; simp)
  have h1 : φ (A i j) = lam * A i j := by
    have := congrFun (congrFun h i) j
    simpa using this
  have h2 : A i j = (φ lam * lam) * A i j := by
    calc A i j = φ (φ (A i j)) := (hφ _).symm
      _ = φ (lam * A i j) := by rw [h1]
      _ = φ lam * φ (A i j) := map_mul φ _ _
      _ = (φ lam * lam) * A i j := by rw [h1]; ring
  have h3 : (φ lam * lam - 1) * A i j = 0 := by linear_combination -h2
  have := sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right hij)
  rw [mul_comm]
  exact this

omit [Finite K] in
theorem isDiag_graph_of_congr (C B : GL (Fin 3) K)
    (hZ : ((C : Matrix (Fin 3) (Fin 3) K)ᵀ * ((B⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      (C : Matrix (Fin 3) (Fin 3) K)).IsDiag) :
    ((C⁻¹ * B * GeneralLinearGroup.inverseTranspose C : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K).IsDiag := by
  refine isDiag_of_mul_eq_one hZ ?_
  simp only [Units.val_mul, GeneralLinearGroup.coe_inverseTranspose]
  have h1 : ((C⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ * (C : Matrix (Fin 3) (Fin 3) K)ᵀ = 1 := by
    rw [← transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, transpose_one]
  have h2 : (B : Matrix (Fin 3) (Fin 3) K) * ((B⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h3 : ((C⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (C : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc _ = ((C⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * B *
        (((C⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ * (C : Matrix (Fin 3) (Fin 3) K)ᵀ) *
        ((B⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (C : Matrix (Fin 3) (Fin 3) K) := by
        simp only [Matrix.mul_assoc]
    _ = ((C⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((B : Matrix (Fin 3) (Fin 3) K) * ((B⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) *
        (C : Matrix (Fin 3) (Fin 3) K) := by rw [h1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h2, Matrix.mul_one, h3]

end CaseF

section CaseFMain

variable {K : Type} [Field K] [Finite K]

theorem good_of_field_data {φ : K ≃+* K} (hφφ : φ * φ = 1) (hK2 : ringChar K ≠ 2)
    {D : Subgroup (MulAut (projectiveSL 3 K))} (hD : CFSG.IsElementaryAbelian 2 ↥D)
    (hfD : LinearFlag.fieldAut 3 K φ ∈ D)
    (hshape : ∀ x ∈ D, (∃ A, x = LinearFlag.conjAut 3 K A) ∨
      (∃ A, x = LinearFlag.conjAut 3 K A * LinearFlag.dualAut 3 K) ∨
      (∃ A, x = LinearFlag.conjAut 3 K A * LinearFlag.fieldAut 3 K φ) ∨
      (∃ A, x = LinearFlag.conjAut 3 K A * LinearFlag.fieldAut 3 K φ * LinearFlag.dualAut 3 K)) :
    ∃ C : GL (Fin 3) K, ∀ x ∈ D, OkC C x := by
  classical
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK2
  have hφ : ∀ x, φ (φ x) = x := fun x => by
    have := congrArg (fun τ : K ≃+* K => τ x) hφφ
    simpa using this
  obtain ⟨hcomm, hsq⟩ := WeakSigGen.forall_of_isElementaryAbelian hD
  obtain ⟨E, ρ, hρsq, hρc, hρD, hρin, hρcomm⟩ := exists_lift_inner hK2 hD
  let L : Subfield K := (φ : K →+* K).eqLocusField (RingHom.id K)
  have hL : ∀ c : K, c ∈ L ↔ φ c = c := fun c => Iff.rfl
  have hρrat : ∀ (e : E) (i j : Fin 3),
      ((ρ e : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j ∈ L := by
    intro e i j
    have hcm := hcomm _ (hρD e) _ hfD
    rw [← hρc e] at hcm
    have := map_eq_of_comm_field (φ := φ) (ρ e) (hρsq e) hcm
    exact (hL _).2 (by simpa using congrFun (congrFun this i) j)
  have common : ∀ C : GL (Fin 3) K,
      (∀ i j, ((C : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j ∈ L) →
      (∀ e : E, ((C⁻¹ * ρ e * C : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag) →
      OkC C (LinearFlag.fieldAut 3 K φ) ∧
        ∀ x ∈ D, (∃ A, x = LinearFlag.conjAut 3 K A) → OkC C x := by
    intro C hCL hCd
    refine ⟨?_, ?_⟩
    · have hCr : GeneralLinearGroup.map (φ : K →+* K) C = C := by
        apply Units.ext
        ext i j
        exact (hL _).1 (hCL i j)
      refine okC_of_comm ?_ (fieldAut_mem_frameStab φ)
      rw [LinearFlag.fieldAut_mul_conjAut, hCr]
    · intro x hx hxA
      obtain ⟨e, he⟩ := hρin x hx hxA
      rw [he, ← hρc e]
      exact okC_conjAut C _ (hCd e)
  by_cases hw : ∃ w ∈ D, ∃ A, w = LinearFlag.conjAut 3 K A * LinearFlag.dualAut 3 K
  · obtain ⟨w, hwD, A, rfl⟩ := hw
    have hAsq : (LinearFlag.conjAut 3 K A * LinearFlag.dualAut 3 K) ^ 2 = 1 := by
      rw [sq]; exact hsq _ hwD
    have hAs := transpose_eq_of_sq h2 A hAsq
    obtain ⟨lam, -, hlam⟩ := map_eq_smul_of_comm_graph (φ := φ) A (hcomm _ hwD _ hfD)
    have hAdet : (A : Matrix (Fin 3) (Fin 3) K).det ≠ 0 := (Matrix.isUnits_det_units A).ne_zero
    obtain ⟨μ, hμ0, hμ⟩ : ∃ μ : K, μ ≠ 0 ∧
        (μ • (A : Matrix (Fin 3) (Fin 3) K)).map φ = μ • (A : Matrix (Fin 3) (Fin 3) K) := by
      by_cases hφ1 : φ = 1
      · refine ⟨1, one_ne_zero, ?_⟩
        subst hφ1
        ext i j
        simp
      · obtain ⟨μ, hμ0, hμ⟩ := exists_mu hφ hφ1 (mul_map_eq_one_of_map_eq_smul hφ _ hAdet hlam)
        refine ⟨μ, hμ0, ?_⟩
        ext i j
        have := congrFun (congrFun hlam i) j
        simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at this ⊢
        rw [map_mul, this, ← mul_assoc, hμ]
    set B : GL (Fin 3) K := A * GeneralLinearGroup.scalar (Fin 3) (Units.mk0 μ hμ0) with hBdef
    have hBm : (B : Matrix (Fin 3) (Fin 3) K) = μ • (A : Matrix (Fin 3) (Fin 3) K) := by
      rw [hBdef, Units.val_mul]
      have hscal : ((GeneralLinearGroup.scalar (Fin 3) (Units.mk0 μ hμ0) : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) = μ • (1 : Matrix (Fin 3) (Fin 3) K) := by
        rw [smul_one_eq_diagonal]; rfl
      rw [hscal, Matrix.mul_smul, Matrix.mul_one]
    have hcB : LinearFlag.conjAut 3 K B = LinearFlag.conjAut 3 K A := by
      rw [hBdef, map_mul, LinearFlag.conjAut_scalar, mul_one]
    have hBs : (B : Matrix (Fin 3) (Fin 3) K)ᵀ = B := by rw [hBm, transpose_smul, hAs]
    have hBr : (B : Matrix (Fin 3) (Fin 3) K).map φ = B := by rw [hBm]; exact hμ
    have hBφ : GeneralLinearGroup.map (φ : K →+* K) B = B := Units.ext hBr
    set S : Matrix (Fin 3) (Fin 3) K := ((B⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hSdef
    have hSB : S * (B : Matrix (Fin 3) (Fin 3) K) = 1 := by
      rw [hSdef, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hBS : (B : Matrix (Fin 3) (Fin 3) K) * S = 1 := by
      rw [hSdef, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hSs : Sᵀ = S := by
      have h1 : Sᵀ * (B : Matrix (Fin 3) (Fin 3) K) = 1 := by
        have := congrArg Matrix.transpose hBS
        rw [transpose_mul, hBs, transpose_one] at this
        exact this
      calc Sᵀ = Sᵀ * (B * S) := by rw [hBS, Matrix.mul_one]
        _ = (Sᵀ * B) * S := by rw [Matrix.mul_assoc]
        _ = S := by rw [h1, Matrix.one_mul]
    have hSφ : S.map φ = S := by
      have : GeneralLinearGroup.map (φ : K →+* K) (B⁻¹) = B⁻¹ := by rw [map_inv, hBφ]
      exact congrArg (fun X : GL (Fin 3) K => (X : Matrix (Fin 3) (Fin 3) K)) this
    have hSL : ∀ i j, S i j ∈ L := fun i j => (hL _).2 (by simpa using congrFun (congrFun hSφ i) j)
    have hiso : ∀ e : E, ((ρ e : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ * S *
        ((ρ e : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = S := by
      intro e
      have hRR : (ρ e : GL (Fin 3) K) * ρ e = 1 := hρsq e
      have hRm : ((ρ e : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * ρ e = 1 := by
        simpa using congrArg Units.val hRR
      have hc : LinearFlag.conjAut 3 K (ρ e) *
          (LinearFlag.conjAut 3 K B * LinearFlag.dualAut 3 K) =
          LinearFlag.conjAut 3 K B * LinearFlag.dualAut 3 K * LinearFlag.conjAut 3 K (ρ e) := by
        rw [hcB, hρc e]
        exact hcomm _ (hρD e) _ hwD
      have hsand := sandwich_of_comm (ρ e) B hRR hc
      have h1 : (B : Matrix (Fin 3) (Fin 3) K) * ((ρ e : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ =
          ((ρ e : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * B := by
        calc (B : Matrix (Fin 3) (Fin 3) K) * ((ρ e : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ
            = (((ρ e : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * ρ e) * B *
                ((ρ e : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ := by rw [hRm, Matrix.one_mul]
          _ = ((ρ e : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
                (((ρ e : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * B *
                  ((ρ e : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ) := by
              simp only [Matrix.mul_assoc]
          _ = ((ρ e : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * B := by rw [hsand]
      calc ((ρ e : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ * S *
            ((ρ e : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
          = S * B * (((ρ e : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ * S *
            ((ρ e : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by rw [hSB, Matrix.one_mul]
        _ = S * (B * ((ρ e : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ) * S *
            ((ρ e : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by simp only [Matrix.mul_assoc]
        _ = S * (((ρ e : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * B) * S *
            ((ρ e : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by rw [h1]
        _ = S * ((ρ e : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (B * S) *
            ((ρ e : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by simp only [Matrix.mul_assoc]
        _ = S := by rw [hBS, Matrix.mul_one, Matrix.mul_assoc, hRm, Matrix.mul_one]
    obtain ⟨C, hCL, hCd, hCZ⟩ := GenLocL3NFLin.exists_orth_conj_diag_sub L h2 S hSs hSL
      (fun e : E => ρ e) hρrat hρcomm hρsq hiso
    obtain ⟨hf, h1⟩ := common C hCL hCd
    refine ⟨C, ok_of_shapes hφφ hfD hshape h1 hf ?_⟩
    intro _
    refine ⟨LinearFlag.conjAut 3 K A * LinearFlag.dualAut 3 K, hwD, ⟨A, rfl⟩, ?_⟩
    rw [← hcB]
    exact okC_graph C B (isDiag_graph_of_congr C B hCZ)
  · obtain ⟨C, hCL, hCd, -⟩ := GenLocL3NFLin.exists_orth_conj_diag_sub L h2
      (0 : Matrix (Fin 3) (Fin 3) K) (by simp) (fun i j => L.zero_mem)
      (fun e : E => ρ e) hρrat hρcomm hρsq (fun e => by simp)
    obtain ⟨hf, h1⟩ := common C hCL hCd
    exact ⟨C, ok_of_shapes hφφ hfD hshape h1 hf (fun h => absurd h hw)⟩

end CaseFMain

section CaseU

variable {K : Type} [Field K] [Finite K]

theorem map_det_of_mul_self_eq_one {F : Type} [Field F] (φ : F ≃+* F) (R : Matrix (Fin 3) (Fin 3) F)
    (hR : R * R = 1) : φ R.det = R.det := by
  have hdet : R.det * R.det = 1 := by rw [← det_mul, hR, det_one]
  rcases mul_self_eq_one_iff.mp hdet with h' | h'
  · rw [h', map_one]
  · rw [h', map_neg, map_one]

theorem eq_one_of_twist {F : Type} [Field F] (R N : Matrix (Fin 3) (Fin 3) F) (hR : R * R = 1)
    (hN : N * N = 1) (hdet : N.det = R.det) {lam : F} (h : N = lam • R) : lam = 1 := by
  have hl2 : lam * lam = 1 := by
    rw [h, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hR] at hN
    have := congrFun (congrFun hN 0) 0
    simpa using this
  have hd : R.det * R.det = 1 := by rw [← det_mul, hR, det_one]
  have hd0 : R.det ≠ 0 := by
    intro h0
    rw [h0] at hd
    simp at hd
  have h3 : lam ^ 3 = 1 := by
    have := congrArg Matrix.det h
    rw [det_smul, Fintype.card_fin, hdet] at this
    exact mul_right_cancel₀ hd0 (this.symm.trans (one_mul _).symm)
  calc lam = lam * (lam * lam) := by rw [hl2, mul_one]
    _ = lam ^ 3 := by ring
    _ = 1 := h3

theorem unitary_of_comm_tau {φ : K ≃+* K} (R : GL (Fin 3) K) (hRR : R * R = 1)
    (hc : LinearFlag.conjAut 3 K R * (LinearFlag.fieldAut 3 K φ * LinearFlag.dualAut 3 K) =
      (LinearFlag.fieldAut 3 K φ * LinearFlag.dualAut 3 K) * LinearFlag.conjAut 3 K R) :
    ((R : Matrix (Fin 3) (Fin 3) K).map φ)ᵀ = (R : Matrix (Fin 3) (Fin 3) K) := by
  have h1 : LinearFlag.conjAut 3 K R * (LinearFlag.fieldAut 3 K φ * LinearFlag.dualAut 3 K) =
      LinearFlag.conjAut 3 K (GeneralLinearGroup.map (φ : K →+* K)
        (GeneralLinearGroup.inverseTranspose R)) *
        (LinearFlag.fieldAut 3 K φ * LinearFlag.dualAut 3 K) := by
    calc _ = (LinearFlag.fieldAut 3 K φ * LinearFlag.dualAut 3 K) * LinearFlag.conjAut 3 K R := hc
      _ = LinearFlag.fieldAut 3 K φ * (LinearFlag.dualAut 3 K * LinearFlag.conjAut 3 K R) := by
          rw [mul_assoc]
      _ = LinearFlag.fieldAut 3 K φ * (LinearFlag.conjAut 3 K (GeneralLinearGroup.inverseTranspose R) *
          LinearFlag.dualAut 3 K) := by rw [LinearFlag.dualAut_mul_conjAut]
      _ = (LinearFlag.fieldAut 3 K φ * LinearFlag.conjAut 3 K (GeneralLinearGroup.inverseTranspose R)) *
          LinearFlag.dualAut 3 K := by rw [mul_assoc]
      _ = (LinearFlag.conjAut 3 K (GeneralLinearGroup.map (φ : K →+* K)
            (GeneralLinearGroup.inverseTranspose R)) * LinearFlag.fieldAut 3 K φ) *
          LinearFlag.dualAut 3 K := by rw [LinearFlag.fieldAut_mul_conjAut]
      _ = _ := by rw [mul_assoc]
  obtain ⟨c, -, hcm⟩ := scalar_of_conjAut_eq _ _ (mul_right_cancel h1)
  have hRm : (R : Matrix (Fin 3) (Fin 3) K) * R = 1 := by
    simpa using congrArg Units.val hRR
  have hRi : ((R⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = R := by
    have : R⁻¹ = R := by rw [inv_eq_iff_mul_eq_one]; exact hRR
    rw [this]
  have hN : ((R : Matrix (Fin 3) (Fin 3) K).map φ)ᵀ = c • (R : Matrix (Fin 3) (Fin 3) K) := by
    have h2 : (((GeneralLinearGroup.map (φ : K →+* K) (GeneralLinearGroup.inverseTranspose R) :
        GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) = (((R : Matrix (Fin 3) (Fin 3) K)ᵀ).map φ) := by
      show ((GeneralLinearGroup.inverseTranspose R : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map φ = _
      rw [GeneralLinearGroup.coe_inverseTranspose, hRi]
    rw [h2, transpose_map] at hcm
    exact hcm.symm.symm
  have hNN : ((R : Matrix (Fin 3) (Fin 3) K).map φ)ᵀ * ((R : Matrix (Fin 3) (Fin 3) K).map φ)ᵀ = 1 := by
    rw [← transpose_mul, ← Matrix.map_mul, hRm, Matrix.map_one _ (map_zero φ) (map_one φ),
      transpose_one]
  have hdet : ((R : Matrix (Fin 3) (Fin 3) K).map φ)ᵀ.det = (R : Matrix (Fin 3) (Fin 3) K).det := by
    have h4 : ((R : Matrix (Fin 3) (Fin 3) K).map φ).det = φ (R : Matrix (Fin 3) (Fin 3) K).det :=
      (RingHom.map_det (φ : K →+* K) _).symm
    rw [det_transpose, h4]
    exact map_det_of_mul_self_eq_one φ _ hRm
  have hc1 := eq_one_of_twist _ _ hRm hNN hdet hN
  rw [hN, hc1, one_smul]

end CaseU

section Conj

variable {K : Type} [Field K]

theorem map_inverseTranspose_eq_of_unitary {φ : K ≃+* K} (C : GL (Fin 3) K)
    (hC : ((C : Matrix (Fin 3) (Fin 3) K).map φ)ᵀ * (C : Matrix (Fin 3) (Fin 3) K) = 1) :
    GeneralLinearGroup.map (φ : K →+* K) (GeneralLinearGroup.inverseTranspose C) = C := by
  apply Units.ext
  show ((GeneralLinearGroup.inverseTranspose C : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map φ = C
  rw [GeneralLinearGroup.coe_inverseTranspose]
  set Cm : Matrix (Fin 3) (Fin 3) K := ((C : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  set Ci : Matrix (Fin 3) (Fin 3) K := ((C⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  have hCCi : Cm * Ci = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hYN : ((Ciᵀ).map φ) * ((Cm.map φ)ᵀ) = 1 := by
    rw [transpose_map, ← transpose_mul, ← Matrix.map_mul, hCCi,
      Matrix.map_one _ (map_zero φ) (map_one φ), transpose_one]
  calc (Ciᵀ).map φ = (Ciᵀ).map φ * ((Cm.map φ)ᵀ * Cm) := by rw [hC, Matrix.mul_one]
    _ = ((Ciᵀ).map φ * (Cm.map φ)ᵀ) * Cm := by rw [Matrix.mul_assoc]
    _ = Cm := by rw [hYN, Matrix.one_mul]

theorem conj_typeIII (H A : GL (Fin 3) K) (φ : K ≃+* K) :
    LinearFlag.conjAut 3 K H * (LinearFlag.conjAut 3 K A * LinearFlag.fieldAut 3 K φ) *
        (LinearFlag.conjAut 3 K H)⁻¹ =
      LinearFlag.conjAut 3 K (H * A * GeneralLinearGroup.map (φ : K →+* K) H⁻¹) *
        LinearFlag.fieldAut 3 K φ := by
  rw [map_mul, map_mul, ← map_inv]
  calc _ = LinearFlag.conjAut 3 K H * LinearFlag.conjAut 3 K A *
        (LinearFlag.fieldAut 3 K φ * LinearFlag.conjAut 3 K H⁻¹) := by simp only [mul_assoc]
    _ = _ := by rw [LinearFlag.fieldAut_mul_conjAut]; simp only [mul_assoc]

theorem good_of_conj {D : Subgroup (MulAut (projectiveSL 3 K))} (H : GL (Fin 3) K)
    (h : ∃ C : GL (Fin 3) K, ∀ x ∈ D.map (MulAut.conj (LinearFlag.conjAut 3 K H)⁻¹).toMonoidHom,
      OkC C x) : ∃ C : GL (Fin 3) K, ∀ x ∈ D, OkC C x := by
  obtain ⟨C, hC⟩ := h
  refine ⟨H * C, fun x hx => ?_⟩
  have h1 := hC _ ⟨x, hx, rfl⟩
  unfold OkC at h1 ⊢
  have hconj : (MulAut.conj (LinearFlag.conjAut 3 K H)⁻¹).toMonoidHom x =
      (LinearFlag.conjAut 3 K H)⁻¹ * x * LinearFlag.conjAut 3 K H := by
    simp
  rw [hconj] at h1
  have e : (LinearFlag.conjAut 3 K (H * C))⁻¹ * x * LinearFlag.conjAut 3 K (H * C) =
      (LinearFlag.conjAut 3 K C)⁻¹ * ((LinearFlag.conjAut 3 K H)⁻¹ * x * LinearFlag.conjAut 3 K H) *
        LinearFlag.conjAut 3 K C := by
    rw [map_mul]
    group
  rw [e]
  exact h1

end Conj

end GenLocL3NFAux

end CFSG.GH74.Generic.BProg.B2
