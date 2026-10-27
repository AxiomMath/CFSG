module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftFieldAut
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftFieldFrame
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaSL3LiftInnerElt

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftField

open Matrix CFSG.ComponentClassification.CatalogueBHigherLinearAction
  CFSG.ComponentClassification.CatalogueBHigherLinearField
  CFSG.LocalAnalysis.RankThreeTheoremC.SL3Lift

variable {k : Type} [Field k]

theorem exists_scalar_of_conj_eq_aux (g₁ g₂ : GL (Fin 3) k)
    (h : ∀ s : Matrix.SpecialLinearGroup (Fin 3) k,
      g₁ * Matrix.SpecialLinearGroup.toGL s * g₁⁻¹ =
        g₂ * Matrix.SpecialLinearGroup.toGL s * g₂⁻¹) :
    ∃ c : kˣ, g₂ = g₁ * GeneralLinearGroup.scalar (Fin 3) c := by
  have hc : ∀ s : Matrix.SpecialLinearGroup (Fin 3) k,
      ((g₁⁻¹ * g₂ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) * (s : Matrix (Fin 3) (Fin 3) k) =
        (s : Matrix (Fin 3) (Fin 3) k) *
          ((g₁⁻¹ * g₂ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) := by
    intro s
    have h1 : g₁⁻¹ * g₂ * Matrix.SpecialLinearGroup.toGL s =
        Matrix.SpecialLinearGroup.toGL s * (g₁⁻¹ * g₂) := by
      calc g₁⁻¹ * g₂ * Matrix.SpecialLinearGroup.toGL s
          = g₁⁻¹ * (g₂ * Matrix.SpecialLinearGroup.toGL s * g₂⁻¹) * g₂ := by group
        _ = g₁⁻¹ * (g₁ * Matrix.SpecialLinearGroup.toGL s * g₁⁻¹) * g₂ := by rw [h s]
        _ = Matrix.SpecialLinearGroup.toGL s * (g₁⁻¹ * g₂) := by group
    exact congrArg Units.val h1
  obtain ⟨c, hc'⟩ := eq_scalar_of_forall_commute (g₁⁻¹ * g₂) hc
  refine ⟨c, ?_⟩
  have h2 : g₁⁻¹ * g₂ = GeneralLinearGroup.scalar (Fin 3) c := by
    apply Units.ext
    rw [hc', GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  rw [← h2]
  group

theorem SemiBy.eq_mul_scalar {ζ : MulAut (Matrix.SpecialLinearGroup (Fin 3) k)} {τ : k ≃+* k}
    {g g' : GL (Fin 3) k} (h : SemiBy ζ τ g) (h' : SemiBy ζ τ g') :
    ∃ c : kˣ, g' = g * GeneralLinearGroup.scalar (Fin 3) c := by
  apply exists_scalar_of_conj_eq_aux
  intro t
  obtain ⟨s, rfl⟩ := (slFieldAut (Fin 3) k τ).surjective t
  have e : Matrix.SpecialLinearGroup.toGL (slFieldAut (Fin 3) k τ s) =
      Matrix.GeneralLinearGroup.map (τ : k →+* k) (Matrix.SpecialLinearGroup.toGL s) :=
    toGL_slFieldEquiv (Fin 3) τ s
  rw [e, ← h s, ← h' s]

theorem isConjBy_iff {σ : MulAut (Matrix.SpecialLinearGroup (Fin 3) k)} {g : GL (Fin 3) k} :
    IsConjBy σ g ↔ σ = slConjugation 3 k g := by
  constructor
  · intro h
    ext1 t
    apply Subtype.ext
    rw [h t, slConjugation_matrix]
  · rintro rfl t
    exact slConjugation_matrix 3 k g t

theorem isConjBy_scalar_mul {σ : MulAut (Matrix.SpecialLinearGroup (Fin 3) k)}
    {g : GL (Fin 3) k} (h : IsConjBy σ g) (c : kˣ) :
    IsConjBy σ (GeneralLinearGroup.scalar (Fin 3) c * g) := by
  rw [isConjBy_iff] at h ⊢
  rw [h, map_mul, slConjugation_scalar, one_mul]

theorem isConjBy_apply_eq {σ : MulAut (Matrix.SpecialLinearGroup (Fin 3) k)}
    {s : Matrix.SpecialLinearGroup (Fin 3) k}
    (h : IsConjBy σ (Matrix.SpecialLinearGroup.toGL s)) (t : Matrix.SpecialLinearGroup (Fin 3) k) :
    σ t = s * t * s⁻¹ := by
  apply Subtype.ext
  rw [h t, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, ← map_inv]
  rfl

theorem GL_ne_zero (g : GL (Fin 3) k) : (g : Matrix (Fin 3) (Fin 3) k) ≠ 0 := fun h =>
  Matrix.GeneralLinearGroup.det_ne_zero g (by rw [h]; simp)

theorem commute_conj_of_commute_aux {R : Type*} [Ring R] {P Q M D T : R} (h1 : P * Q = 1)
    (h2 : Q * P = 1) (hD : Q * M * P = D) (hDT : D * T = T * D) :
    M * (P * T * Q) = (P * T * Q) * M := by
  have hM : M = P * D * Q := by
    rw [← hD]
    calc M = (P * Q) * M * (P * Q) := by rw [h1]; simp
      _ = P * (Q * M * P) * Q := by simp only [mul_assoc]
  have e1 : P * D * Q * (P * T * Q) = P * (D * T) * Q := by
    calc _ = P * D * (Q * P) * T * Q := by simp only [mul_assoc]
      _ = _ := by rw [h2, mul_one]; simp only [mul_assoc]
  have e2 : P * T * Q * (P * D * Q) = P * (T * D) * Q := by
    calc _ = P * T * (Q * P) * D * Q := by simp only [mul_assoc]
      _ = _ := by rw [h2, mul_one]; simp only [mul_assoc]
  rw [hM, e1, e2, hDT]

theorem slFieldAut_conj_transvection (τ : k ≃+* k) {P : GL (Fin 3) k}
    (hP : Matrix.GeneralLinearGroup.map (τ : k →+* k) P = P) {a b : Fin 3} (hab : a ≠ b) :
    slFieldAut (Fin 3) k τ (slConjugation 3 k P (Matrix.SpecialLinearGroup.transvection hab 1)) =
      slConjugation 3 k P (Matrix.SpecialLinearGroup.transvection hab 1) := by
  have hP1 : (P : Matrix (Fin 3) (Fin 3) k).map τ = (P : Matrix (Fin 3) (Fin 3) k) :=
    congrArg Units.val hP
  have hP2 : ((P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k).map τ =
      ((P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) := by
    have : Matrix.GeneralLinearGroup.map (τ : k →+* k) P⁻¹ = P⁻¹ := by rw [map_inv, hP]
    exact congrArg Units.val this
  have hT : ((Matrix.SpecialLinearGroup.transvection hab (1 : k) :
      Matrix.SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k).map τ =
        ((Matrix.SpecialLinearGroup.transvection hab (1 : k) :
          Matrix.SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) := by
    ext i j
    change τ ((1 + Matrix.single a b 1 : Matrix (Fin 3) (Fin 3) k) i j) =
      (1 + Matrix.single a b 1 : Matrix (Fin 3) (Fin 3) k) i j
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    by_cases hij : i = j <;> by_cases hc : a = i ∧ b = j <;> simp [hij, hc]
  apply Subtype.ext
  change ((slConjugation 3 k P (Matrix.SpecialLinearGroup.transvection hab 1) :
      Matrix.SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k).map τ = _
  rw [slConjugation_matrix, Matrix.map_mul, Matrix.map_mul, hP1, hP2, hT]

variable [Finite k]

theorem exists_fixed_conj (F : FrobData k) {β : MulAut (Matrix.SpecialLinearGroup (Fin 3) k)}
    {g : GL (Fin 3) k} (hg : IsConjBy β g)
    (hcomm : β * slFieldAut (Fin 3) k F.τ = slFieldAut (Fin 3) k F.τ * β) :
    ∃ y : GL (Fin 3) k, IsConjBy β y ∧
      ∀ i j, F.τ ((y : Matrix (Fin 3) (Fin 3) k) i j) = (y : Matrix (Fin 3) (Fin 3) k) i j := by
  have h1 : SemiBy (β * slFieldAut (Fin 3) k F.τ) F.τ g := by
    have := (semiBy_one_iff.2 hg).mul (semiBy_fieldAut F.τ)
    rwa [one_mul, map_one, mul_one] at this
  have h2 : SemiBy (slFieldAut (Fin 3) k F.τ * β) F.τ
      (Matrix.GeneralLinearGroup.map (F.τ : k →+* k) g) := by
    have := (semiBy_fieldAut F.τ).mul (semiBy_one_iff.2 hg)
    rwa [mul_one, one_mul] at this
  rw [hcomm] at h1
  obtain ⟨l, hl⟩ := h1.eq_mul_scalar h2
  have hl' : (g : Matrix (Fin 3) (Fin 3) k).map F.τ = (l : k) • (g : Matrix (Fin 3) (Fin 3) k) := by
    have := congrArg Units.val hl
    rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_eq_mul_diagonal] at this
    exact this
  obtain ⟨m, hm⟩ := F.exists_unit_smul_fixed _ (GL_ne_zero g) l hl'
  refine ⟨GeneralLinearGroup.scalar (Fin 3) m * g, isConjBy_scalar_mul hg m, fun i j => ?_⟩
  have hy : ((GeneralLinearGroup.scalar (Fin 3) m * g : GL (Fin 3) k) :
      Matrix (Fin 3) (Fin 3) k) = (m : k) • (g : Matrix (Fin 3) (Fin 3) k) := by
    rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_eq_diagonal_mul]
  rw [hy]
  exact congrFun (congrFun hm i) j

theorem exists_det_one_conj (F : FrobData k) (h3 : 3 ∣ Nat.card k - 1)
    {β : MulAut (Matrix.SpecialLinearGroup (Fin 3) k)} {y : GL (Fin 3) k} (hy : IsConjBy β y)
    (hyfix : ∀ i j, F.τ ((y : Matrix (Fin 3) (Fin 3) k) i j) =
      (y : Matrix (Fin 3) (Fin 3) k) i j) :
    ∃ (c : kˣ) (s : Matrix.SpecialLinearGroup (Fin 3) k),
      (c : k) ^ 3 = (y : Matrix (Fin 3) (Fin 3) k).det ∧
      (s : Matrix (Fin 3) (Fin 3) k) = (c : k)⁻¹ • (y : Matrix (Fin 3) (Fin 3) k) ∧
      ∀ t, β t = s * t * s⁻¹ := by
  obtain ⟨c, hc⟩ := F.exists_fixed_cube h3 y hyfix
  have hdet : ((c : k)⁻¹ • (y : Matrix (Fin 3) (Fin 3) k)).det = 1 := by
    rw [Matrix.det_smul, ← hc]
    have : (c : k) ≠ 0 := c.ne_zero
    simp [inv_pow, this]
  let s : Matrix.SpecialLinearGroup (Fin 3) k := ⟨(c : k)⁻¹ • (y : Matrix (Fin 3) (Fin 3) k), hdet⟩
  refine ⟨c, s, hc, rfl, ?_⟩
  have h1 : Matrix.SpecialLinearGroup.toGL s = GeneralLinearGroup.scalar (Fin 3) c⁻¹ * y := by
    apply Units.ext
    rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_eq_diagonal_mul, Units.val_inv_eq_inv_val]
    rfl
  exact isConjBy_apply_eq (h1 ▸ isConjBy_scalar_mul hy c⁻¹)

theorem closure_fixed_eq_top_semi (F : FrobData k)
    {β : MulAut (Matrix.SpecialLinearGroup (Fin 3) k)} {y : GL (Fin 3) k} (hβ : IsConjBy β y)
    {P : GL (Fin 3) k} {u : Fin 3 → k}
    (hP : Matrix.GeneralLinearGroup.map (F.τ : k →+* k) P = P)
    (hPu : ((P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) * (y : Matrix (Fin 3) (Fin 3) k) *
      (P : Matrix (Fin 3) (Fin 3) k) = Matrix.diagonal u) :
    Subgroup.closure {x : Matrix.SpecialLinearGroup (Fin 3) k |
      slFieldAut (Fin 3) k F.τ x = x ∨ β x = x} = ⊤ := by
  apply eq_top_of_conj_transvection_diag P
  · intro a b hab
    exact Subgroup.subset_closure (Or.inl (slFieldAut_conj_transvection F.τ hP hab))
  · intro d hd
    refine Subgroup.subset_closure (Or.inr (hβ.fix ?_))
    rw [slConjugation_matrix]
    have hPQ : (P : Matrix (Fin 3) (Fin 3) k) * ((P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
        1 := Units.mul_inv P
    have hQP : ((P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) * (P : Matrix (Fin 3) (Fin 3) k) =
        1 := Units.inv_mul P
    refine commute_conj_of_commute_aux hPQ hQP hPu ?_
    change Matrix.diagonal u * Matrix.diagonal (fun i => (d i : k)) =
      Matrix.diagonal (fun i => (d i : k)) * Matrix.diagonal u
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    exact mul_comm _ _

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftField
