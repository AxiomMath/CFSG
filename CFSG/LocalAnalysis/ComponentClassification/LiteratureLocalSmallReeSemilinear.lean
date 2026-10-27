module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoCoordinateSemilinear
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear

public noncomputable section

namespace CFSG.ComponentClassification.LiteratureLocal

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo

variable (K : Type) [Field K]

open Classical in
@[expose] def semilinearFractional (α β γ δ : K) (σ : K ≃+* K) : Option K → Option K
  | none => if γ = 0 then none else some (α / γ)
  | some x => if γ * σ x + δ = 0 then none else some ((α * σ x + β) / (γ * σ x + δ))

theorem gl_smul_affine {α β γ δ : K} (M : GL (Fin 2) K) (hM : M.1 = !![α, β; γ, δ]) (x : K) :
    M • (![x, 1] : Fin 2 → K) = ![α * x + β, γ * x + δ] := by
  ext i
  fin_cases i <;> simp [Units.smul_def, hM, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem gl_smul_infinity {α β γ δ : K} (M : GL (Fin 2) K) (hM : M.1 = !![α, β; γ, δ]) :
    M • (![1, 0] : Fin 2 → K) = ![α, γ] := by
  ext i
  fin_cases i <;> simp [Units.smul_def, hM, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem mk_eq_infinity {y : K} (hy : y ≠ 0) (h : (![y, 0] : Fin 2 → K) ≠ 0) :
    Projectivization.mk K ![y, 0] h = psl2ProjectiveInfinity K := by
  rw [psl2ProjectiveInfinity, Projectivization.mk_eq_mk_iff]
  refine ⟨Units.mk0 y hy, ?_⟩
  ext i
  fin_cases i <;> simp [Units.smul_def]

theorem mk_eq_affine {y d : K} (hd : d ≠ 0) (h : (![y, d] : Fin 2 → K) ≠ 0) :
    Projectivization.mk K ![y, d] h = psl2AffinePoint K (y / d) := by
  rw [psl2AffinePoint, Projectivization.mk_eq_mk_iff]
  refine ⟨Units.mk0 d hd, ?_⟩
  ext i
  fin_cases i <;> simp [Units.smul_def, mul_div_cancel₀ _ hd]

theorem coordinatePGLAction_mk_some {α β γ δ : K} (M : GL (Fin 2) K)
    (hM : M.1 = !![α, β; γ, δ]) (x : K) :
    coordinatePGLAction K (Matrix.ProjGenLinGroup.mk M) (some x) =
      semilinearFractional K α β γ δ (RingEquiv.refl K) (some x) := by
  have hv : M • (![x, 1] : Fin 2 → K) ≠ 0 :=
    (smul_ne_zero_iff_ne M).2 (psl2AffineVector_ne_zero x)
  have hpt : coordinateEquiv K (coordinatePGLAction K (Matrix.ProjGenLinGroup.mk M) (some x)) =
      Projectivization.mk K (M • (![x, 1] : Fin 2 → K)) hv := by
    rw [coordinatePGLAction_point, coordinateEquiv_some, psl2AffinePoint,
      Projectivization.PGL.mk_smul_mk]
  simp only [semilinearFractional, RingEquiv.refl_apply]
  by_cases hd : γ * x + δ = 0
  · simp only [hd, ↓reduceIte]
    apply (coordinateEquiv K).injective
    rw [hpt, coordinateEquiv_none]
    have hy : α * x + β ≠ 0 := by
      intro hy
      apply hv
      rw [gl_smul_affine K M hM, hy, hd]
      ext i
      fin_cases i <;> rfl
    have h2 : (![α * x + β, 0] : Fin 2 → K) ≠ 0 := by
      intro h0
      exact hy (by simpa using congrFun h0 0)
    rw [← mk_eq_infinity K hy h2]
    congr 1
    rw [gl_smul_affine K M hM, hd]
  · simp only [hd, ↓reduceIte]
    apply (coordinateEquiv K).injective
    rw [hpt, coordinateEquiv_some]
    have h2 : (![α * x + β, γ * x + δ] : Fin 2 → K) ≠ 0 := by
      intro h0
      exact hd (by simpa using congrFun h0 1)
    rw [← mk_eq_affine K hd h2]
    congr 1
    rw [gl_smul_affine K M hM]

theorem coordinatePGLAction_mk_none {α β γ δ : K} (M : GL (Fin 2) K)
    (hM : M.1 = !![α, β; γ, δ]) :
    coordinatePGLAction K (Matrix.ProjGenLinGroup.mk M) none =
      semilinearFractional K α β γ δ (RingEquiv.refl K) none := by
  have hv : M • (![1, 0] : Fin 2 → K) ≠ 0 := (smul_ne_zero_iff_ne M).2 psl2_e0_ne_zero
  have hpt : coordinateEquiv K (coordinatePGLAction K (Matrix.ProjGenLinGroup.mk M) none) =
      Projectivization.mk K (M • (![1, 0] : Fin 2 → K)) hv := by
    rw [coordinatePGLAction_point, coordinateEquiv_none, psl2ProjectiveInfinity,
      Projectivization.PGL.mk_smul_mk]
  simp only [semilinearFractional]
  by_cases hc : γ = 0
  · simp only [hc, ↓reduceIte]
    apply (coordinateEquiv K).injective
    rw [hpt, coordinateEquiv_none]
    have hy : α ≠ 0 := by
      intro hy
      apply hv
      rw [gl_smul_infinity K M hM, hy, hc]
      ext i
      fin_cases i <;> rfl
    have h2 : (![α, 0] : Fin 2 → K) ≠ 0 := by
      intro h0
      exact hy (by simpa using congrFun h0 0)
    rw [← mk_eq_infinity K hy h2]
    congr 1
    rw [gl_smul_infinity K M hM, hc]
  · simp only [hc, ↓reduceIte]
    apply (coordinateEquiv K).injective
    rw [hpt, coordinateEquiv_some]
    have h2 : (![α, γ] : Fin 2 → K) ≠ 0 := by
      intro h0
      exact hc (by simpa using congrFun h0 1)
    rw [← mk_eq_affine K hc h2]
    congr 1
    rw [gl_smul_infinity K M hM]

variable [Finite K]

theorem coordinateSemilinearAction_inl_mul_inr {α β γ δ : K} (M : GL (Fin 2) K)
    (hM : M.1 = !![α, β; γ, δ]) (σ : K ≃+* K) :
    ⇑(coordinateSemilinearAction K
        (SemidirectProduct.inl (Matrix.ProjGenLinGroup.mk M) * SemidirectProduct.inr σ)) =
      semilinearFractional K α β γ δ σ := by
  funext x
  rw [map_mul, Equiv.Perm.mul_apply, coordinateSemilinearAction_inl,
    coordinateSemilinearAction_inr]
  cases x with
  | none =>
    rw [fieldExtension_none, coordinatePGLAction_mk_none K M hM]
    rfl
  | some x =>
    rw [fieldExtension_some, coordinatePGLAction_mk_some K M hM]
    rfl

theorem coe_coordinateE_eq :
    (coordinateE K : Set (Equiv.Perm (Option K))) =
      {f : Equiv.Perm (Option K) | ∃ α β γ δ : K, ∃ σ : K ≃+* K, α * δ - β * γ ≠ 0 ∧
        ⇑f = semilinearFractional K α β γ δ σ} := by
  ext f
  constructor
  · intro hf
    rw [SetLike.mem_coe, ← coordinateSemilinearAction_range_eq_E] at hf
    obtain ⟨p, rfl⟩ := hf
    obtain ⟨M, hM⟩ := Matrix.ProjGenLinGroup.mk_surjective p.left
    have hMe : M.1 = !![M.1 0 0, M.1 0 1; M.1 1 0, M.1 1 1] := (Matrix.eta_fin_two _)
    refine ⟨M.1 0 0, M.1 0 1, M.1 1 0, M.1 1 1, p.right, ?_, ?_⟩
    · have hdet : (M.1).det ≠ 0 := (M.isUnit.map Matrix.detMonoidHom).ne_zero
      rwa [Matrix.det_fin_two] at hdet
    · rw [← SemidirectProduct.inl_left_mul_inr_right p, ← hM]
      exact coordinateSemilinearAction_inl_mul_inr K M hMe p.right
  · rintro ⟨α, β, γ, δ, σ, hdet, hf⟩
    have hA : (!![α, β; γ, δ] : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
      rwa [Matrix.det_fin_two_of]
    set M : GL (Fin 2) K := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hA with hMdef
    rw [SetLike.mem_coe, ← coordinateSemilinearAction_range_eq_E]
    refine ⟨SemidirectProduct.inl (Matrix.ProjGenLinGroup.mk M) * SemidirectProduct.inr σ, ?_⟩
    apply DFunLike.coe_injective
    rw [coordinateSemilinearAction_inl_mul_inr K M rfl, hf]

@[expose] def semilinearFractionalGroup : Subgroup (Equiv.Perm (Option K)) :=
  (coordinateE K).copy
    {f : Equiv.Perm (Option K) | ∃ α β γ δ : K, ∃ σ : K ≃+* K, α * δ - β * γ ≠ 0 ∧
      ⇑f = semilinearFractional K α β γ δ σ}
    (coe_coordinateE_eq K).symm

theorem mem_semilinearFractionalGroup {f : Equiv.Perm (Option K)} :
    f ∈ semilinearFractionalGroup K ↔ ∃ α β γ δ : K, ∃ σ : K ≃+* K, α * δ - β * γ ≠ 0 ∧
      ⇑f = semilinearFractional K α β γ δ σ :=
  Iff.rfl

theorem semilinearFractionalGroup_eq : semilinearFractionalGroup K = coordinateE K :=
  Subgroup.copy_eq _ _ _

@[expose] def pGammaL2EquivSemilinearFractional :
    PGammaL2 K ≃* semilinearFractionalGroup K :=
  (semilinearEquivCoordinateE K).trans
    (MulEquiv.subgroupCongr (semilinearFractionalGroup_eq K).symm)

@[expose] def mulAutPSL2EquivSemilinearFractional :
    MulAut (PSL2 K) ≃* semilinearFractionalGroup K :=
  (semilinearEquivAut K).symm.trans (pGammaL2EquivSemilinearFractional K)

theorem card_semilinearFractionalGroup {p n : ℕ} (hp : p.Prime) (hK : Nat.card K = p ^ n) :
    Nat.card (semilinearFractionalGroup K) = Nat.card K * (Nat.card K ^ 2 - 1) * n := by
  rw [← Nat.card_congr (pGammaL2EquivSemilinearFractional K).toEquiv, SemidirectProduct.card,
    pgl2_card_formula, (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hp K hK).1]

end CFSG.ComponentClassification.LiteratureLocal
