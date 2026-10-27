module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PslHb
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeModel
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeSpecial

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open Polynomial Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne CFSG.RankThree.CentralLift

section Scalar

variable {E W : Type*} [Field E] [AddCommGroup W] [Module E W]

@[expose] noncomputable def t6psuh_scalar (δ : Eˣ) : LinearMap.GeneralLinearGroup E W :=
  Units.map (algebraMap E (Module.End E W) : E →* Module.End E W) δ

theorem t6psuh_scalar_apply (δ : Eˣ) (w : W) :
    ((t6psuh_scalar δ : LinearMap.GeneralLinearGroup E W) : Module.End E W) w = (δ : E) • w := by
  simp [t6psuh_scalar, Module.algebraMap_end_apply]

theorem t6psuh_scalar_comm (δ : Eˣ) (g : LinearMap.GeneralLinearGroup E W) :
    t6psuh_scalar δ * g = g * t6psuh_scalar δ := by
  apply Units.ext
  simp only [Units.val_mul, t6psuh_scalar, Units.coe_map, MonoidHom.coe_coe]
  exact Algebra.commutes (δ : E) (g : Module.End E W)

theorem t6psuh_det_scalar [FiniteDimensional E W] (δ : Eˣ) :
    LinearMap.det ((t6psuh_scalar δ : LinearMap.GeneralLinearGroup E W) : Module.End E W) =
      (δ : E) ^ Module.finrank E W := by
  have : ((t6psuh_scalar δ : LinearMap.GeneralLinearGroup E W) : Module.End E W) =
      (δ : E) • LinearMap.id := LinearMap.ext fun w => t6psuh_scalar_apply δ w
  rw [this, LinearMap.det_smul, LinearMap.det_id, mul_one]

end Scalar

section NormDet

variable {ℓ f : ℕ} {E : Type} [Field E]

theorem t6psuh_norm_det (hE : UnitaryFieldData ℓ f E) {W : Type*} [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] {Hf : W →ₛₗ[hE.bar] W →ₗ[E] E} (hHf : Hf.IsSymm)
    (hHfl : Hf.SeparatingLeft) {γ : LinearMap.GeneralLinearGroup E W}
    (hγ : γ ∈ sesqUnitaryGroup Hf) :
    hE.bar (LinearMap.det (γ : Module.End E W)) * LinearMap.det (γ : Module.End E W) = 1 := by
  obtain ⟨e, he⟩ := hE.exists_orthonormal_basis hHf hHfl
  have heG : ∀ i j, Hf (e i) (e j) =
      (1 : Matrix (Fin (Module.finrank E W)) (Fin (Module.finrank E W)) E) i j :=
    fun i j => by rw [he i j, Matrix.one_apply]
  set M := LinearMap.toMatrix e e (γ : Module.End E W) with hMdef
  have hMu : ∀ y : W, e.equivFun (((γ : LinearMap.GeneralLinearGroup E W) : W →ₗ[E] W) y) =
      M.mulVec (e.equivFun y) := by
    intro y
    rw [Module.Basis.equivFun_apply, Module.Basis.equivFun_apply]
    exact (LinearMap.toMatrix_mulVec_repr e e (γ : Module.End E W) y).symm
  have hiso : ∀ u v, gramForm hE (1 : Matrix (Fin (Module.finrank E W))
      (Fin (Module.finrank E W)) E) (M.mulVec u) (M.mulVec v) = gramForm hE 1 u v := by
    intro u v
    have h1 := hγ (e.equivFun.symm u) (e.equivFun.symm v)
    rw [form_eq_gramForm hE e heG, form_eq_gramForm hE e heG, hMu, hMu,
      LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h1
    exact h1
  have hM : (M.map hE.bar)ᵀ * 1 * M = 1 := (gramForm_isometry_iff hE 1 M).mp hiso
  have hdet := congrArg Matrix.det hM
  have hb : (M.map hE.bar).det = hE.bar M.det := by rw [RingHom.map_det]; rfl
  rw [Matrix.mul_one, Matrix.det_mul, Matrix.det_transpose, hb, Matrix.det_one] at hdet
  rw [← LinearMap.det_toMatrix e (γ : Module.End E W)]
  exact hdet

end NormDet

section Model

universe u

variable {ℓ f : ℕ} {K : Type} [Field K] {hK : UnitaryFieldData ℓ f K} {V : Type u}
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] {B : V →ₛₗ[hK.bar] V →ₗ[K] K}
  {x : LinearMap.GeneralLinearGroup K V}

theorem t6psuh_exists_model (H : UnitaryPrimaryData hK.bar B x)
    (b : primaryFactors (x : Module.End K V)) :
    ∃ (Ω : Subgroup (blockGL (x : Module.End K V) (b : K[X])))
      (φ : ↥(orbitFactor B x (b : K[X])) ≃* ↥Ω),
      (∀ s : ↥(orbitFactor B x (b : K[X])), (φ s : blockGL (x : Module.End K V) (b : K[X])) =
        blockRestrict x (b : K[X]) ⟨s.1, orbitFactor_le_gl_centralizer s.2⟩) ∧
      (∀ γ ∈ Ω, t6psuh_scalar (blockGLDet (x : Module.End K V) (b : K[X]) γ) ∈ Ω) := by
  by_cases hself : dualPoly hK.bar (b : K[X]) = b
  · obtain ⟨hE, Hf, hHf, hHfl, φ, hφ, -⟩ :=
      exists_selfDualFactor hself (selfDualPrimaryBlock H b hself)
    refine ⟨sesqUnitaryGroup Hf, φ, fun s => blockGL_ext fun v hv => hφ s v hv, fun γ hγ => ?_⟩
    have hn := t6psuh_norm_det hE hHf hHfl hγ
    intro w w'
    have hδ : (((blockGLDet (x : Module.End K V) (b : K[X]) γ : (AdjoinRoot (b : K[X]))ˣ)) :
        AdjoinRoot (b : K[X])) = LinearMap.det (γ : Module.End (AdjoinRoot (b : K[X]))
          (primaryComponent (x : Module.End K V) (b : K[X]))) := rfl
    rw [t6psuh_scalar_apply, t6psuh_scalar_apply]
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [hδ]
    linear_combination (Hf w w') * hn
  · obtain ⟨φ, hφ, -⟩ := exists_pairedFactor (pairedPrimaryBlock H b (Ne.symm hself))
    exact ⟨⊤, φ.trans Subgroup.topEquiv.symm, fun s => blockGL_ext fun v hv => hφ s v hv,
      fun γ _ => Subgroup.mem_top _⟩


theorem t6psuh_sq_mem (H : UnitaryPrimaryData hK.bar B x)
    (b : primaryFactors (x : Module.End K V))
    (hm2 : primaryMultiplicity (x : Module.End K V) (b : K[X]) = 2)
    {g : LinearMap.GeneralLinearGroup K V} (hg : g ∈ orbitFactor B x (b : K[X])) :
    ∃ n ∈ specialBlock B x (b : K[X]), ∃ z ∈ orbitFactor B x (b : K[X]),
      (∀ m ∈ orbitFactor B x (b : K[X]), z * m = m * z) ∧ g ^ 2 = n * z := by
  obtain ⟨Ω, φ, hcompat, hscalar⟩ := t6psuh_exists_model H b
  let s : ↥(orbitFactor B x (b : K[X])) := ⟨g, hg⟩
  let γ : blockGL (x : Module.End K V) (b : K[X]) := (φ s : blockGL (x : Module.End K V) (b : K[X]))
  let δ : (AdjoinRoot (b : K[X]))ˣ := blockGLDet (x : Module.End K V) (b : K[X]) γ
  let z0 : ↥Ω := ⟨t6psuh_scalar δ, hscalar γ (φ s).2⟩
  let z : ↥(orbitFactor B x (b : K[X])) := φ.symm z0
  let n : ↥(orbitFactor B x (b : K[X])) := s ^ 2 * z⁻¹
  have hφz : φ z = z0 := MulEquiv.apply_symm_apply φ z0
  have hzc : ∀ m : ↥(orbitFactor B x (b : K[X])), z * m = m * z := by
    intro m
    apply φ.injective
    apply Subtype.ext
    rw [map_mul, map_mul, hφz, Subgroup.coe_mul, Subgroup.coe_mul]
    exact t6psuh_scalar_comm δ _
  have hdz : blockGLDet (x : Module.End K V) (b : K[X]) (t6psuh_scalar δ) = δ ^ 2 := by
    apply Units.ext
    have hd := t6psuh_det_scalar (E := AdjoinRoot (b : K[X]))
      (W := primaryComponent (x : Module.End K V) (b : K[X])) δ
    rw [show Module.finrank (AdjoinRoot (b : K[X]))
      (primaryComponent (x : Module.End K V) (b : K[X])) = 2 from hm2] at hd
    exact hd
  refine ⟨n.1, ?_, z.1, z.2, fun m hm => congrArg Subtype.val (hzc ⟨m, hm⟩), ?_⟩
  · refine mem_specialBlock.mpr ⟨n.2, orbitFactor_le_gl_centralizer n.2, ?_⟩
    have h1 : blockDetHom x (b : K[X]) ⟨n.1, orbitFactor_le_gl_centralizer n.2⟩ =
        blockGLDet (x : Module.End K V) (b : K[X])
          (φ n : blockGL (x : Module.End K V) (b : K[X])) := by
      show blockGLDet (x : Module.End K V) (b : K[X])
        (blockRestrict x (b : K[X]) ⟨n.1, orbitFactor_le_gl_centralizer n.2⟩) = _
      rw [hcompat n]
    rw [h1]
    have h2 : (φ n : blockGL (x : Module.End K V) (b : K[X])) = γ ^ 2 * (t6psuh_scalar δ)⁻¹ := by
      show ((φ (s ^ 2 * z⁻¹) : ↥Ω) : blockGL (x : Module.End K V) (b : K[X])) = _
      rw [map_mul, map_pow, map_inv, hφz]
      rfl
    rw [h2, map_mul, map_pow, map_inv, hdz]
    show δ ^ 2 * (δ ^ 2)⁻¹ = 1
    exact mul_inv_cancel _
  · show g ^ 2 = ((s ^ 2 * z⁻¹ : ↥(orbitFactor B x (b : K[X]))) : LinearMap.GeneralLinearGroup K V) *
      (z : LinearMap.GeneralLinearGroup K V)
    rw [← Subgroup.coe_mul, inv_mul_cancel_right]
    rfl

end Model

end CFSG.HardMathSupport.Dickson.Sec6.I1431
