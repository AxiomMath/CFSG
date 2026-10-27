module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGOutZetaBDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5FrameType

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open TauCeti QuadraticMap CFSG.ClassicalInvolution
open scoped Matrix

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private theorem zetaBFrame_norm_eq (fr : NFrame Q (Fin 6) 1) (x : V) :
    Q x = fr.b.repr x ⬝ᵥ fr.b.repr x := by
  rw [fr.map_eq, one_mul, dotProduct]
  exact Finset.sum_congr rfl fun i _ => by ring

private theorem zetaBFrame_polar_eq (fr : NFrame Q (Fin 6) 1) (x y : V) :
    QuadraticMap.polar Q x y = 2 * (fr.b.repr x ⬝ᵥ fr.b.repr y) := by
  have key : ∀ i : Fin 6, (fr.b.repr (x + y)) i ^ 2 - (fr.b.repr x) i ^ 2 -
      (fr.b.repr y) i ^ 2 = 2 * ((fr.b.repr x) i * (fr.b.repr y) i) := by
    intro i
    rw [map_add, Finsupp.add_apply]
    ring
  have h1 : (∑ i, (fr.b.repr (x + y)) i ^ 2) - (∑ i, (fr.b.repr x) i ^ 2) =
      ∑ i, ((fr.b.repr (x + y)) i ^ 2 - (fr.b.repr x) i ^ 2) :=
    (Finset.sum_sub_distrib (fun i => (fr.b.repr (x + y)) i ^ 2)
      (fun i => (fr.b.repr x) i ^ 2)).symm
  have h2 : (∑ i, ((fr.b.repr (x + y)) i ^ 2 - (fr.b.repr x) i ^ 2)) -
      (∑ i, (fr.b.repr y) i ^ 2) =
      ∑ i, ((fr.b.repr (x + y)) i ^ 2 - (fr.b.repr x) i ^ 2 -
        (fr.b.repr y) i ^ 2) :=
    (Finset.sum_sub_distrib (fun i => (fr.b.repr (x + y)) i ^ 2 - (fr.b.repr x) i ^ 2)
      (fun i => (fr.b.repr y) i ^ 2)).symm
  calc QuadraticMap.polar Q x y
      = Q (x + y) - Q x - Q y := rfl
    _ = (∑ i, (fr.b.repr (x + y)) i ^ 2) - (∑ i, (fr.b.repr x) i ^ 2) -
        (∑ i, (fr.b.repr y) i ^ 2) := by
        rw [fr.map_eq (x + y), fr.map_eq x, fr.map_eq y, one_mul, one_mul, one_mul]
    _ = ∑ i, ((fr.b.repr (x + y)) i ^ 2 - (fr.b.repr x) i ^ 2 -
        (fr.b.repr y) i ^ 2) := by
        rw [h1, h2]
    _ = ∑ i, 2 * ((fr.b.repr x) i * (fr.b.repr y) i) :=
        Finset.sum_congr rfl fun i _ => key i
    _ = 2 * (fr.b.repr x ⬝ᵥ fr.b.repr y) := by
        rw [dotProduct, Finset.mul_sum]

private theorem zetaBFrame_polar_invariant (fr : NFrame Q (Fin 6) 1) (g : OGroup Q) (x y : V) :
    QuadraticMap.polar Q ((g : V ≃ₗ[ZMod 3] V) x) ((g : V ≃ₗ[ZMod 3] V) y) =
      QuadraticMap.polar Q x y := by
  rw [QuadraticMap.polar, QuadraticMap.polar, ← map_add (g : V ≃ₗ[ZMod 3] V)]
  simp only [QuadraticMap.map_app_of_mem_orthogonalGroup g.2]

private theorem zetaBFrame_dotProduct_invariant (fr : NFrame Q (Fin 6) 1) (g : OGroup Q)
    (x y : V) :
    fr.b.repr ((g : V ≃ₗ[ZMod 3] V) x) ⬝ᵥ fr.b.repr ((g : V ≃ₗ[ZMod 3] V) y) =
      fr.b.repr x ⬝ᵥ fr.b.repr y := by
  have h1 : (2 : ZMod 3) * (fr.b.repr ((g : V ≃ₗ[ZMod 3] V) x) ⬝ᵥ
      fr.b.repr ((g : V ≃ₗ[ZMod 3] V) y)) =
      (2 : ZMod 3) * (fr.b.repr x ⬝ᵥ fr.b.repr y) := by
    rw [← zetaBFrame_polar_eq fr ((g : V ≃ₗ[ZMod 3] V) x) ((g : V ≃ₗ[ZMod 3] V) y),
      zetaBFrame_polar_invariant fr g x y, zetaBFrame_polar_eq fr x y]
  exact mul_left_cancel₀ (by decide : (2 : ZMod 3) ≠ 0) h1

private theorem zetaBFrame_basis_dotProduct (fr : NFrame Q (Fin 6) 1) (i j : Fin 6) :
    fr.b.repr (fr.b i) ⬝ᵥ fr.b.repr (fr.b j) =
      (1 : Matrix (Fin 6) (Fin 6) (ZMod 3)) i j := by
  rw [dotProduct]
  simp only [Module.Basis.repr_self_apply]
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl, one_mul, Matrix.one_apply]
    by_cases h : i = j
    · rw [if_pos h.symm, if_pos h]
    · rw [if_neg (Ne.symm h), if_neg h]
  · intro k _ hki
    rw [if_neg (Ne.symm hki), zero_mul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

private theorem zetaBFrame_mul_transpose (fr : NFrame Q (Fin 6) 1) (g : OGroup Q) :
    LinearMap.toMatrix fr.b fr.b (g : V →ₗ[ZMod 3] V) *
      (LinearMap.toMatrix fr.b fr.b (g : V →ₗ[ZMod 3] V))ᵀ = 1 := by
  have hMtM : (LinearMap.toMatrix fr.b fr.b (g : V →ₗ[ZMod 3] V))ᵀ *
      LinearMap.toMatrix fr.b fr.b (g : V →ₗ[ZMod 3] V) = 1 := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.transpose_apply, LinearMap.toMatrix_apply]
    change (fr.b.repr ((g : V ≃ₗ[ZMod 3] V) (fr.b i)) ⬝ᵥ
      fr.b.repr ((g : V ≃ₗ[ZMod 3] V) (fr.b j))) = (1 : Matrix (Fin 6) (Fin 6) (ZMod 3)) i j
    rw [zetaBFrame_dotProduct_invariant, zetaBFrame_basis_dotProduct]
  exact (Matrix.mem_orthogonalGroup_iff (n := Fin 6) (R := ZMod 3)).mp
    ((Matrix.mem_orthogonalGroup_iff' (n := Fin 6) (R := ZMod 3)).mpr hMtM)

private theorem zetaBFrame_inv_eq_self_all : ∀ q : ZMod 3, q ≠ 0 → q⁻¹ = q := by
  decide +kernel

private theorem zetaBFrame_inv_eq_self (q : ZMod 3) (hq : q ≠ 0) : q⁻¹ = q :=
  zetaBFrame_inv_eq_self_all q hq

private theorem zetaBFrame_reflection_toMatrix (fr : NFrame Q (Fin 6) 1) {v : Fin 6 → ZMod 3}
    {vv : V} (hvv : fr.b.repr vv = v) [Invertible (Q vv)] :
    LinearMap.toMatrix fr.b fr.b
      ((TauCeti.QuadraticMap.reflectionOrthogonal Q vv : OGroup Q) : V →ₗ[ZMod 3] V) =
      zRefl v := by
  have hQne : Q vv ≠ 0 := (isUnit_of_invertible (Q vv)).ne_zero
  have hQvv : Q vv = v ⬝ᵥ v := by
    rw [zetaBFrame_norm_eq fr vv, hvv]
  have hqne : v ⬝ᵥ v ≠ 0 := by rw [← hQvv]; exact hQne
  have hvv' : fr.b.equivFun vv = v := by
    rw [Module.Basis.equivFun_apply]
    exact hvv
  ext i j
  rw [LinearMap.toMatrix_apply]
  change fr.b.repr (((TauCeti.QuadraticMap.reflectionOrthogonal Q vv : OGroup Q) :
    V ≃ₗ[ZMod 3] V) (fr.b j)) i = zRefl v i j
  have hpolar : QuadraticMap.polar Q vv (fr.b j) = 2 * v j := by
    rw [zetaBFrame_polar_eq fr vv (fr.b j), hvv, Module.Basis.repr_self,
      Finsupp.single_eq_pi_single, dotProduct_single]
    ring
  have hrefl : ((TauCeti.QuadraticMap.reflectionOrthogonal Q vv : OGroup Q) : V ≃ₗ[ZMod 3] V)
      (fr.b j) = fr.b j - ((2 * v j) * (v ⬝ᵥ v)⁻¹) • vv := by
    rw [coe_reflectionOrthogonal_eq_reflect,
      CFSG.ClassicalGroups.Orthogonal.reflect_apply hQne, div_eq_mul_inv]
    have hdiv : QuadraticMap.polar Q vv (fr.b j) * (Q vv)⁻¹ = (2 * v j) * (v ⬝ᵥ v)⁻¹ :=
      (congrArg (fun z => z * (Q vv)⁻¹) hpolar).trans
        (congrArg (fun z => (2 * v j) * z⁻¹) hQvv)
    exact congrArg (fun c => fr.b j - c • vv) hdiv
  rw [← Module.Basis.equivFun_apply, hrefl, map_sub, map_smul, Pi.sub_apply, Pi.smul_apply,
    Module.Basis.equivFun_self, hvv']
  rw [zRefl, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.vecMulVec_apply]
  rw [zetaBFrame_inv_eq_self (v ⬝ᵥ v) hqne]
  by_cases h : i = j
  · rw [if_pos h.symm, if_pos h]
    simp only [smul_eq_mul]
    ring <;> rfl
  · rw [if_neg (Ne.symm h), if_neg h]
    simp only [smul_eq_mul]
    ring <;> rfl

theorem zetaFrameHom_holds : ZetaFrameHom := by
  intro V _ _ _ Q hQ hdim hsgn
  obtain ⟨fr⟩ := exists_nframe_six hQ hdim hsgn
  let L : OGroup Q →* (V →ₗ[ZMod 3] V) :=
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom).comp
      (Subgroup.subtype (TauCeti.QuadraticMap.orthogonalGroup Q))
  let ι : OGroup Q →* Matrix (Fin 6) (Fin 6) (ZMod 3) :=
    (LinearMap.toMatrixAlgEquiv fr.b).toMonoidHom.comp L
  refine ⟨ι, ?_, ?_, ?_, ?_, ?_⟩
  · intro g h hgh
    change LinearMap.toMatrix fr.b fr.b (g : V →ₗ[ZMod 3] V) =
      LinearMap.toMatrix fr.b fr.b (h : V →ₗ[ZMod 3] V) at hgh
    exact Subtype.ext (LinearEquiv.toLinearMap_injective
      ((LinearMap.toMatrix fr.b fr.b).injective hgh))
  · intro g
    change LinearMap.toMatrix fr.b fr.b (g : V →ₗ[ZMod 3] V) *
      (LinearMap.toMatrix fr.b fr.b (g : V →ₗ[ZMod 3] V))ᵀ = 1
    exact zetaBFrame_mul_transpose fr g
  · change LinearMap.toMatrix fr.b fr.b ((piOrth Q : OGroup Q) : V →ₗ[ZMod 3] V) = -1
    have hlin : ((piOrth Q : OGroup Q) : V →ₗ[ZMod 3] V) = -LinearMap.id := by
      ext x
      rw [LinearMap.neg_apply, LinearMap.id_apply]
      exact coe_piOrth_apply x
    rw [hlin, map_neg, LinearMap.toMatrix_id]
  · exact (piOrth_mem_omegaGroup_iff hQ).mpr
      ⟨by rw [hdim]; decide, by rw [hdim, hsgn]; decide⟩
  · intro v hv
    let vv : V := fr.b.equivFun.symm v
    have hvv : fr.b.repr vv = v := by
      funext i
      rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    have hQvv : Q vv = v ⬝ᵥ v := by
      rw [zetaBFrame_norm_eq fr vv, hvv]
    have hQne : Q vv ≠ 0 := by rw [hQvv]; exact hv
    letI : Invertible (Q vv) := invertibleOfNonzero hQne
    refine ⟨TauCeti.QuadraticMap.reflectionOrthogonal Q vv, ?_, ?_⟩
    · change LinearMap.toMatrix fr.b fr.b
        ((TauCeti.QuadraticMap.reflectionOrthogonal Q vv : OGroup Q) : V →ₗ[ZMod 3] V) =
        zRefl v
      exact zetaBFrame_reflection_toMatrix fr hvv
    · rw [detSpinorNorm_reflectionOrthogonal]
      refine Prod.ext rfl ?_
      have hU : unitOfInvertible (Q vv) = Units.mk0 (v ⬝ᵥ v) hv := by
        apply Units.ext
        rw [val_unitOfInvertible, Units.val_mk0]
        exact hQvv
      exact congrArg squareClassHom hU

end CFSG.OddStandard.SmallF3.Omega
