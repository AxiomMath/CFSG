module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieModelDefs
public import CFSG.GroupTheory.ABGLocalTools.SL2FieldAutPGammaL
public import CFSG.GroupTheory.ABGLocalTools.SL2FieldAutInner
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DeterminantSquare
public import CFSG.LocalAnalysis.ComponentInitial.ScalarSemilinearNormalizer

public section

namespace CFSG.ComponentClassification.RankTwoOddLie

open Matrix CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.ABGLocalTools
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem psl2MulAutOf_mul (α β : MulAut SL(2, F)) :
    psl2MulAutOf (α * β) = psl2MulAutOf α * psl2MulAutOf β := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H b => rfl

theorem psl2MulAutOf_one : psl2MulAutOf (1 : MulAut SL(2, F)) = 1 := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H b => rfl

@[expose] noncomputable def psl2MulAutHom : MulAut SL(2, F) →* MulAut (PSL2 F) where
  toFun := psl2MulAutOf
  map_one' := psl2MulAutOf_one
  map_mul' := psl2MulAutOf_mul

theorem psl2FieldAut_mul_pglAction (σ : F ≃+* F) (x : PGL2 F) :
    psl2FieldAut F σ * pglAction F x = pglAction F (pgl2FieldAut F σ x) * psl2FieldAut F σ := by
  have h := DFunLike.congr_fun (pglAction_fieldAut F σ) x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
  rw [h]
  group

theorem exists_eq_pglAction_mul_psl2FieldAut [Finite F] (γ : MulAut (PSL2 F)) :
    ∃ (g : PGL2 F) (σ : F ≃+* F), γ = pglAction F g * psl2FieldAut F σ := by
  obtain ⟨x, rfl⟩ := semilinearAction_surjective F γ
  refine ⟨x.left, x.right, ?_⟩
  conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right x]
  rw [map_mul, semilinearAction_inl, semilinearAction_inr]

theorem commutator_pglAction_mul_psl2FieldAut [Finite F] (g h : PGL2 F) (σ τ : F ≃+* F) :
    pglAction F g * psl2FieldAut F σ * (pglAction F h * psl2FieldAut F τ) *
        (pglAction F g * psl2FieldAut F σ)⁻¹ * (pglAction F h * psl2FieldAut F τ)⁻¹ =
      pglAction F (g * pgl2FieldAut F σ h * (pgl2FieldAut F τ g)⁻¹ * h⁻¹) := by
  have R2 : psl2FieldAut F σ * psl2FieldAut F τ = psl2FieldAut F τ * psl2FieldAut F σ := by
    rw [← map_mul, ← map_mul, CFSG.LocalAnalysis.ComponentInitial.ringAut_mul_comm F σ τ]
  calc pglAction F g * psl2FieldAut F σ * (pglAction F h * psl2FieldAut F τ) *
        (pglAction F g * psl2FieldAut F σ)⁻¹ * (pglAction F h * psl2FieldAut F τ)⁻¹ =
      pglAction F g * (psl2FieldAut F σ * pglAction F h) * psl2FieldAut F τ *
        (psl2FieldAut F σ)⁻¹ * (pglAction F g)⁻¹ * (psl2FieldAut F τ)⁻¹ *
          (pglAction F h)⁻¹ := by group
    _ = pglAction F g * pglAction F (pgl2FieldAut F σ h) *
        (psl2FieldAut F σ * psl2FieldAut F τ) * (psl2FieldAut F σ)⁻¹ * (pglAction F g)⁻¹ *
          (psl2FieldAut F τ)⁻¹ * (pglAction F h)⁻¹ := by
        rw [psl2FieldAut_mul_pglAction]
        group
    _ = pglAction F g * pglAction F (pgl2FieldAut F σ h) *
        (psl2FieldAut F τ * pglAction F g⁻¹) * (psl2FieldAut F τ)⁻¹ * (pglAction F h)⁻¹ := by
        rw [R2, map_inv]
        group
    _ = pglAction F (g * pgl2FieldAut F σ h * (pgl2FieldAut F τ g)⁻¹ * h⁻¹) := by
        rw [psl2FieldAut_mul_pglAction, map_inv (pgl2FieldAut F τ), map_mul, map_mul, map_mul,
          map_inv, map_inv]
        group

theorem isSquare_ringEquiv_mul_inv [Finite F] (hF : ringChar F ≠ 2) (σ : F ≃+* F) {x : F}
    (hx : x ≠ 0) : IsSquare (σ x * x⁻¹) := by
  have : Fintype F := Fintype.ofFinite F
  have hσx : σ x ≠ 0 := (map_ne_zero σ).mpr hx
  rw [FiniteField.isSquare_iff hF (mul_ne_zero hσx (inv_ne_zero hx)), mul_pow, inv_pow,
    ← map_pow]
  rcases FiniteField.pow_dichotomy hF hx with h | h <;> rw [h] <;> simp

theorem pgl2FieldAut_mk (σ : F ≃+* F) (H : GL (Fin 2) F) :
    pgl2FieldAut F σ (ProjGenLinGroup.mk H) =
      ProjGenLinGroup.mk (GeneralLinearGroup.map σ.toRingHom H) :=
  pgl2RingEquiv_mk σ H

theorem commutator_mem_range_toPGL [Finite F] (hF : ringChar F ≠ 2) (g h : PGL2 F)
    (σ τ : F ≃+* F) :
    g * pgl2FieldAut F σ h * (pgl2FieldAut F τ g)⁻¹ * h⁻¹ ∈
      (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
  obtain ⟨G, rfl⟩ := ProjGenLinGroup.mk_surjective g
  obtain ⟨H, rfl⟩ := ProjGenLinGroup.mk_surjective h
  have hw : ProjGenLinGroup.mk G * pgl2FieldAut F σ (ProjGenLinGroup.mk H) *
      (pgl2FieldAut F τ (ProjGenLinGroup.mk G))⁻¹ * (ProjGenLinGroup.mk H)⁻¹ =
      ProjGenLinGroup.mk (G * GeneralLinearGroup.map σ.toRingHom H *
        (GeneralLinearGroup.map τ.toRingHom G)⁻¹ * H⁻¹) := by
    rw [pgl2FieldAut_mk, pgl2FieldAut_mk, map_mul, map_mul, map_mul, map_inv, map_inv]
  rw [hw]
  refine (pgl2_mk_mem_psl2_range_iff_det_isSquare _).2 ?_
  have hdet : ∀ (ρ : F ≃+* F) (M : GL (Fin 2) F),
      ((GeneralLinearGroup.det (GeneralLinearGroup.map ρ.toRingHom M) : Fˣ) : F) =
        ρ ((GeneralLinearGroup.det M : Fˣ) : F) := fun ρ M => by
    rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.val_det_apply]
    change _ = ρ.toRingHom _
    rw [RingHom.map_det]
    rfl
  have hG : ((GeneralLinearGroup.det G : Fˣ) : F) ≠ 0 := Units.ne_zero _
  have hH : ((GeneralLinearGroup.det H : Fˣ) : F) ≠ 0 := Units.ne_zero _
  have e : ((GeneralLinearGroup.det (G * GeneralLinearGroup.map σ.toRingHom H *
      (GeneralLinearGroup.map τ.toRingHom G)⁻¹ * H⁻¹) : Fˣ) : F) =
      (σ ((GeneralLinearGroup.det H : Fˣ) : F) * ((GeneralLinearGroup.det H : Fˣ) : F)⁻¹) *
        (τ ((GeneralLinearGroup.det G : Fˣ) : F) * ((GeneralLinearGroup.det G : Fˣ) : F)⁻¹)⁻¹ := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, Units.val_mul, Units.val_mul, Units.val_mul,
      Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, hdet, hdet]
    have hτG : τ ((GeneralLinearGroup.det G : Fˣ) : F) ≠ 0 := (map_ne_zero τ).mpr hG
    field_simp
  change IsSquare ((GeneralLinearGroup.det _ : Fˣ) : F)
  rw [e]
  exact (isSquare_ringEquiv_mul_inv hF σ hH).mul (isSquare_ringEquiv_mul_inv hF τ hG).inv

theorem sl2OuterComm : SL2OuterComm := by
  intro F _ _ hodd α β
  have hF : ringChar F ≠ 2 := ringChar_ne_two_of_odd_card hodd
  obtain ⟨g, σ, hα⟩ := exists_eq_pglAction_mul_psl2FieldAut (psl2MulAutOf α)
  obtain ⟨h, τ, hβ⟩ := exists_eq_pglAction_mul_psl2FieldAut (psl2MulAutOf β)
  obtain ⟨x, hx⟩ := commutator_mem_range_toPGL hF g h σ τ
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  refine ⟨y, eq_conj_of_inv_mul_conj_mem_center hF _ y fun b => ?_⟩
  have hcomm : psl2MulAutOf (α * β * α⁻¹ * β⁻¹) = MulAut.conj (y : PSL2 F) := by
    have h1 : psl2MulAutOf (α * β * α⁻¹ * β⁻¹) =
        psl2MulAutHom α * psl2MulAutHom β * (psl2MulAutHom α)⁻¹ * (psl2MulAutHom β)⁻¹ := by
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      rfl
    rw [h1]
    change psl2MulAutOf α * psl2MulAutOf β * (psl2MulAutOf α)⁻¹ * (psl2MulAutOf β)⁻¹ = _
    rw [hα, hβ, commutator_pglAction_mul_psl2FieldAut, ← hx, pglAction_toPGL]
  have h2 := DFunLike.congr_fun hcomm (QuotientGroup.mk b)
  rw [MulAut.conj_apply] at h2
  change ((((α * β * α⁻¹ * β⁻¹) b : SL(2, F)) : PSL2 F)) = (y * b * y⁻¹ : SL(2, F)) at h2
  exact QuotientGroup.eq.mp h2

end CFSG.ComponentClassification.RankTwoOddLie
