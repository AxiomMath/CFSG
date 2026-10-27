module

public import CFSG.ClassicalInvolution.Phan.PhanP13Fix
public import CFSG.ClassicalInvolution.Phan.PhanP7Rot
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders

public section

namespace CFSG.ClassicalInvolution.PhanP

open QuadraticMap CliffordAlgebra CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.GroupTheory.WeirSylow
open scoped MatrixGroups

section Elliptic

variable {F : Type} [Field F] {ε : F} {hε : ε ≠ 0} {h4 : (4 : F) ≠ 0}

@[expose] noncomputable def combMap (h2 : (2 : F) ≠ 0) (ε : F) (hε : ε ≠ 0) (h4 : (4 : F) ≠ 0) :
    (F × F) →ₗ[F] planeA ε hε h4 where
  toFun v := ⟨v.1 • vecA1 F + v.2 • jOp ε (vecA1 F),
    add_mem (Submodule.smul_mem _ _ (vecA1_mem_planeA ε hε h4))
      (Submodule.smul_mem _ _ (jOp_mem_planeA h2 (vecA1_mem_planeA ε hε h4)))⟩
  map_add' v w := by
    refine Subtype.ext ?_
    simp only [Prod.fst_add, Prod.snd_add, add_smul, Submodule.coe_add]
    abel
  map_smul' c v := by
    refine Subtype.ext ?_
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_smul, RingHom.id_apply,
      Submodule.coe_smul, smul_add]

theorem combMap_apply (h2 : (2 : F) ≠ 0) (v : F × F) :
    ((combMap h2 ε hε h4 v : planeA ε hε h4) : Fin 4 ⊕ Fin 4 → F) =
      v.1 • vecA1 F + v.2 • jOp ε (vecA1 F) := rfl

theorem combMap_bijective (h2 : (2 : F) ≠ 0) : Function.Bijective (combMap h2 ε hε h4) := by
  refine ⟨fun v w h => ?_, fun x => ?_⟩
  · have := congrArg Subtype.val h
    rw [combMap_apply, combMap_apply] at this
    obtain ⟨h1, h2'⟩ := comb_A_inj hε this
    exact Prod.ext h1 h2'
  · obtain ⟨α, β, hx⟩ := exists_comb_of_mem_planeA h2 x.2
    exact ⟨(α, β), Subtype.ext hx.symm⟩

end Elliptic

section Binary

theorem nondegenerate_binForm {F : Type} [Field F] (h2 : (2 : F) ≠ 0) {ε : F} (hε : ε ≠ 0) :
    (binForm (0 : F) ε).Nondegenerate := by
  have : Invertible (2 : F) := invertibleOfNonzero h2
  refine QuadraticMap.nondegenerate_polar_iff.mp ?_
  have hsep : ∀ v : F × F, (∀ w, polarBilin (binForm (0 : F) ε) v w = 0) → v = 0 := by
    intro v hv
    have h1 := hv (1, 0)
    have h3 := hv (0, 1)
    rw [polarBilin_apply_apply, polar, binForm_apply, binForm_apply, binForm_apply] at h1 h3
    simp only [Prod.fst_add, Prod.snd_add] at h1 h3
    have e1 : 2 * v.1 = 0 := by linear_combination h1
    have e2 : 2 * ε * v.2 = 0 := by linear_combination h3
    refine Prod.ext ?_ ?_
    · exact (mul_eq_zero.1 e1).resolve_left h2
    · exact (mul_eq_zero.1 e2).resolve_left (mul_ne_zero h2 hε)
  exact ⟨hsep, fun v hv => hsep v (fun w => by rw [polarBilin_apply_apply, polar_comm]; exact hv w)⟩

end Binary

section Plane

noncomputable def planeAIsometry {F : Type} [Field F] (h2 : (2 : F) ≠ 0) (ε : F) (hε : ε ≠ 0)
    (h4 : (4 : F) ≠ 0) :
    (binForm (0 : F) ε).IsometryEquiv ((quadPlus 4 F).restrict (planeA ε hε h4)) where
  toLinearEquiv := LinearEquiv.ofBijective (combMap h2 ε hε h4) (combMap_bijective h2)
  map_app' v := by
    rw [binForm_apply]
    change quadPlus 4 F (v.1 • vecA1 F + v.2 • jOp ε (vecA1 F)) = _
    rw [Q_comb_A]
    ring

theorem restrict_planeA_nondegenerate {F : Type} [Field F] (h2 : (2 : F) ≠ 0) {ε : F}
    (hε : ε ≠ 0) (h4 : (4 : F) ≠ 0) :
    ((quadPlus 4 F).restrict (planeA ε hε h4)).Nondegenerate :=
  (planeAIsometry h2 ε hε h4).nondegenerate_iff.mp (nondegenerate_binForm h2 hε)

theorem finrank_planeA {F : Type} [Field F] (h2 : (2 : F) ≠ 0) {ε : F} (hε : ε ≠ 0)
    (h4 : (4 : F) ≠ 0) : Module.finrank F (planeA ε hε h4) = 2 := by
  have := (planeAIsometry h2 ε hε h4).toLinearEquiv.finrank_eq
  rw [Module.finrank_prod, Module.finrank_self] at this
  omega

end Plane

section Minus

variable {F : Type} [Field F]

theorem finrank_planeA_perp (h2 : (2 : F) ≠ 0) {ε : F} (hε : ε ≠ 0) (h4 : (4 : F) ≠ 0) :
    Module.finrank F (LinearMap.BilinForm.orthogonal (quadPlus 4 F).polarBilin
      (planeA ε hε h4)) = 6 := by
  have : Invertible (2 : F) := invertibleOfNonzero h2
  have hA := restrict_planeA_nondegenerate h2 hε h4
  have h1 := Submodule.finrank_add_eq_of_isCompl hA.isCompl_orthogonal
  rw [finrank_planeA h2 hε h4] at h1
  have h8 : Module.finrank F (Fin 4 ⊕ Fin 4 → F) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  omega

theorem not_isPlusType_planeA_perp [Finite F] (h2 : (2 : F) ≠ 0) {ε : F} (hε : ε ≠ 0)
    (h4 : (4 : F) ≠ 0) (hε' : ¬IsSquare (-ε)) :
    ¬ IsPlusType ((quadPlus 4 F).restrict (LinearMap.BilinForm.orthogonal
      (quadPlus 4 F).polarBilin (planeA ε hε h4))) := by
  intro hplus
  have : Invertible (2 : F) := invertibleOfNonzero h2
  have hA := restrict_planeA_nondegenerate h2 hε h4
  have hQ : (quadPlus 4 F).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp (nondegenerate_polarBilin_quadPlus 4 F)
  have hN := hQ.nondegenerate_restrict_orthogonal hA
  obtain ⟨eP⟩ := nonempty_isometry_quadPlus (n := 3) (QuadraticMap.nondegenerate_polar_iff.mpr hN)
    (by rw [finrank_planeA_perp h2 hε h4]) hplus
  have hirr : ∀ s : F, s ^ 2 + 0 * s + ε ≠ 0 := fun s hs =>
    hε' ⟨s, by linear_combination -hs⟩
  have e : (quadPlus 4 F).IsometryEquiv (quadMinus 4 F 0 ε) :=
    ((decompOrth hA).symm.trans ((eP.prod (planeAIsometry h2 ε hε h4).symm).trans
      (quadMinusIsometry 4 0 ε).symm))
  exact not_isPlusType_quadMinus (by norm_num) hirr ((isPlusType_quadPlus F 4).of_isometryEquiv e)

theorem nonempty_isometry_planeA_perp_quadMinus [Finite F] (h2 : (2 : F) ≠ 0) {ε : F} (hε : ε ≠ 0)
    (h4 : (4 : F) ≠ 0) (hε' : ¬IsSquare (-ε)) :
    Nonempty (((quadPlus 4 F).restrict (LinearMap.BilinForm.orthogonal (quadPlus 4 F).polarBilin
      (planeA ε hε h4))).IsometryEquiv (quadMinus 3 F 0 ε)) := by
  have : Invertible (2 : F) := invertibleOfNonzero h2
  have hA := restrict_planeA_nondegenerate h2 hε h4
  have hQ : (quadPlus 4 F).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp (nondegenerate_polarBilin_quadPlus 4 F)
  have hN := hQ.nondegenerate_restrict_orthogonal hA
  exact nonempty_isometry_of_not_isPlusType (QuadraticMap.nondegenerate_polar_iff.mpr hN)
    (n := 3) (by norm_num) (finrank_planeA_perp h2 hε h4) (not_isPlusType_planeA_perp h2 hε h4 hε')
    (fun s hs => hε' ⟨s, by linear_combination -hs⟩)

end Minus

end CFSG.ClassicalInvolution.PhanP
