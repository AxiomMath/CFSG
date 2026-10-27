module

public import CFSG.ClassicalInvolution.Q3.Q3TLFam
public import CFSG.ClassicalInvolution.SmallOrth.Orth3Block

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T

open Module QuadraticMap CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Orthogonal.Small
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
open CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

variable {K : Type} [Field K]

variable (K) in
@[expose] noncomputable def ePHom :
    elementaryGroup (quadPlus 4 K) →* StatedProj (StatedOmega (StatedQuadPlus 4 K)) :=
  (QuotientGroup.mk' _).comp
    (((toLinEquiv _ K).symm.toMonoidHom.comp (elementaryGroup (quadPlus 4 K)).subtype).codRestrict
      _ fun a => symm_mem_statedOmega a.2)

theorem ePHom_apply (a : elementaryGroup (quadPlus 4 K)) :
    ePHom K a = QuotientGroup.mk ⟨(toLinEquiv _ K).symm a, symm_mem_statedOmega a.2⟩ :=
  rfl

theorem ePHom_smul (a : elementaryGroup (quadPlus 4 K)) (X : Submodule K (Fin 4 ⊕ Fin 4 → K)) :
    statedProjectiveSubspaceAction (StatedQuadPlus 4 K) (ePHom K a) X =
      X.map (a : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)).toLinearMap := by
  rw [ePHom_apply]
  change X.map (toLinEquiv _ K ((toLinEquiv _ K).symm a)).toLinearMap = _
  rw [MulEquiv.apply_symm_apply]

theorem ePHom_eq_one_iff (a : elementaryGroup (quadPlus 4 K)) :
    ePHom K a = 1 ↔ (a : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) ∈
      scalars K (Fin 4 ⊕ Fin 4 → K) := by
  rw [ePHom_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, mem_statedScalars_iff]
  simp only [MulEquiv.apply_symm_apply]

section Block

variable {W W' : Submodule K (Fin 4 ⊕ Fin 4 → K)} (hc : IsCompl W W')
  (horth : ∀ u ∈ W, ∀ w ∈ W', polar (quadPlus 4 K) u w = 0)
  {P₁ P₂ : HypPair ((quadPlus 4 K).comp W.subtype)} (h : P₁.Orth P₂) (hdim : finrank K W = 4)

@[expose] noncomputable def rhoL : SL(2, K) →* StatedProj (StatedOmega (StatedQuadPlus 4 K)) :=
  (ePHom K).comp ((blockHom (quadPlus 4 K) hc horth).comp
    ((thetaL h hdim).codRestrict _ (thetaL_mem_elementaryGroup h hdim)))

@[expose] noncomputable def rhoR : SL(2, K) →* StatedProj (StatedOmega (StatedQuadPlus 4 K)) :=
  (ePHom K).comp ((blockHom (quadPlus 4 K) hc horth).comp
    ((thetaR h hdim).codRestrict _ (thetaR_mem_elementaryGroup h hdim)))

theorem rhoL_apply (A : SL(2, K)) :
    rhoL hc horth h hdim A = ePHom K (blockHom (quadPlus 4 K) hc horth
      ⟨thetaL h hdim A, thetaL_mem_elementaryGroup h hdim A⟩) :=
  rfl

theorem rhoR_apply (B : SL(2, K)) :
    rhoR hc horth h hdim B = ePHom K (blockHom (quadPlus 4 K) hc horth
      ⟨thetaR h hdim B, thetaR_mem_elementaryGroup h hdim B⟩) :=
  rfl

theorem rhoL_rhoR_comm (A B : SL(2, K)) :
    rhoL hc horth h hdim A * rhoR hc horth h hdim B =
      rhoR hc horth h hdim B * rhoL hc horth h hdim A := by
  rw [rhoL_apply, rhoR_apply, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
  congr 2
  exact Subtype.ext (thetaL_thetaR_comm h hdim A B)

theorem orthExtend_apply_right (φ : W ≃ₗ[K] W) {w : Fin 4 ⊕ Fin 4 → K} (hw : w ∈ W') :
    orthExtend hc φ w = w := by
  have := orthExtend_apply hc φ 0 ⟨w, hw⟩
  simpa using this

theorem eq_one_of_orthExtend_mem_scalars (hW' : W' ≠ ⊥) {φ : W ≃ₗ[K] W}
    (hs : orthExtend hc φ ∈ scalars K (Fin 4 ⊕ Fin 4 → K)) : φ = 1 := by
  obtain ⟨c, hcs⟩ := mem_scalars.mp hs
  obtain ⟨w', hw'W', hw'0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW'
  have hc1 : c = 1 := by
    have h2 := hcs w'
    rw [orthExtend_apply_right hc φ hw'W'] at h2
    have h3 : (1 - c) • w' = 0 := by rw [sub_smul, one_smul, ← h2, sub_self]
    exact (sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hw'0)).symm
  refine LinearEquiv.ext fun u => Subtype.ext ?_
  have h4 := orthExtend_apply hc φ u 0
  simp only [ZeroMemClass.coe_zero, add_zero] at h4
  rw [← h4, hcs, hc1, one_smul]
  rfl

theorem rhoL_injective (hW' : W' ≠ ⊥) : Function.Injective (rhoL hc horth h hdim) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  rw [rhoL_apply, ePHom_eq_one_iff, coe_blockHom] at hA
  exact thetaL_injective h hdim ((eq_one_of_orthExtend_mem_scalars hc hW' hA).trans
    (map_one _).symm)

theorem rhoR_injective (hW' : W' ≠ ⊥) : Function.Injective (rhoR hc horth h hdim) := by
  rw [injective_iff_map_eq_one]
  intro B hB
  rw [rhoR_apply, ePHom_eq_one_iff, coe_blockHom] at hB
  exact thetaR_injective h hdim ((eq_one_of_orthExtend_mem_scalars hc hW' hB).trans
    (map_one _).symm)

end Block

end CFSG.ClassicalInvolution.Q3.Q3T
