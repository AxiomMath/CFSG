module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LocalEmbeddingInheritance

public section

namespace CFSG.ProperTwoGeneratedCore

open CFSG.BenderSuzuki CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G]

theorem actual_right_conjugate_intersection_eq_normal_core (H : Subgroup G) :
    (⨅ g : G, rightConjugate H g) = H.normalCore := by
  rw [H.normalCore_eq_iInf_comap_conj]
  congr 1
  funext g
  change H.map (MulAut.conj g⁻¹).toMonoidHom = H.comap (↑(MulAut.conj g) : G →* G)
  rw [Subgroup.map_equiv_eq_comap_symm']
  have heq : (MulAut.conj g⁻¹).symm.toMonoidHom = (↑(MulAut.conj g) : G →* G) := by
    rw [← MulEquiv.toMonoidHom_eq_coe (MulAut.conj g)]
    ext x
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_symm_apply, inv_inv,
      MulAut.conj_apply]
  rw [heq]

theorem point_right_coset_kernel_iff (H : Subgroup G) (g : G) :
    (∀ omega : pointRightCosetSpace H, pointRightCosetMul H omega g = omega) ↔
      g ∈ H.normalCore := by
  rw [H.normalCore_eq_iInf_comap_conj]
  constructor
  · intro hfix
    apply Subgroup.mem_iInf.mpr
    intro x
    have hx := hfix (Quotient.mk (QuotientGroup.rightRel H) x)
    rw [pointRightCosetMul_mk] at hx
    have hrel := Quotient.exact hx.symm
    change QuotientGroup.rightRel H x (x * g) at hrel
    rw [QuotientGroup.rightRel_apply] at hrel
    change x * g * x⁻¹ ∈ H
    simpa only [mul_assoc] using hrel
  · intro hcore omega
    refine Quotient.inductionOn omega fun x => ?_
    rw [pointRightCosetMul_mk]
    apply Eq.symm
    apply Quotient.sound
    change QuotientGroup.rightRel H x (x * g)
    rw [QuotientGroup.rightRel_apply]
    have hx := Subgroup.mem_iInf.mp hcore x
    change x * g * x⁻¹ ∈ H at hx
    simpa only [mul_assoc] using hx

theorem point_right_coset_faithful_of_normal_core_eq_bot
    (H : Subgroup G) (hcore : H.normalCore = ⊥) :
    Function.Injective (fun g : G => fun omega : pointRightCosetSpace H =>
      pointRightCosetMul H omega g) := by
  intro g k hsame
  have hfix : ∀ omega : pointRightCosetSpace H,
      pointRightCosetMul H omega (g * k⁻¹) = omega := by
    intro omega
    have heq : pointRightCosetMul H omega g = pointRightCosetMul H omega k :=
      congrFun hsame omega
    rw [← pointRightCosetMul_mul, heq,
      pointRightCosetMul_mul, mul_inv_cancel, pointRightCosetMul_one]
  have hmem := (point_right_coset_kernel_iff H (g * k⁻¹)).mp hfix
  rw [hcore] at hmem
  exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp hmem)

end CFSG.ProperTwoGeneratedCore
