module

public import Mathlib.GroupTheory.QuotientGroup.Basic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Pointwise Subgroup QuotientGroup

variable {G : Type*} [Group G] (H K : Subgroup G) [H.Normal]

instance normal_inf_subgroupOf_right : ((H ⊓ K).subgroupOf K).Normal := by
  rw [Subgroup.inf_subgroupOf_right]; infer_instance

def toQuotientSup : K →* (H ⊔ K : Subgroup G) ⧸ H.subgroupOf (H ⊔ K) :=
  (QuotientGroup.mk' _).comp (Subgroup.inclusion le_sup_right)

theorem toQuotientSup_apply (k : K) :
    toQuotientSup H K k = QuotientGroup.mk (Subgroup.inclusion le_sup_right k) := (rfl)

theorem toQuotientSup_surjective : Function.Surjective (toQuotientSup H K) := by
  intro x
  induction x using QuotientGroup.induction_on with
  | _ y =>
    have hy : (y : G) ∈ (H : Set G) * (K : Set G) := by
      rw [← Subgroup.normal_mul]; exact y.2
    obtain ⟨h, hh, k, hk, hhk⟩ := hy
    refine ⟨⟨k, hk⟩, ?_⟩
    rw [toQuotientSup_apply, QuotientGroup.eq]
    change (k : G)⁻¹ * (y : G) ∈ H
    rw [← hhk, ← mul_assoc]
    simpa using (Subgroup.Normal.conj_mem ‹H.Normal› h hh k⁻¹)

theorem ker_toQuotientSup : (toQuotientSup H K).ker = (H ⊓ K).subgroupOf K := by
  ext k
  simp [toQuotientSup, Subgroup.mem_subgroupOf]

noncomputable def quotientInfEquivSupQuotient :
    K ⧸ (H ⊓ K).subgroupOf K ≃* (H ⊔ K : Subgroup G) ⧸ H.subgroupOf (H ⊔ K) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_toQuotientSup H K).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (toQuotientSup_surjective H K))

@[simp]
theorem quotientInfEquivSupQuotient_mk (k : K) :
    quotientInfEquivSupQuotient H K (QuotientGroup.mk k) =
      QuotientGroup.mk (Subgroup.inclusion le_sup_right k) := by
  rw [quotientInfEquivSupQuotient, MulEquiv.trans_apply,
    QuotientGroup.quotientMulEquivOfEq_mk, QuotientGroup.quotientKerEquivOfSurjective,
    QuotientGroup.quotientKerEquivOfRightInverse_apply, QuotientGroup.kerLift_mk,
    toQuotientSup_apply]

@[simp]
theorem quotientInfEquivSupQuotient_symm_mk (k : K) :
    (quotientInfEquivSupQuotient H K).symm
        (QuotientGroup.mk (Subgroup.inclusion le_sup_right k)) = QuotientGroup.mk k := by
  rw [MulEquiv.symm_apply_eq, quotientInfEquivSupQuotient_mk]

theorem quotientInfEquivSupQuotient_comp_mk :
    (quotientInfEquivSupQuotient H K).toMonoidHom.comp (QuotientGroup.mk' _) =
      toQuotientSup H K := by
  ext k
  simpa using (toQuotientSup_apply H K k).symm

end CFSG.FeitThompson
