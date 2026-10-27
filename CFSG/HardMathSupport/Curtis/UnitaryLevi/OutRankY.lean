module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.NormalizerConj

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

variable {Y : Type} [Group Y] {L : Subgroup Y}

@[expose] noncomputable def descendHom {P : Type} [Group P] (e : ↥L ⧸ Subgroup.center ↥L ≃* P) :
    Subgroup.normalizer (L : Set Y) →* MulAut P :=
  MonoidHom.mk' (fun u => descendAut e (u : Y) u.2) (fun u v => by
    ext p
    obtain ⟨q, rfl⟩ := e.surjective p
    obtain ⟨ℓ, rfl⟩ := QuotientGroup.mk_surjective q
    simp only [MulAut.mul_apply, descendAut_apply]
    congr 2
    ext
    simp [mul_assoc])

theorem inv_mul_mem_centralizer_of_descendAut_eq_conj [Group.IsPerfect ↥L] {P : Type} [Group P]
    (e : ↥L ⧸ Subgroup.center ↥L ≃* P) {a : Y} (ha : a ∈ Subgroup.normalizer (L : Set Y))
    (ℓ : ↥L) (h : descendAut e a ha = MulAut.conj (e (QuotientGroup.mk ℓ))) :
    (ℓ : Y)⁻¹ * a ∈ Subgroup.centralizer (L : Set Y) := by
  have key : (MulAut.conj ℓ).toMonoidHom = (conjL a ha).toMonoidHom := by
    refine eq_of_inv_mul_mem_center _ _ fun g => ?_
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, inv_mul_eq_one]
    apply e.injective
    change e (QuotientGroup.mk (ℓ * g * ℓ⁻¹)) = e (QuotientGroup.mk (conjL a ha g))
    have h1 := congrArg (fun α : MulAut P => α (e (QuotientGroup.mk g))) h
    simp only [MulAut.conj_apply, descendAut_apply] at h1
    rw [h1]
    simp [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  have h1 := congrArg (fun f : ↥L →* ↥L => ((f ⟨g, hg⟩ : ↥L) : Y)) key
  simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom, coe_conjL, Subgroup.coe_mul,
    InvMemClass.coe_inv] at h1
  calc g * ((ℓ : Y)⁻¹ * a) = (ℓ : Y)⁻¹ * ((ℓ : Y) * g * (ℓ : Y)⁻¹) * a := by group
    _ = (ℓ : Y)⁻¹ * (a * g * a⁻¹) * a := by rw [h1]
    _ = ((ℓ : Y)⁻¹ * a) * g := by group

end CFSG.HardMathSupport.Curtis.UnitaryLevi
