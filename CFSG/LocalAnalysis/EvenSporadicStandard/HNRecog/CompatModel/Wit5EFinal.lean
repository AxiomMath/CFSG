module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.CpInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CompatModel.Transport
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CompatModel.Wit5EDict
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CompatModel.Wit5ESpec

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3
  CFSG.EvenSporadicStandard.HNRecog.CompatModel

section Cert


theorem wit5e_holds : Wit5E := by
  intro G _ a z h x _ t t' hat hzt' hztt' htx ht'x _
  obtain ⟨ht't, Ψ, hΨ, hΨt'⟩ := exists_vertexIso_at_pZ₁ h hat ⟨hzt', hztt'⟩
  have hta : a * t = t * a := mem_Gx.1 (mem_Gxy.1 htx).1
  have htx' : x * t = t * x := mem_Gx.1 (mem_Gxy.1 htx).2
  have ha : a ∈ Gx t := mem_Gx.2 hta.symm
  have hx : x ∈ Gx t := mem_Gx.2 htx'.symm
  have e1 : (⟨a, ha⟩ : ↥(Gx t)) * ⟨t', ht't⟩ = ⟨t', ht't⟩ * ⟨a, ha⟩ :=
    Subtype.ext (mem_Gx.1 (mem_Gxy.1 ht'x).1)
  have e2 : (⟨x, hx⟩ : ↥(Gx t)) * ⟨t', ht't⟩ = ⟨t', ht't⟩ * ⟨x, hx⟩ :=
    Subtype.ext (mem_Gx.1 (mem_Gxy.1 ht'x).2)
  have hac : Ψ ⟨a, ha⟩ * pZ₁ = pZ₁ * Ψ ⟨a, ha⟩ := by
    have := congrArg Ψ e1
    rwa [map_mul, map_mul, hΨt'] at this
  have hxc : Ψ ⟨x, hx⟩ * pZ₁ = pZ₁ * Ψ ⟨x, hx⟩ := by
    have := congrArg Ψ e2
    rwa [map_mul, map_mul, hΨt'] at this
  have haA : In2A (Ψ ⟨a, ha⟩) := (hΨ.isConj_a_iff hat ⟨a, ha⟩).1 (IsConj.refl a)
  have hmodel := wit5e_model (natCard_P1408_of_F5Std h) _ _ haA hac hxc
  have hΨt'' : Ψ.symm pZ₁ = ⟨t', ht't⟩ := (MulEquiv.symm_apply_eq Ψ).2 hΨt'.symm
  let f : ↥P1408 →* G := (Gx t).subtype.comp Ψ.symm.toMonoidHom
  have hf : ∀ p, f p = (Ψ.symm p : G) := fun p => rfl
  have hfx : f (Ψ ⟨x, hx⟩) = x := by rw [hf, MulEquiv.symm_apply_apply]
  have h2 := Subgroup.mem_map_of_mem f hmodel
  rw [MonoidHom.map_closure, hfx] at h2
  refine Subgroup.closure_mono ?_ h2
  rintro _ ⟨y, ⟨hy1, hy2, hy3⟩, rfl⟩
  refine ⟨mem_Gxy.2 ⟨(Ψ.symm y).2, mem_Gx.2 ?_⟩, ?_, fun h5 => hy3 ?_⟩
  · have := coe_symm_comm Ψ hy1.symm
    rwa [hΨt''] at this
  · rw [hf]
    exact (hΨ.isConj_a_iff hat (Ψ.symm y)).2 (by rwa [MulEquiv.apply_symm_apply])
  · have h6 : orderOf (Ψ ⟨a, ha⟩ * y) = orderOf (⟨a, ha⟩ * Ψ.symm y : ↥(Gx t)) := by
      rw [← MulEquiv.orderOf_eq Ψ.symm, map_mul, MulEquiv.symm_apply_apply]
    rw [h6, ← Subgroup.orderOf_coe]
    exact h5.2.1

end Cert

end CFSG.EvenSporadicStandard.HNRecog.Section4
