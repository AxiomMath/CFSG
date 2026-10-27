module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.CpInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CompatModel.Dict
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CompatModel.Gen2ASpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CompatModel.Transport

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3
  CFSG.EvenSporadicStandard.HNRecog.CompatModel

section Cert


theorem gen2A_holds : Gen2A := by
  intro G _ a z h x hx b hb
  obtain ⟨hbx, Ψ, hΨ, hΨb⟩ := exists_vertexIso_at_pB h hx hb
  obtain ⟨c₁, c₂, g, ho1, ho2, hcb1, hcb2, h11, h12, h13, h21, h22, h23, hg1, hg2, hgb, hcl⟩ :=
    gen2a_model
  obtain ⟨hi1, hx1, hb1, hxb1⟩ := invIn_Gxy_of_model hbx Ψ hΨ.self_eq hΨb ho1 hcb1 h11 h12 h13
  obtain ⟨hi2, hx2, hb2, hxb2⟩ := invIn_Gxy_of_model hbx Ψ hΨ.self_eq hΨb ho2 hcb2 h21 h22 h23
  refine ⟨(Ψ.symm c₁ : G), (Ψ.symm c₂ : G), (Ψ.symm g : G), hi1, hi2, hx1, hb1, hxb1, hx2, hb2,
    hxb2, mem_Gxyz.2 ⟨(Ψ.symm g).2, mem_Gx.2 (coe_symm_comm Ψ hg1.symm),
      mem_Gx.2 (coe_symm_comm Ψ hg2.symm)⟩, fun e => hgb ?_, closure_Gxy_eq Ψ hcl⟩
  have e' : (⟨b, hbx⟩ : ↥(Gx x)) * Ψ.symm g = Ψ.symm g * ⟨b, hbx⟩ := Subtype.ext e
  have := congrArg Ψ e'
  rw [map_mul, map_mul, hΨb, MulEquiv.apply_symm_apply] at this
  exact this.symm

end Cert

end CFSG.EvenSporadicStandard.HNRecog.Section4
