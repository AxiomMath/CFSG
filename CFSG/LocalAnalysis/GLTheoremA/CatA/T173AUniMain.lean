module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AUniQuot
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AUniCentre
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AUniBStruct
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AUniHbQuot
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AUniCompQuot
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AIvLift

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.T173
open scoped MatrixGroups

theorem t173AUni_holds : T173AUni := by
  intro p Ω _ _ S B N D K x n d F _ _ θ hcfg hM hd
  have hp : p.Prime := hcfg.prime
  have hp2 : p ≠ 2 := hcfg.odd
  have hZ : ¬ p ∣ Nat.card (Subgroup.center ↥S) := uni_center_coprime hp hcfg.qs hM hd
  obtain ⟨hBx, hBe⟩ := uni_B_structure hcfg hM hd hZ
  have hxC : x ∈ Subgroup.centralizer (S : Set Ω) :=
    (hcfg.cent x hcfg.mem).2 (Subgroup.mem_zpowers x)
  have harith : UniArith p n d F :=
    ⟨hp, hM.2.2.2.2.1, hd, hM.1, hM.2.1, hM.2.2.1, hM.2.2.2.1⟩
  obtain ⟨T', hT2, hTN, hTc⟩ := hb_quot hp hp2 hZ hcfg.elem hM.2.2.2.2.2.1 hxC hBx hcfg.hb
  obtain ⟨y, hyB, hy1, hK⟩ := comp_quot hp hZ hcfg.elem hBx hcfg.mem hcfg.ne_one hxC hcfg.std
  have hcomp : CFSG.Open.IsComponentOf K (S ⊓ Subgroup.centralizer (D : Set Ω)) :=
    hcfg.std.2.2.2.2.2.1
  have hKS : K ≤ S := hcomp.1.trans inf_le_left
  have hyQ : (QuotientGroup.mk y : ↥S ⧸ Subgroup.center ↥S) ∈ modCentreImage S B := by
    unfold modCentreImage
    exact Subgroup.mem_map.2 ⟨y, Subgroup.mem_subgroupOf.2 hyB, rfl⟩
  obtain ⟨B', U, hB'e, hle, hne, hBK, hU, hU2, hUK, hdec⟩ :=
    uni_quot_iv harith θ hBe ⟨T', hT2, hTN, hTc⟩ hyQ hy1 hK
  unfold T173Concl
  right
  exact iv_lift hp hp2 hZ hcfg.elem hcfg.mem hxC hBx hKS hcomp.2.2 hB'e hle hne hBK hU hU2 hUK
    hdec

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
