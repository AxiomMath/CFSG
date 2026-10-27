module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430ChevModel
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430ChevBridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.L84

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

theorem i1430M23Chev_holds :
    I1430M23Chev := by
  intro H _ _ hq _ ℓ hℓ hcat
  have hcen : Subgroup.center H = ⊥ :=
    I1430ChevBridge.center_eq_bot_of_isBOfTwo hq hℓ hcat
  obtain ⟨e⟩ := I1430ChevBridge.iso_sp_of_isBOfTwo hcat
  let e' : H ≃* ↥(StatedSp ℓ (ZMod 2)) :=
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hcen.symm)).trans e
  rw [hcen, pRank_bot_eq_zero 3 (by norm_num), add_zero]
  exact i1430TwoLocal_of_injective e'.symm.toMonoidHom e'.symm.injective
    (I1430ChevModel.i1430TwoLocal_statedSp ℓ hℓ)

end CFSG.LocalAnalysis.GLTheoremA.S8.L84
