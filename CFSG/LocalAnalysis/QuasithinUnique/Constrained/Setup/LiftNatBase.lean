module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftBaumannOrig
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftNatDecomp
public import CFSG.LocalAnalysis.QuasithinUnique.EscapingComponents

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup

theorem natBaseProp
    : NatBaseProp := by
  intro G _ _ R M V n F _ r Lc ctx hVS
  have hS := ctx.setting
  have hout := even_SL2_natural_baumann hS ctx.comps ctx.natural
  have hred := hS.reduced
  have hVn : V.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hred.2.1)
  have hJS : thompsonJ (baum R) = thompsonJ R :=
    B6.thompsonJ_eq_of_le (B6.thompsonJ_le_baum R) inf_le_left
  have hV2 : IsPGroup 2 ↥V := fun g => ⟨1, Subtype.ext (by simpa using hred.2.2.1.2 g g.2)⟩
  refine ⟨C1GN.characteristic_baum R, hJS, by rw [hJS], C1GN.baum_baum R, ?_, ?_, ?_⟩
  · exact EscapingComponents.charTwo_of_isSubnormal ctx.charTwo le_top
      (Subgroup.Normal.isSubnormal ((normal_L_sup_baum hS).subgroupOf _))
  · exact EscapingLocal.pCoreOf_le_of_isSylowTwoOf hout.sylow
  · exact CFSG.LieType.BorelTits.le_pCoreOf 2 (hVS.trans le_sup_right) (hVn.subgroupOf _) hV2

end CFSG.QuasithinUnique.Setup.Lift
