module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceNatTools
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellPropagation

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Campbell

theorem natQProp
    : NatQProp := by
  intro G _ _ R M V n F _ r Lc ctx i P hloc hres had
  classical
  have hS := ctx.setting
  have hout := even_SL2_natural_baumann hS ctx.comps ctx.natural
  have hSP : baum R ≤ P := hloc.basic.lt.le
  have hPLS := hres.le_LS
  have hblk : IsBlock2 P (oddOrderSubgroup P) := had.chi0.1
  obtain ⟨hUW, hQY, -⟩ := full_Sylow_short_core_propagation hloc.base.charTwo hout.sylow hSP hPLS
    hblk
  refine ⟨hQY.trans had.coreComm, ?_, ?_⟩
  · rw [BlueprintB2.omegaOneCenterOf_eq_centerTorsion, ← had.coreComm]
    exact hUW
  · have hQ2 : IsPGroup 2 (blockQ (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R)) :=
      C1.blockQ_isPGroup _
    have hQn : oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R ≤
        normalizer (blockQ (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R) : Set G) :=
      C1.le_normalizer_blockQ _
    have hQH : blockQ (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R) ≤ P :=
      (hout.sylow.pCoreOf_le).trans hSP
    exact (signalizer_action_ambient hblk.2.1 hblk.2.2 hblk.1.1 hQ2 hQH
      (((oddOrderSubgroup_le P).trans hPLS).trans hQn)).1

end CFSG.QuasithinUnique.Setup.Lift
