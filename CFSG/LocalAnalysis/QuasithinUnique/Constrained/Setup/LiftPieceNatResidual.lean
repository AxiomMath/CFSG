module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftNatDecomp

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup

theorem natResidualProp : NatResidualProp := by
  intro G _ _ R M V n F _ r Lc ctx i P hloc
  classical
  have hS := ctx.setting
  have hbasic := hloc.basic
  have hbase := hloc.base
  have hmin := hloc.minimal
  have hSP : baum R ≤ P := hbasic.lt.le
  have hSR : baum R ≤ R := inf_le_left
  have hSM : baum R ≤ M ⊓ P := le_inf (hSR.trans hS.max.1) hSP
  have hMP : M ⊓ P < P := by
    refine lt_of_le_of_ne inf_le_right fun h => hmin.not_le ?_
    rw [← h]
    exact inf_le_left
  have hmax : ∀ Y : Subgroup G, baum R ≤ Y → Y < P → Y ≤ M ⊓ P := fun Y hY hYP =>
    le_inf (hbasic.max Y hY hYP) hYP.le
  have hTn : ¬ P ≤ normalizer (baum R : Set G) := fun h =>
    hbasic.not_normal ((normal_subgroupOf_iff_le_normalizer hSP).mpr h)
  have hJP : thompsonJ (baum R) ≤ P := (B6.thompsonJ_le (baum R)).trans hSP
  have hVH : ¬ P ≤ centralizer (modComm V (Lc i) : Set G) := fun hc =>
    hloc.campbell.thompson_ne (commutator_eq_bot_iff_le_centralizer.mpr (hJP.trans hc))
  obtain ⟨hPeq, -⟩ := reduced_detects_commutator hbasic.sylow hTn hSM hMP hmax
    hloc.image.I_reduced hVH
  obtain ⟨hdet1, hdet2⟩ := reduced_detects_commutator_thompsonJ hbasic.sylow hTn hSM hMP hmax
    hloc.image.I_reduced hVH
  have hKP : P ≤ normalizer (oddOrderSubgroup P : Set G) :=
    le_normalizer.trans (normalizer_le_normalizer_oddOrderSubgroup P)
  have hnot : ¬ thompsonJ (baum R) ≤ pCoreOf 2 P := fun h =>
    hloc.campbell.thompson_ne (commutator_eq_bot_iff_le_centralizer.mpr (hdet2.mp h))
  have hle : ⁅oddOrderSubgroup P, thompsonJ (baum R)⁆ ≤ oddOrderSubgroup P :=
    le_normalizer_iff_commutator_le_left.mp (hJP.trans hKP)
  have hperf : ⁅oddOrderSubgroup P, thompsonJ (baum R)⁆ = oddOrderSubgroup P :=
    hle.eq_or_lt.resolve_right fun hlt => hnot (hdet1.mp hlt)
  refine ⟨hPeq, ?_⟩
  rw [← hbase.J_S]
  exact hperf

end CFSG.QuasithinUnique.Setup.Lift
