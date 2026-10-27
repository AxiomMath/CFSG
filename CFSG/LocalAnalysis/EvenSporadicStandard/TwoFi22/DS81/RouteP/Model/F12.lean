module

public import Certificates.Certificate450289
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.F12Central
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Rigid

public section

open scoped Pointwise

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model

open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

theorem rigidOK_planeDTabs_eq_true :
    CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Rigid.Native.rigidOK 891 (planeDTabs ())
      (planeInterCount (planeXData ())) = true :=
  Certificates.certificate450289

theorem f12 :
    ∀ β : ↥Q0 ≃* ↥Q0, (∀ d : ↥Q0, (d : Q3) ∈ D0 → β d = d) → β = MulEquiv.refl _ := by
  intro β hβ
  letI := planeXMulAction
  haveI := planeXMulAction_isPretransitive
  refine CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Rigid.eq_refl_of_rigidOK
    (n := 891) (gens := planeDTabs ()) (R := planeInterCount (planeXData ()))
    (0 : Fin 891) (D0.subgroupOf Q0) ?_ planeGenQ ?_ ?_ ?_ rigidOK_planeDTabs_eq_true ?_ ?_ β ?_
  · intro q hq
    rw [stabilizer_planeXMulAction_zero]
    exact hq
  · intro k hk
    rw [planeDTabs_size] at hk
    exact planeGenQ_mem_D0 hk
  · intro k hk i
    rw [planeDTabs_size] at hk
    exact planeDTabs_getElem_eq hk i
  · intro q a b
    exact planeInterCount_planeXAct q a b
  · intro q hq
    exact mem_center_of_planeXAct_fixes hq
  · rw [stabilizer_planeXMulAction_zero]
    exact sup_commutator_eq_top
  · intro d hd
    rw [stabilizer_planeXMulAction_zero] at hd
    exact hβ d (Subgroup.mem_subgroupOf.1 hd)

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
