module

public import CFSG.LocalAnalysis.EvenSmallLie.FrontierOutcome
public import CFSG.LocalAnalysis.EvenSmallLie.FFourTwo.Main
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.Child2Final
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3Final
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3AltEight
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelectorFinal
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child4Final
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.Child5Complete
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaHAut
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.Child6
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylMain
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Child8Final
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Child79Done
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaHAutCaseInput

public section

namespace CFSG.EvenSmallLie.FrontierFinal

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Recognition


theorem frontier_models_of_epsilonOne (hG1 : Child3.GapEpsilonOne)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (L : Subgroup G) (hL : standardComponentIsStandard L)
    (hcore : ∀ t : G, orderOf t = 2 →
      standardComponentOddCore (Subgroup.centralizer ({t} : Set G)) = ⊥)
    (S : Sylow 2 (Subgroup.centralizer (L : Set G)))
    (hS : IsCyclic (S : Subgroup (Subgroup.centralizer (L : Set G))))
    (_htype : Blueprint.Recognition.Exact.EvenStandardType (L ⧸ Subgroup.center L))
    (_hexc : ¬ Blueprint.Recognition.Exact.EvenStandardException (L ⧸ Subgroup.center L))
    (hres : Blueprint.Recognition.Exact.EvenStandardResidual L)
    (hbcd : Blueprint.Recognition.Exact.ResidualB L ∨ Blueprint.Recognition.Exact.ResidualC L ∨
      Blueprint.Recognition.Exact.ResidualD L) :
    Blueprint.Recognition.EvenSporadicOutcome G :=
  even_small_lie_of_children FFourTwo.childG2F4 TwoE6.child2E6
    (Child3.childSp6Centerless_of_gaps hG1 Child3.gapLagrangianSelector' Child3.gapAltEight) SympSix.childSp6Cover
    (UnitarySix.Child5.childU6Centerless_of_hypAut UnitarySix.YamadaHAut.hypAutInput
        UnitarySix.YamadaHAut.caseInput)
    UnitarySix.childU6Cover OmegaEight.Child79.childO8PlusCenterless
    (OmegaEight.Child8.childO8PlusCover_of_inputs OmegaEight.Weyl.weylPackage) OmegaEight.Child79.childO8Minus G hnonab hK L hL hcore S hS
    hres hbcd

theorem frontier_of_epsilonOne (hG1 : Child3.GapEpsilonOne)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (L : Subgroup G) (hL : standardComponentIsStandard L)
    (hcore : ∀ t : G, orderOf t = 2 →
      standardComponentOddCore (Subgroup.centralizer ({t} : Set G)) = ⊥)
    (S : Sylow 2 (Subgroup.centralizer (L : Set G)))
    (hS : IsCyclic (S : Subgroup (Subgroup.centralizer (L : Set G))))
    (_htype : Blueprint.Recognition.Exact.EvenStandardType (L ⧸ Subgroup.center L))
    (_hexc : ¬ Blueprint.Recognition.Exact.EvenStandardException (L ⧸ Subgroup.center L))
    (hres : Blueprint.Recognition.Exact.EvenStandardResidual L)
    (hbcd : Blueprint.Recognition.Exact.ResidualB L ∨ Blueprint.Recognition.Exact.ResidualC L ∨
      Blueprint.Recognition.Exact.ResidualD L) :
    Nat.card G ∈ standardComponentEvenSporadicOrders := by
  rcases outcome_of_children FFourTwo.childG2F4 TwoE6.child2E6
    (Child3.childSp6Centerless_of_gaps hG1 Child3.gapLagrangianSelector' Child3.gapAltEight) SympSix.childSp6Cover
    (UnitarySix.Child5.childU6Centerless_of_hypAut UnitarySix.YamadaHAut.hypAutInput
        UnitarySix.YamadaHAut.caseInput)
    UnitarySix.childU6Cover OmegaEight.Child79.childO8PlusCenterless
    (OmegaEight.Child8.childO8PlusCover_of_inputs OmegaEight.Weyl.weylPackage) OmegaEight.Child79.childO8Minus G hnonab hK L hL hcore S hS
    hres hbcd
    with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · have h : Nat.card G = 495766656000 :=
      (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Co3.card_Co3
    rw [h, standardComponentEvenSporadicOrders]
    norm_num
  · have h : Nat.card G = 64561751654400 :=
      (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Fi22.card_Fi22
    rw [h, standardComponentEvenSporadicOrders]
    norm_num
  · have h : Nat.card G = CFSG.Open.monsterBabyOrder :=
      (Nat.card_congr e.toEquiv).trans CFSG.Monster.Existence.card_nativeB
    rw [h, standardComponentEvenSporadicOrders, CFSG.Open.monsterBabyOrder]
    norm_num

end CFSG.EvenSmallLie.FrontierFinal
