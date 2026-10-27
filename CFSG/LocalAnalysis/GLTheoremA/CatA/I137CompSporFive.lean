module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I137CompList
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SporTables
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2FamSpor

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (LieOrderBridge SporadicOrdersTable sporOrd)
open CFSG.LocalAnalysis.GLTheoremB.MovingAround (SporTables.SporTypes)

private theorem not_two_pow_sixty_dvd_sporOrd (name : TauCeti.SporadicName) :
    ¬ 2 ^ 60 ∣ sporOrd name := by
  cases name <;>
    norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu,
      CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime,
      CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster,
      CFSG.Open.orderMonster]

theorem sporTypes_notList93_five (hb : LieOrderBridge) (hOrd : SporadicOrdersTable)
    (name : TauCeti.SporadicName) :
    SporTables.SporTypes 5 (fun T _ => ¬ catalogIs T (S9.isList93 5)) name := by
  intro T _ _ ⟨e⟩ s _ I _ hcat
  haveI : Finite (PSimple 5 I) := inferInstance
  have h260 : 2 ^ 60 ∣ Nat.card (PSimple 5 I) :=
    two_pow_sixty_dvd_card_of_isList93_five hb hcat
  have hdvd : 2 ^ 60 ∣ Nat.card T :=
    h260.trans ((Subgroup.card_quotient_dvd_card _).trans
      ((Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_subgroup_dvd_card I)))
  have hcard : Nat.card T = sporOrd name :=
    (Nat.card_congr e.toEquiv).trans (hOrd name)
  exact not_two_pow_sixty_dvd_sporOrd name (hcard ▸ hdvd)

end CFSG.LocalAnalysis.GLTheoremA
