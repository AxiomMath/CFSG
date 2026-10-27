module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneHallTwoArithAltSpor
public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersSporadic
public import CFSG.Sporadic.Th.Certificate
public import CFSG.Monster.SteinbergMCatalogNativeIso
public import CFSG.YGroups.Y443.Tri.Finiteness

public section

namespace CFSG.SeitzReduction.RankOne

open CFSG.Blueprint NativeSporadic


theorem card_of_mulEquiv_nativeM {T : Type*} [Group T] [IsSimpleGroup T] (θ : T ≃* M) :
    Nat.card T = CFSG.Open.monsterOrder :=
  (Nat.card_eq_of_bijective _
    (CFSG.ComponentClassification.BMCase.catalog_fM_comp_mulEquiv_bijective θ)).trans
    CFSG.YGroups.Y443.natCard_Gmat_eq_monsterOrder

section Sporadic


theorem not_hallTwoArith_sporadic {T : Type} [Group T] [IsSimpleGroup T] (hs : SporadicRep T) :
    ¬ HallTwoArith (Nat.card T) := by
  obtain ⟨s, ⟨θ⟩⟩ := hs
  cases s
  case M11 =>
    exact not_hallTwoArith_card_of_mulEquiv θ (e := 4) (h := 495)
      (CFSG.Sporadic.Mathieu.card_M11.trans (by norm_num)) (by decide) (by decide)
  case M12 =>
    exact not_hallTwoArith_card_of_mulEquiv θ (e := 6) (h := 1485)
      (CFSG.Sporadic.Mathieu.card_M12.trans (by norm_num)) (by decide) (by decide)
  case M22 =>
    exact not_hallTwoArith_card_of_mulEquiv θ (e := 7) (h := 3465)
      (CFSG.Sporadic.Mathieu.card_M22.trans (by norm_num)) (by decide) (by decide)
  case M23 =>
    exact not_hallTwoArith_card_of_mulEquiv θ (e := 7) (h := 79695)
      (CFSG.EvenSmallLie.CatalogOrders.card_M23.trans (by norm_num)) (by decide) (by decide)
  case M24 =>
    exact not_hallTwoArith_card_of_mulEquiv θ (e := 10) (h := 239085)
      (CFSG.Sporadic.Mathieu.card_M24.trans (by norm_num)) (by decide) (by decide)
  case J1 =>
    exact not_hallTwoArith_card_of_mulEquiv θ (e := 3) (h := 21945)
      (CFSG.Sporadic.J1.card_J1.trans (by norm_num)) (by decide) (by decide)
  case J2 =>
    exact not_hallTwoArith_card_of_mulEquiv θ (e := 7) (h := 4725)
      (CFSG.Sporadic.J2.card_J2.trans (by norm_num)) (by decide) (by decide)
  case J3 =>
    exact not_hallTwoArith_card_of_mulEquiv θ (e := 7) (h := 392445)
      (CFSG.Sporadic.J3.card_J3.trans (by norm_num)) (by decide) (by decide)
  case J4 =>
    exact not_hallTwoArith_card_of_mulEquiv θ (e := 21) (h := 41377816699065)
      (CFSG.Sporadic.J4.card_J4.trans (by norm_num)) (by decide) (by decide)
  case HS =>
    exact not_hallTwoArith_card_of_mulEquiv θ (e := 9) (h := 86625)
      (CFSG.Sporadic.HS.card_HS.trans (by norm_num)) (by decide) (by decide)
  case McL =>
    exact not_hallTwoArith_card_of_mulEquiv θ (e := 7) (h := 7016625)
      (CFSG.Sporadic.McL.card_McL.trans (by norm_num)) (by decide) (by decide)
  case He =>
    exact not_hallTwoArith_card_of_mulEquiv θ (e := 10) (h := 3935925)
      (CFSG.Sporadic.He.fam_he_order.1.trans (by norm_num)) (by decide) (by decide)
  case Ru =>
    exact not_hallTwoArith_card_of_mulEquiv θ (e := 14) (h := 8906625)
      (CFSG.Sporadic.Ru.card_Ru.trans (by norm_num)) (by decide) (by decide)
  case Suz =>
    exact not_hallTwoArith_card_of_mulEquiv θ (e := 13) (h := 54729675)
      (CFSG.Sporadic.Suz.card_Suz.trans (by norm_num)) (by decide) (by decide)
  case ONan =>
    exact not_hallTwoArith_card_of_mulEquiv θ (e := 9) (h := 900030285)
      (CFSG.Sporadic.ON.card_ON.trans (by norm_num)) (by decide) (by decide)
  case Co1 =>
    exact not_hallTwoArith_card_of_mulEquiv θ (e := 21) (h := 1982582476875)
      (CFSG.Sporadic.Co1.card_Co1.trans (by norm_num)) (by decide) (by decide)
  case Co2 =>
    exact not_hallTwoArith_card_of_mulEquiv θ (e := 18) (h := 161382375)
      (CFSG.Sporadic.Co2.card_Co2.trans (by norm_num)) (by decide) (by decide)
  case Co3 =>
    exact not_hallTwoArith_card_of_mulEquiv θ (e := 10) (h := 484147125)
      (CFSG.Sporadic.Co3.card_Co3.trans (by norm_num)) (by decide) (by decide)
  case Fi22 =>
    exact not_hallTwoArith_card_of_mulEquiv θ (e := 17) (h := 492567075)
      (CFSG.Sporadic.Fi22.card_Fi22.trans (by norm_num)) (by decide) (by decide)
  case Fi23 =>
    exact not_hallTwoArith_card_of_mulEquiv θ (e := 18) (h := 15600091832325)
      (CFSG.Sporadic.Fi23.card_Fi23.trans (by norm_num)) (by decide) (by decide)
  case Fi24Prime =>
    exact not_hallTwoArith_card_of_mulEquiv θ (e := 21) (h := 598528723330813275)
      (CFSG.Sporadic.Fi24.card_Fi24prime.trans (by norm_num)) (by decide) (by decide)
  case HN =>
    exact not_hallTwoArith_card_of_mulEquiv θ (e := 14) (h := 16664484375)
      (CFSG.Sporadic.HN.card_HN.trans (by norm_num)) (by decide) (by decide)
  case Ly =>
    exact not_hallTwoArith_card_of_mulEquiv θ (e := 8) (h := 202207730484375)
      (CFSG.Sporadic.Ly.card_Ly.trans (by norm_num)) (by decide) (by decide)
  case Th =>
    have hTh : Nat.card Th = 90745943887872000 := by
      have hJ : Nat.card CFSG.Sporadic.Th.J = 90745943887872000 :=
        CFSG.Sporadic.Th.Kernel.card_J_eq CFSG.Sporadic.Th.th_kernel_facts
      rw [Nat.card_congr CFSG.Sporadic.Th.thEquivJ.toEquiv, hJ]
    exact not_hallTwoArith_card_of_mulEquiv θ (e := 15) (h := 2769346432125)
      (hTh.trans (by norm_num)) (by decide) (by decide)
  case B =>
    exact not_hallTwoArith_card_of_mulEquiv θ (e := 41) (h := 1889375872099856765625)
      (CFSG.Monster.Existence.card_nativeB.trans (by norm_num [CFSG.Open.monsterBabyOrder]))
      (by decide) (by decide)
  case M =>
    exact not_hallTwoArith_of_eq (e := 46) (h := 11482618231106483731969943632999939453125)
      ((card_of_mulEquiv_nativeM θ).trans (by norm_num [CFSG.Open.monsterOrder])) (by decide)
      (by decide)

end Sporadic

end CFSG.SeitzReduction.RankOne
