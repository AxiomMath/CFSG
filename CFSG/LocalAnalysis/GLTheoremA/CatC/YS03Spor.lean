module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS03Core
public import CFSG.HardMathSupport.Solomon.Coordinator.I19SporMathieu
public import CFSG.HardMathSupport.Timmesfeld.Proving.SporadicOuterLeTwo
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Assemble
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BFiveAClose
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Fuse
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1Five
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1Three
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3Three
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Sylow
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Pair
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.HNFiveOrders
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.LyFive
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.LyThree
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveGmat
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFrontier
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterKleinFrontier
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSeven
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenCensus
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThreeBFinal
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ONOuter
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ONWitness
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.RestSplit
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzThree
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThThreeClose
public import CFSG.LieType.SeitzGeneration.ExtSeitzG2Odd
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.HardMathSupport.Timmesfeld.Coordinator

open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.LieType.SeitzGeneration
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance
open CFSG.HardMathSupport.Timmesfeld.Tables.Census

theorem ys03_sporadicLocalOnePairs :
    SporadicLocalOnePairs :=
  sporadicLocalOnePairs_of_rest CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
        Proving.sporadicOuterLeTwo_holds
        (sporadicOneRest_of_split
          { Suz_three := sporadicOPrimeHolds_Suz_three, ONan_three := sporadicOPrimeHolds_ONan_three
            Co3_three := sporadicOPrimeHolds_Co3_three, Co2_three := sporadicOPrimeHolds_Co2_three
            Co1_three := sporadicOPrimeHolds_Co1_three, Fi22_three := sporadicOPrimeHolds_Fi22_three
            Fi23_three := sporadicOPrimeHolds_Fi23_three
            Fi24Prime_three := sporadicOPrimeHolds_Fi24_three
            Ly_three := sporadicOPrimeHolds_Ly_three, Th_three := sporadicOPrimeHolds_Th_three
            B_three := (sporadicOPrimeHolds_B_iff 3).2 BThreeFi23.oPrimeCoreTrivialAt_B_three
            M_three := sporadicOPrimeHolds_M_of_gmat
              (oPrimeCoreTrivialAt_gmat_of_uninverted Nat.prime_three (by norm_num)
                (uninvertedOPrimeTrivial_gmat_of_twoAPureKlein Nat.prime_three (by norm_num)
                  BThreeFi23.oPrimeCoreTrivialAt_B_three ThreeBNF.twoAPureKlein_three_Gmat))
            Co1_five := sporadicOPrimeHolds_Co1_five
            HN_five := sporadicOPrimeHolds_HN_five_of_orders hnFiveOrders_holds
            Ly_five := sporadicOPrimeHolds_Ly_five
            B_five := (sporadicOPrimeHolds_B_iff 5).2 oPrimeCoreTrivialAt_B_five
            M_five := sporadicOPrimeHolds_M_of_gmat
              (oPrimeCoreTrivialAt_gmat_of_uninverted Nat.prime_five (by norm_num)
                (uninvertedOPrimeTrivial_gmat_of_twoATwoCommuting Nat.prime_five (by norm_num)
                  oPrimeCoreTrivialAt_B_five sporadicOPrimeHolds_Co1_five
                  MonsterFiveGmat.twoATwoCommuting_five_Gmat))
            M_seven := sporadicOPrimeHolds_M_of_gmat
              (oPrimeCoreTrivialAt_seven_Gmat_of_classes MonsterSevenCensus.monsterSevenClasses) }
          { Suz_three := sporadicOuterHolds_Suz_three, ONan_three := sporadicOuterHolds_ONan_three
            Fi22_three := sporadicOuterHolds_Fi22_three
            Fi24Prime_three := sporadicOuterHolds_Fi24_three
            HN_five := sporadicOuterHolds_HN_five })

end CFSG.HardMathSupport.Timmesfeld.Coordinator

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.Open CFSG.Blueprint


theorem ys03_oneBalanced_M11
    {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hnab : ∃ a b : S, a * b ≠ b * a)
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.M11).Group)) :
    IsLocallyOneBalancedAbs 3 S := by
  have hcen : Subgroup.center S = ⊥ := by
    have := hS
    exact center_eq_bot_of_isSimpleGroup hnab
  obtain ⟨h1, h2⟩ := CFSG.HardMathSupport.Solomon.Coordinator.sporadicOnePairHolds_M11_three
  have he' : Nonempty (S ≃* NativeSporadic.Carrier TauCeti.SporadicName.M11) :=
    ⟨he.some.trans
      (CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group TauCeti.SporadicName.M11).some.symm⟩
  have := hS
  exact isLocallyOneBalancedAbs_of_parts Nat.prime_three (by norm_num) hcen
    (CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds S hS hnab
      TauCeti.SporadicName.M11 he) (h1 S he') (h2 S he')

theorem ys03_weak_of_sporadicOPrime
    {name : TauCeti.SporadicName} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hO : SporadicOPrimeHolds name p) {S : Type} [Group S] [Finite S]
    (hS : IsSimpleGroup S) (hnab : ∃ a b : S, a * b ≠ b * a)
    (e : S ≃* (TauCeti.CFSGIndex.sporadic name).Group) {A : Subgroup (MulAut S)}
    (hA : CFSG.Open.IsElemAbelian p A) :
    CFSG.LocalAnalysis.GLTheoremA.IsTwoPrimaryWeaklyLocallyBalanced p 1 A := by
  have hcen : Subgroup.center S = ⊥ := by
    have := hS
    exact center_eq_bot_of_isSimpleGroup hnab
  have hOut := CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds S hS hnab name ⟨e⟩
  have he' : Nonempty (S ≃* NativeSporadic.Carrier name) :=
    ⟨e.trans (CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group name).some.symm⟩
  have := hS
  exact CFSG.LocalAnalysis.GLTheoremA.ys03_weak_of_oPrime hp hcen
    (fun y hy => CFSG.LocalAnalysis.GLTheoremA.ys03_inner_of_pow_of_outer_le_two hp hp2 hOut hy)
    (hO S he') hA

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
