module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.LyFive
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.McLThree
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.SporRec
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Assemble
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Blueprint CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.ComponentBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Tables.Census

section LyFive

theorem sporPair_Ly_five (hOut : SporadicOuterLeTwo)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hBr : SporadicBridges) : SporPair .Ly 5 := by
  intro X _ _ hX K B hH hN hS hF hO
  right
  have hq : CFSG.Open.IsQuasisimple ↥K := i116e_isQuasisimple hH.core hH.comp
  have hZ : Subgroup.center ↥K = ⊥ := center_eq_bot_of_five_le hSpM hH (le_refl 5) hS
  obtain ⟨e⟩ := hS
  haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hq.2
  have hloc : IsLocallyOneBalancedAbs 5 (↥K ⧸ Subgroup.center ↥K) :=
    isLocallyOneBalancedAbs_Ly_five hOut hBr _ hq.2 (exists_noncomm_of_isQuasisimple hq) ⟨e⟩
  let eK : ↥K ≃* NativeSporadic.Carrier .Ly :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans
      (e.trans (hBr .Ly).some.symm)
  refine strong_of_constrained hOut hH hN ⟨e⟩ hloc ?_
  intro k hkZ hkp
  have hk1 : k ^ 5 = 1 := by
    rw [hZ] at hkp
    exact Subgroup.mem_bot.1 hkp
  have hk : k ≠ 1 := fun h => hkZ (h ▸ Subgroup.one_mem _)
  exact pConstrainedShape_Ly_five ↥K ⟨eK⟩ (orderOf_eq_prime hk1 hk)

end LyFive

section LeafPairs

theorem sporPair_Th_three (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges)
    (hP : SporadicOnePairHolds .Th 3) (hChev : ChevStrong 3) (hD : LeafShape .Th 3) :
    SporPair .Th 3 :=
  sporPair_of_leafShape_cover hOut hBr hP hChev hD

theorem sporPair_Fi23_three (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges)
    (hP : SporadicOnePairHolds .Fi23 3) (hChev : ChevStrong 3) (hD : LeafShape .Fi23 3) :
    SporPair .Fi23 3 :=
  sporPair_of_leafShape_cover hOut hBr hP hChev hD

theorem sporPair_HN_three (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges)
    (hP : SporadicOnePairHolds .HN 3) (hChev : ChevStrong 3) (hD : LeafShape .HN 3) :
    SporPair .HN 3 :=
  sporPair_of_leafShape_cover hOut hBr hP hChev hD

theorem sporPair_Co2_three (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges)
    (hP : SporadicOnePairHolds .Co2 3) (hChev : ChevStrong 3) (hD : LeafShape .Co2 3) :
    SporPair .Co2 3 :=
  sporPair_of_leafShape_cover hOut hBr hP hChev hD

theorem sporPair_Fi22_three (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges)
    (hP : SporadicOnePairHolds .Fi22 3) (hChev : ChevStrong 3) (hD : LeafShape .Fi22 3) :
    SporPair .Fi22 3 :=
  sporPair_of_leafShape_cover hOut hBr hP hChev hD

theorem sporPair_Fi24_three (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges)
    (hP : SporadicOnePairHolds .Fi24Prime 3) (hChev : ChevStrong 3)
    (hD : LeafShape .Fi24Prime 3) : SporPair .Fi24Prime 3 :=
  sporPair_of_leafShape_cover hOut hBr hP hChev hD

end LeafPairs

section McLPair

theorem sporStrong_McL_three (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges) :
    SporStrong .McL 3 :=
  sporStrong_of_constrainedShape hOut hBr sporadicOnePairHolds_McL
    (mcl_constrainedShape_three oPrimeCoreTrivialAt_McL)

theorem sporPair_McL_three (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges) :
    SporPair .McL 3 :=
  sporPair_of_sporStrong (sporStrong_McL_three hOut hBr)

theorem sporPair_Ly_three
    (hOut : SporadicOuterLeTwo)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hBr : SporadicBridges) (hP : SporadicOnePairHolds .Ly 3) (hChev : ChevStrong 3)
    (hD : CentShapeRk 3 (GoodSpor 3 [.McL]) (RkSpor 3 [.McL]) (NativeSporadic.Carrier .Ly)) :
    SporPair .Ly 3 :=
  sporPair_of_sporStrong
    (sporStrong_of_goodSporShape hOut hSpM hBr hP (by decide) hChev
      (fun S hS => by
        simp only [List.mem_singleton] at hS
        subst hS
        exact sporStrong_McL_three hOut hBr) hD)

theorem sporPair_Co1_three
    (hOut : SporadicOuterLeTwo)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hBr : SporadicBridges) (hP : SporadicOnePairHolds .Co1 3) (hChev : ChevStrong 3)
    (hSuz : SporStrong .Suz 3)
    (hD : CentShapeRk 3 (GoodSpor 3 [.Suz]) (RkSpor 3 [.Suz]) (NativeSporadic.Carrier .Co1)) :
    SporPair .Co1 3 :=
  sporPair_of_sporStrong
    (sporStrong_of_goodSporShape hOut hSpM hBr hP (by decide) hChev
      (fun S hS => by
        simp only [List.mem_singleton] at hS
        subst hS
        exact hSuz) hD)

end McLPair

end CFSG.HardMathSupport.Dickson.I271
