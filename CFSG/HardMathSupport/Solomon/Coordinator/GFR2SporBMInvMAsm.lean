module

public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporBMInvM
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporBMInvHat
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporComp
public import CFSG.Sporadic.Bridge.MonsterModelsGriess
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFrontier
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterKleinFrontier
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThreeBFinal
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Fuse

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Monster.Generated CFSG.Monster.Existence CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier

section Assembly


theorem sporNoPumpup_M_of_uninverted
    (hSpM : SporadicMultipliers) (hOG : UniquenessMaximal.InputONGroup)
    (hOut : SporadicOuterLeTwo)
    (hU : ∀ s : Gmat, orderOf s = 3 → ¬ InvertedByTwoA s → ∀ K : Subgroup Gmat,
      CFSG.Open.IsComponentOf K (Subgroup.centralizer ({s} : Set Gmat)) →
      IsHatSix ↥K ∨ IsHatON ↥K → False) :
    SporNoPumpup .M := by
  haveI : Finite Gmat := generated_rational_group_finite_simple.2.2
  have hE := CFSG.Milestones.cl_lit_monster_existence_griess_conway
  obtain ⟨e1⟩ : Nonempty (Gmat ≃* (TauCeti.CFSGIndex.sporadic .M).Group) :=
    CFSG.Blueprint.NativeSporadic.MonsterModel.iso_gmat_tauCeti
  have e0 := e1.symm
  have φ := (CFSG.YGroups.Y443.griessEquivGmat CFSG.YGroups.Y443.Gmat_eq_AutO_of_stroth).symm
  haveI : Finite (TauCeti.CFSGIndex.sporadic .M).Group := Finite.of_equiv _ e1.toEquiv
  refine sporNoPumpup_of_components hSpM hOG hOut ?_ ?_ ?_ ?_
  · rw [← Nat.card_congr e1.toEquiv]
    exact CFSG.YGroups.Y443.natCard_Gmat_eq_monsterOrder
  · have hOm : OPrimeCoreTrivialAt 3 Gmat :=
      CFSG.HardMathSupport.Timmesfeld.SporadicBalance.oPrimeCoreTrivialAt_gmat_of_uninverted
        Nat.prime_three (by norm_num)
        (uninvertedOPrimeTrivial_gmat_of_twoAPureKlein Nat.prime_three (by norm_num)
          BThreeFi23.oPrimeCoreTrivialAt_B_three ThreeBNF.twoAPureKlein_three_Gmat)
    exact OPrimeCoreTrivialAt.of_mulEquiv e0 hOm
  · intro s hs K hK h
    have hh : IsHatSix ↥K ∨ IsHatON ↥K := h.elim Or.inl fun h => Or.inr h.2
    refine bmInv_false_of_hat_of_mulEquiv e0 hK hh ?_
    intro K' hK' h'
    have hs' := bmInv_orderOf_map e0 hs
    by_cases hinv : InvertedByTwoA (e0 s)
    · refine bmInv_false_of_hat_of_mulEquiv φ hK' h' ?_
      intro K'' hK'' h''
      exact false_of_isHat_of_invertedByTwoA hOG hE (bmInv_orderOf_map φ hs') (hinv.map φ) hK''
        h''
    · exact hU (e0 s) hs' hinv K' hK' h'
  · intro h
    exact absurd h (by decide)

end Assembly

end CFSG.HardMathSupport.Solomon.Coordinator
