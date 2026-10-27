module

public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporBMInvB
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporBMInvHat
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporComp
import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Fuse

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Blueprint CFSG.Monster.GMS CFSG.Monster.Existence
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Assembly


open CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier

theorem sporNoPumpup_B_of_uninverted
    (hSpM : SporadicMultipliers) (hOG : UniquenessMaximal.InputONGroup)
    (hOut : SporadicOuterLeTwo) (hbr : SporadicBridges)
    (hU : ∀ s : NativeSporadic.B, orderOf s = 3 →
      (∀ d : NativeSporadic.B, BabyInv 0 d → d * s * d⁻¹ ≠ s⁻¹) →
      ∀ K : Subgroup NativeSporadic.B,
        CFSG.Open.IsComponentOf K (Subgroup.centralizer ({s} : Set NativeSporadic.B)) →
        IsHatSix ↥K → False) :
    SporNoPumpup .B := by
  haveI : Finite NativeSporadic.B := CFSG.Monster.B.Pinned.finite_B
  have e0 := (hbr .B).some.symm
  haveI : Finite (NativeSporadic.Carrier .B) := (inferInstance : Finite NativeSporadic.B)
  haveI : Finite (TauCeti.CFSGIndex.sporadic .B).Group := Finite.of_equiv _ e0.symm.toEquiv
  refine sporNoPumpup_of_components hSpM hOG hOut ?_ ?_ ?_ ?_
  · rw [Nat.card_congr e0.toEquiv]
    exact (card_nativeB : Nat.card NativeSporadic.B = _)
  · have hO3 : OPrimeCoreTrivialAt 3 NativeSporadic.B := BThreeFi23.oPrimeCoreTrivialAt_B_three
    exact OPrimeCoreTrivialAt.of_mulEquiv e0 hO3
  · intro s hs K hK h
    rcases h with h | ⟨h, -⟩
    · have hs' := bmInv_orderOf_map e0 hs
      refine bmInv_false_of_hatSix_of_mulEquiv e0 hK h ?_
      intro K' hK' h'
      let s' : NativeSporadic.B := e0 s
      have hs'' : orderOf s' = 3 := hs'
      by_cases hinv : ∃ d : NativeSporadic.B, BabyInv 0 d ∧ d * s' * d⁻¹ = s'⁻¹
      · obtain ⟨d, hd, hdx⟩ := hinv
        exact false_of_isHatSix_of_inverted_B hs'' hd hdx hK' h'
      · exact hU s' hs'' (fun d hd hdx => hinv ⟨d, hd, hdx⟩) K' hK' h'
    · exact absurd h (by decide)
  · intro h
    exact absurd h (by decide)

end Assembly

end CFSG.HardMathSupport.Solomon.Coordinator
