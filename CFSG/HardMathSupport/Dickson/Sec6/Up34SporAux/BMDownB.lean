module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BMInvB
public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BMLeaves
import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BMNum

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.BM

open CFSG.Blueprint CFSG.Monster.GMS CFSG.Monster.Existence
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.HardMathSupport.Solomon.Coordinator.YS08

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Down


theorem sporL3DownInner_B_of_leaf (hbr : SporadicBridges) (hB : B3BLeaf) :
    SporL3DownInner .B := by
  haveI : Finite NativeSporadic.B := CFSG.Monster.B.Pinned.finite_B
  have hcard : Nat.card NativeSporadic.B = 4154781481226426191177580544000000 := by
    rw [card_nativeB, monsterBabyOrder_eq_numeral]
  have hM : Nonempty (NativeSporadic.B ≃* (TauCeti.CFSGIndex.sporadic .B).Group) := hbr .B
  have h1 := @sporL3DownInner_of_comp .B NativeSporadic.B inferInstance inferInstance hM
  refine h1 ?_ ?_
  · rw [hcard]
    exact noL3Eq_B
  · intro x hx
    by_cases hinv : ∃ d, BabyInv 0 d ∧ d * x * d⁻¹ = x⁻¹
    · obtain ⟨d, hd, hdx⟩ := hinv
      exact noL3Comp_B_of_inverted hx hd hdx
    · have hinv' : ∀ d : NativeSporadic.B, BabyInv 0 d → d * x * d⁻¹ ≠ x⁻¹ :=
        fun d hd h => hinv ⟨d, hd, h⟩
      exact noL3Comp_of_not_dvd (q := 7) (by norm_num) (by norm_num)
        (by rw [hcard]; exact noL3DvdPrime_B_seven) (hB x hx hinv')

end Down

end CFSG.HardMathSupport.Dickson.Sec6.BM
