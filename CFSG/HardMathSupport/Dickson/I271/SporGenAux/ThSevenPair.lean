module

public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.ThSeven
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.ThreeKill

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Sporadic.Th CFSG.Sporadic.SmallOddCore CFSG.EvenSporadicStandard.Solomon78
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Tables.Census CFSG.Blueprint CFSG.RankThree.PartTwo.Sec4

theorem sporPlaneKill_Th_seven
    (hOut : SporadicOuterLeTwo) : SporPlaneKill .Th 7 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Th.nonempty_mulEquiv
  have b₀ : NativeSporadic.Carrier .Th ≃* Spor .Th := b
  have bX : ↥JT ≃* Spor .Th := thJTEquiv.symm.trans b₀
  have h0 : ¬ SporadicOnePair .Th 7 := by decide
  have hoff := offPair_Th
  refine @sporPlaneKill_of_noSig_model hOut .Th 7 (by norm_num) (by norm_num) h0 ↥JT
    (Subgroup.toGroup JT) bX ?_ (NativeSporadic.Carrier .Th) _ b₀ hoff
  intro R Y hR hR9 hY3 hRY
  exact th7_noSig R hR hR9 Y ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hY3) hRY

theorem sporPair_Th_seven
    (hOut : SporadicOuterLeTwo) : SporPair .Th 7 :=
  sporPair_of_planeKill (sporPlaneKill_Th_seven hOut)

end CFSG.HardMathSupport.Dickson.I271
