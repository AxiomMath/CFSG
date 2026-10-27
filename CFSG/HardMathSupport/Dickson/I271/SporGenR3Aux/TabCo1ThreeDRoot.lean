module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1PowBound
public import Certificates.Certificate17592

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeDRoot

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block CFSG.HardMathSupport.Dickson.I271.TabCo1


theorem threeD_root_bound :
    boundOK (colsOf (powList (rootRows3D ()) 3)) 3 base conds cnts span comb = true ∧
      cnts.prod ≤ 544320 := by
  have h := (Certificates.certificate17592 : rootCheck () = true)
  simpa only [rootCheck, Bool.and_eq_true, decide_eq_true_eq] using h

theorem card_cent_threeD_root_le (x : ↥GA)
    (hx : MRep (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T.Native.rootRows 2)
      (x : GL24)) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set ↥GA)) ≤ 544320 := by
  obtain ⟨hb, hp⟩ := threeD_root_bound
  have hcard := card_inf_GA_le_of_powBound (kR := rootRows3D ()) hx 3 hb
  rw [card_centralizer_GA_eq_inf]
  exact hcard.trans hp

end CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeDRoot
