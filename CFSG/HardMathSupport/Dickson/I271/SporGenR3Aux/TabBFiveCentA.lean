module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBFiveCentTransport
public import Certificates.Certificate17562

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabBFiveCent

open CFSG.YGroups CFSG.YGroups.DCE CFSG.YGroups.DCE.B433

section Certified


theorem tabBFiveACard_holds
    : TabBFiveACard := by
  obtain ⟨θ⟩ := CFSG.Monster.Existence.nonempty_B433_mulEquiv_nativeB
  have hG : 4154781481226426191177580544000000 ≤ Nat.card B433 := by
    rw [Nat.card_congr θ.toEquiv]
    exact CFSG.Sporadic.Bridge.B.card_le_card_B
  obtain ⟨h5, h7, hle⟩ := Certificates.certificate17562 hG
  exact tabBFiveACard_of_B433 h5 h7 (hle.trans_lt (by norm_num))

end Certified

end CFSG.HardMathSupport.Dickson.I271.TabBFiveCent
