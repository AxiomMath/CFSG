module

public import CFSG.GF2Type.Smith1979W3.Cert690.Census.Main
public import CFSG.GF2Type.Smith1979W3.Cert690.Census.Elt

public section

namespace CFSG.GF2Type.Smith1979W3.Cert690

theorem grpFacts_of_censusBase {minus : Bool} (hb : censusBase minus () = true) :
    GrpFacts minus (grpData minus ()) := by
  have h : censusBaseOf minus (grpData minus ()) (ldata minus ()) = true := by
    unfold censusBase at hb
    exact hb
  have hg : groupOK minus (grpData minus ()) = true := by
    unfold censusBaseOf at h
    rw [Bool.and_eq_true] at h
    exact h.1
  exact grpFacts_of_groupOK hg

end CFSG.GF2Type.Smith1979W3.Cert690

end
