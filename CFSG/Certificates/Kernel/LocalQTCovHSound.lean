module

public import Certificates.Data.Kernel.LocalQT.CovH
public import CFSG.Certificates.Kernel.Spor.RawDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.HSCoverCheck

import CFSG.Certificates.Kernel.LocalQTCovHParse
import CFSG.Certificates.Kernel.LocalQTCovHElts
import CFSG.Certificates.Kernel.LocalQTCovHEqns

public section

namespace CFSG.KC.LQT.Cov

open CFSG.QuasithinUnique.Ch1.HSCover CFSG.Sporadic.Schreier

theorem covH_sound (cs : List Char) (P : List ℕ) (H : List (List ℕ)) (nV0 : ℕ) (A B : ℕ)
    (hA : hsStrongArrs[0]! = CFSG.KS.Raw.unpack 3850 12 A)
    (hB : hsStrongArrs[1]! = CFSG.KS.Raw.unpack 3850 12 B)
    (h1 : covHA 3850 12 A B cs P nV0 = true) (h2 : covHB cs H = true) :
    covCheck (parseData (String.ofList cs)) = true ∧ (parseData (String.ofList cs)).nV = nV0 := by
  cases hp : parseH cs with
  | none =>
    rw [covHA, hp] at h1
    exact absurd h1 Bool.false_ne_true
  | some D =>
    obtain ⟨hxw, hwords, hletters, hpd⟩ := CFSG.KC.LQT.Cov.H.parseH_sound hp
    obtain ⟨hgood, hpairs, hanchors, hnv0, hn⟩ :=
      CFSG.KC.LQT.Cov.H.covHA_sound hp hxw hwords hletters hA hB h1
    obtain ⟨hvalid, hge⟩ := CFSG.KC.LQT.Cov.H.covHB_sound hp hletters hn h2
    rw [hpd]
    refine ⟨?_, hnv0⟩
    simp only [covCheck, Bool.and_eq_true]
    exact ⟨⟨⟨⟨hgood, hpairs⟩, hanchors⟩, hvalid⟩, hge⟩

end CFSG.KC.LQT.Cov

end
