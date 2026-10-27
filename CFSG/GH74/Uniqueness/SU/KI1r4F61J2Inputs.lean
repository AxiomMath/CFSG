module

public import Mathlib.Data.Nat.Notation
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheckInputs
public meta import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheckInputs
public meta import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore
public import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore

public section

namespace CFSG.GH74.Uniqueness.SU.K.R4.J2M

open CFSG.ComponentClassification.J2Cover CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Certificates.Native CFSG.Sporadic.Th.Native
@[expose] def wordArr (S : Array (Array ℕ)) : List ℕ → Array ℕ
  | [] => idA 315
  | i :: w => compA 315 S[i]! (wordArr S w)

@[expose] def pairCheck (rt U V : Array ℕ) : Bool :=
  isInvA 315 U (invCand 315 U) && isInvA 315 V (invCand 315 V) && inP U && inP V &&
    commA U rt && commA V rt && eqA 315 (compA 315 U U) (idA 315) &&
    eqA 315 (compA 315 V V) (idA 315) && !eqA 315 U (idA 315) && !eqA 315 V (idA 315) &&
    !eqA 315 U V && commA U V

end CFSG.GH74.Uniqueness.SU.K.R4.J2M

