module

public import Certificates.Data.Kernel.Misc.T46
public import CFSG.Certificates.Kernel.Misc.T46Defs
import CFSG.Certificates.Kernel.Spor.PK.T46
public import CFSG.Certificates.Kernel.Misc.O73Defs

public section

namespace CFSG.KC.Misc.T46

open CFSG.F4.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.Sporadic.Fi22.Native

theorem t46_eq : t46SimpleCertificate () =
    t46G uPts wordStrings t46TvWords [30, 33, 16, 12, 9, 39, 39] [41, 46, 21, 23, 36] t46Base
      t46SubRoot := rfl

theorem t46_sound {U : Array Nat} {WS : List String} {TWd : Array (List Int)} {xw yw : List Int}
    {B : Array Nat} {r : Nat} {UL BL : List Nat} {UP : Nat} {GP LP O1 Pa1 La1 O2 Pa2 La2 : List Nat}
    {WC TW : List (List Nat)} (hU : U = UL.toArray) (hWS : WS = WC.map CFSG.KC.Misc.O73.strOf)
    (hTW : TWd = (TW.map (List.map Int.ofNat)).toArray) (hB : B = BL.toArray)
    (hp : ptsK UL UP = true) (hg : ∀ k < 46, gensOK UL UP GP k 1 = true)
    (hl : lettersK GP WC LP = true) (ht : treesK LP BL r O1 Pa1 La1 O2 Pa2 La2 = true)
    (hxy : xyK GP xw yw = true) (htv : ∀ k < 46, tvWordsK GP xw yw TW k 1 = true) :
    t46G U WS TWd xw yw B r = true :=
  CFSG.KS.PK.t46_sound' hU hWS hTW hB hp hg hl ht hxy htv

end CFSG.KC.Misc.T46

end
