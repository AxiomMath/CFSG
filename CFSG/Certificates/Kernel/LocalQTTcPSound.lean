module

public import Certificates.Data.Kernel.LocalQT.TcP
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42J2Multi
import CFSG.Certificates.Kernel.LocalQTTcPProved
public import CFSG.Certificates.Kernel.Spor.RawDefs

public section

namespace CFSG.KC.LQT.TC

open CFSG.KS.Raw CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.Bridge.J2Excl

@[expose] noncomputable def unpackP (n w : Nat) (L LI : List Nat) : List PArr :=
  (L.zip LI).map fun p => (unpack n w p.1, unpack n w p.2)

theorem mcP_sound {n w : Nat} {G GI TS TIS : List Nat} {ws : List (List Int)}
    {prog : List (Int × Int)} {targets : List Nat}
    (h : mcP n w G GI TS TIS ws prog targets = true) :
    multiConjCheck n (unpackP n w G GI) (unpackP n w TS TIS) ws prog
      (targets.map (unpack n w)) = true := by
  exact CFSG.KC.LQT.TCP.mcP_core h

theorem threeConj_eq_multi {n : Nat} {gens : List PArr} {t : PArr} {ws : List (List Int)}
    {prog : List (Int × Int)} {targets : List (Array Nat)} :
    threeConjCheck n gens t ws prog targets = multiConjCheck n gens [t] ws prog targets := by
  have e : (ws.flatMap fun w => [t].map fun t => pConj n (pWord n gens w) t) =
      ws.map fun w => pConj n (pWord n gens w) t := by
    induction ws with
    | nil => rfl
    | cons w ws ih =>
      rw [List.flatMap_cons, ih]
      rfl
  simp only [threeConjCheck, multiConjCheck, e]

theorem threeConj_of_mcP {n w : Nat} {G GI : List Nat} {T TI : Nat} {ws : List (List Int)}
    {prog : List (Int × Int)} {targets : List Nat}
    (h : mcP n w G GI [T] [TI] ws prog targets = true) :
    threeConjCheck n (unpackP n w G GI) (unpack n w T, unpack n w TI) ws prog
      (targets.map (unpack n w)) = true := by
  rw [threeConj_eq_multi]
  exact mcP_sound h

end CFSG.KC.LQT.TC

end
