module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelU43Arr
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutNative
public import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore
public import Certificates.Data.Kernel.J2Cover
public import Certificates.Data.Kernel.Misc.Oq
import CFSG.Certificates.Kernel.Misc.OqSound
import CFSG.Certificates.Kernel.Spor.PrimSound
import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.Child3Inv
import CFSG.Certificates.Kernel.Child3Cent
public import CFSG.Certificates.Kernel.Spor.RawDefs

public section

namespace CFSG.KC.Child3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.Monster.B.Co2.Native
open CFSG.Certificates.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.EvenSmallLie.Child3 CFSG.ComponentClassification.J2Cover

theorem eqA_unpackN {n w p q : Nat} (hp : canonK n w (mask w) (n * w) p = true)
    (hq : canonK n w (mask w) (n * w) q = true) :
    eqA n (unpack n w p) (unpack n w q) = Nat.beq p q := by
  cases h : Nat.beq p q
  · refine neK_sound ?_
    unfold neK
    rw [hp, hq, h]
  · exact eqK_sound h

theorem canon_pcN {n w p q : Nat} (hp : canonK n w (mask w) (n * w) p = true)
    (hq : canonK n w (mask w) (n * w) q = true) :
    canonK n w (mask w) (n * w) (pcomp n w (mask w) p q) = true :=
  canon_pcomp hp hq

theorem ordTest2_unpack {n w R : Nat} (hR : canonK n w (mask w) (n * w) R = true) :
    ordTest n 2 (arrTable n (unpack n w R)) =
      (Nat.beq (pcomp n w (mask w) R R) (pidn n w) && !Nat.beq R (pidn n w)) :=
  ordTest2_tabP hR

theorem centOK_sound {n w kS : Nat} {PS PSI FP FL FD : Nat → Nat} {S : Array (Array Nat)}
    {rs : List (Nat × List (List Int))} (hsz : szOK n w = true)
    (hnd : CFSG.KC.Misc.Oq.nodupK (rs.map Prod.fst) = true)
    (hS : S.size = kS ∧ ∀ j < kS, S[j]! = unpack n w (PS j))
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hst : rs.all (fun r => stabK n w PS PSI kS r.1 r.2) = true)
    (hf : forestK n w PS kS (rs.map Prod.fst) FP FL FD = true) :
    centOK n S rs = true :=
  centOK_of hsz (CFSG.KC.Misc.Oq.nodupK_sound hnd) hS hp hst hf

theorem allL_pos {CS : List Nat} (h : CFSG.KC.J2Cover.allL (fun c => Nat.blt 0 c) CS = true) :
    ∀ c ∈ CS, 0 < c := by
  induction CS with
  | nil => exact fun c hc => by simp at hc
  | cons x CS ih =>
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact Nat.blt_eq.mp h1
    · exact ih h2 c hc

theorem repsOK_sound {n w g N cap : Nat} {GP GIP CI E P L K S SI : Nat → Nat}
    {CS OFF : List Nat} {gens gensInv : Array Table} {X reps : List Table}
    (hg : gens.size = g ∧ gensInv.size = g ∧ ∀ l < g, gens[l]! = arrTable n (unpack n w (GP l)) ∧
      gensInv[l]! = arrTable n (unpack n w (GIP l)))
    (hgc : ∀ l < g, canonK n w (mask w) (n * w) (GP l) = true ∧
      canonK n w (mask w) (n * w) (GIP l) = true)
    (hreps : reps = (List.range CS.length).map fun i => arrTable n (unpack n w (E (lget OFF i))))
    (hoff : offOK CS OFF N = true)
    (hpos : CFSG.KC.J2Cover.allL (fun c => Nat.blt 0 c) CS = true) (hx : X.length = N)
    (h : ∀ j < N, repK n w GP GIP g CS OFF CI E P L K S SI N cap j = true) :
    repsOK n gens gensInv X reps cap = true :=
  repsOK_of_rec hg hgc hoff h (allL_pos hpos) hreps hx

theorem invList2_sound {n w kS BP : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat}
    (hb : Binds n w PS kS 2 BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS 2 BP) :
    (filterProducts n (ordTest n 2) (chainTables n S base) (idT n) []).length =
      invCount2 n w LR TR :=
  invList2_of hb hp hl

end CFSG.KC.Child3

end
