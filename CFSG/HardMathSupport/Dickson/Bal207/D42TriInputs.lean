module

public import Certificates.Data.D42Triality
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.D42Inputs
public import CFSG.Quasithin.Recognition.CertU33PresInputs

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.D42Tri

open CFSG.EvenSmallLie.OmegaEight CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.SmallOddCore CFSG.ComponentClassification.J2Cover
  CFSG.Monster.B.Co2.Native CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.D42
  CFSG.HardMathSupport.Dickson.Bal207.D42TriData CFSG.Quasithin

@[expose] def tblAt (s : String) (j : ℕ) : Table := hexT 3 360 (360 * j) s

@[expose] def rhoTbl (_ : Unit := ()) : Table := arrTable 360 rhoArr

@[expose] def t2Tbl (_ : Unit := ()) : Table := tblAt repHex 0

@[expose] def p0Tbls (_ : Unit := ()) : List Table := (List.range 3).map (tblAt p0Hex)

@[expose] def p1Tbls (_ : Unit := ()) : List Table := p0Tbls () ++ [rhoTbl ()]

@[expose] def repConj (_ : Unit := ()) : List (Table × Table) :=
  (rhoTbl (), idT 360) :: (List.range 12).map fun j => (tblAt repHex j, tblAt conjHex j)

@[expose] def k2Tbls (_ : Unit := ()) : List Table := (List.range 2).map (tblAt k2Hex)

@[expose] def l0Tbls (_ : Unit := ()) : List Table := (List.range 5).map (tblAt l0Hex)

@[expose] def omGT (_ : Unit := ()) : Array Table :=
  ((List.range 8).map fun i => arrTable 360 genArrs[i]!).toArray

@[expose] def omGI (_ : Unit := ()) : Array Table :=
  ((List.range 8).map fun i => arrTable 360 (invCand 360 genArrs[i]!)).toArray

@[expose] def inOmega (lv : Array Level) (T : Table) : Bool := permOK 360 T && siftOmega lv T

@[expose] def relTbl (L Li : Array Table) (w : List (Fin 5 × Bool)) : Table :=
  w.foldl (fun acc l => compT 360 acc (cond l.2 L[l.1.val]! Li[l.1.val]!)) (idT 360)

@[expose] def p1Check : Bool :=
  let lv := omegaLevels
  (p0Tbls ()).all (inOmega lv) &&
    (p1Tbls ()).all (fun g => permOK 360 g && invOK 360 g (invT 360 g)) &&
    enumOK 360 729 729 (p1Tbls ())

@[expose] def repOK (lv : Array Level) (R T : Table) (rc : Table × Table) : Bool :=
  let c := rc.2
  let ci := invT 360 c
  permOK 360 rc.1 && inOmega lv c && invOK 360 c ci &&
    (tblEq 360 (conjT 360 c ci rc.1) R || tblEq 360 (conjT 360 c ci rc.1) T)

@[expose] def clsCheck : Bool :=
  let lv := omegaLevels
  let R := rhoTbl ()
  let T := t2Tbl ()
  let A := (p1Tbls ()).toArray
  let Ai := A.map (invT 360)
  let E := (mulClosureH 360 A 729).1
  let cls := (repConj ()).map fun rc => (rc, conjClosureH 360 A Ai rc.1 729)
  permOK 360 T &&
    cls.all (fun c => repOK lv R T c.1 && conjTreeOK 360 A Ai c.1.1 c.2.1 c.2.2.1 c.2.2.2) &&
    E.all fun v => invOK 360 v (invT 360 v) &&
      (!tblEq 360 (compT 360 v (compT 360 v v)) (idT 360) || siftOmega lv v ||
        cls.any fun c => memT 360 c.2.1 v || memT 360 c.2.1 (invT 360 v))

@[expose] def l0Check : Bool :=
  let lv := omegaLevels
  let R := rhoTbl ()
  let L := (l0Tbls ()).toArray
  let Li := L.map (invT 360)
  (l0Tbls ()).all (fun g => inOmega lv g && invOK 360 g (invT 360 g) && commTT 360 g R) &&
    u33PresRels.all (fun w => tblEq 360 (relTbl L Li w) (idT 360)) &&
    !tblEq 360 L[0]! (idT 360)

@[expose] def k2Check : Bool :=
  let lv := omegaLevels
  let T := t2Tbl ()
  (k2Tbls ()).all (fun g => inOmega lv g && commTT 360 g T) && enumOK 360 216 216 (k2Tbls ())

@[expose] def rhoClassCheck : Bool :=
  let GT := omGT ()
  let GI := omGI ()
  let R := rhoTbl ()
  let c := conjClosureH 360 GT GI R 14400
  conjTreeOK 360 GT GI R c.1 c.2.1 c.2.2 && hkeysDistinct 360 c.1.toList &&
    decide (14400 ≤ c.1.size)

@[expose] def t2ClassCheck : Bool :=
  let GT := omGT ()
  let GI := omGI ()
  let T := t2Tbl ()
  let c := conjClosureH 120 GT GI T 203500
  conjTreeOK 120 GT GI T c.1 c.2.1 c.2.2 && hkeysDistinct 120 c.1.toList &&
    decide (403201 ≤ c.1.size)

end CFSG.HardMathSupport.Dickson.Bal207.D42Tri
