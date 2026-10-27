module

public import Certificates.Data.Kernel.SporSch.J3F80
public import Certificates.Data.Kernel.SporSch.PairJ3Cert
public import CFSG.Certificates.Kernel.J4Q.Rep
public import CFSG.Certificates.Kernel.Spor.RawDefs
public import CFSG.Sporadic.Schreier.PairJ3FaithfulCheckInputs
import CFSG.Certificates.Kernel.SporSch.J3F80.Words
import CFSG.Certificates.Kernel.SporSch.J3F80.Core
import CFSG.Certificates.Kernel.SporSch.J3F80.Sep

public section

namespace CFSG.KS.SporSch.J3F

open CFSG.KC.Enum CFSG.KC.J4Q CFSG.KS CFSG.KS.SporSch CFSG.KS.Raw CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairF2 CFSG.Sporadic.Schreier.PairJ3
open CFSG.Sporadic.SmallF2.Native

theorem words_sound {cs : List (List Char)} {k : Nat} {F : Nat → Nat}
    (hasc : ∀ c ∈ cs, le70K c = true)
    (h : ∀ j < cs.length, wordsK F k (k * j) (cs.getD j []) = true) :
    ∀ r < k * cs.length, hexAt (String.ofList cs.flatten).toUTF8 (810 * r) 810 = F r := by
  exact WordsPf.words_sound' hasc h

variable {c rm one pad t0 t1 t2 t3 t4 t5 t6 : Nat}

theorem forms_sound (_hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {bytes : ByteArray}
    {S : Array (Array Nat)} {L1 L2 : List Nat} {F : Nat → Nat} {S0 S1 : Nat}
    (hF : ∀ r < 6156, hexAt bytes (810 * r) 810 = F r)
    (hS0 : S[0]! = unpack 6156 13 S0) (hS1 : S[1]! = unpack 6156 13 S1)
    (hL1 : rows80K L1 = true) (hL2 : rows80K L2 = true)
    (h : ∀ r < 6156, formsF c rm t0 t1 t2 t3 t4 t5 t6 usK dgK F S0 S1 (packRowsK L1)
      (trJ t0 t1 t2 t3 t4 t5 t6 (packRowsK L1)) (packRowsK L2)
      (trJ t0 t1 t2 t3 t4 t5 t6 (packRowsK L2)) r = true) :
    formsCheckWith bytes S L1.toArray L2.toArray = true := by
  exact CorePf.forms_sound' _hK hF hS0 hS1 hL1 hL2 h

theorem sort_sound {bytes : ByteArray} {F SG SGI : Nat → Nat}
    (hF : ∀ r < 6156, hexAt bytes (810 * r) 810 = F r) (h : sortK F SG SGI 6156 = true) :
    PairNative.strictInc (sortedWords bytes) = true := by
  exact WordsPf.sort_sound' hF h

theorem pull_sound (_hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {L : List Nat} {z : Nat}
    (hL : rows80K L = true) (hz : z < 2 ^ 3240)
    (h : Nat.beq (imgK c rm t0 t1 t2 t3 t4 t5 t6 usK dgK (packRowsK L)
      (trJ t0 t1 t2 t3 t4 t5 t6 (packRowsK L)) z) z = true) :
    pullOKZ 80 L.toArray z z = true := by
  exact CorePf.pull_sound' _hK hL hz h

theorem binv_sound (_hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {z RB : Nat}
    (hz : z < 2 ^ 3240)
    (h : Nat.beq (mulJ c rm RB (polarK t0 t1 t2 t3 t4 t5 t6 z)) dgK = true) :
    mulRows 80 (invRowsF2 80 (polarRowsZ 80 z)) (polarRowsZ 80 z) = idRows 80 := by
  exact CorePf.binv_sound' _hK hz h

theorem sep_sound (_hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {zB RB SI : Nat} {zs : List Nat}
    (hzs : zs.length = 4) (hzB : zB < 2 ^ 3240) (hz : ∀ z ∈ zs, z < 2 ^ 3240)
    (hP : rows80K sepP.toList = true)
    (h : sepK c rm t0 t1 t2 t3 t4 t5 t6 dgK zB RB zs sepTerms sepVec sepIdx (packRowsK sepP.toList)
      sepTree SI = true) :
    sepCheckWith (Array.ofFn fun r : Fin 4 =>
      mulRows 80 (invRowsF2 80 (polarRowsZ 80 zB)) (polarRowsZ 80 (zs.getD r.val 0))) = true := by
  exact SepPf.sep_sound' _hK hzs hzB hz hP h

end CFSG.KS.SporSch.J3F

end
