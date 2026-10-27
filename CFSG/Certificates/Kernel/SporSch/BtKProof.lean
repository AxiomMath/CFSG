module

public import CFSG.Certificates.Kernel.SporSch.ChainSProof

public section

namespace CFSG.KS.SporSch.MBT

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch.MOC
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu
open Finset

variable {n w : Nat} {PS PSI LR TR TRI : Nat → Nat} {kS nb BP NS CH : Nat}
  {S : Array (Array Nat)} {base : Array Nat} {D : List (List Int)} {gA gB : Equiv.Perm (Fin n)}

open scoped Classical

theorem btK_proved (hQ : ChainS n w PS PSI LR TR TRI kS 2 nb BP S base D NS CH)
    (hA : imageList gA = (unpack n w (PS 0)).toList)
    (hB : imageList gB = (unpack n w (PS 1)).toList) (hnd : base.toList.Nodup) (hk64 : nb ≤ 64)
    (x y : gen2 gA gB) {X Y : Nat}
    (hX : imageList (x : Equiv.Perm (Fin n)) = (unpack n w X).toList)
    (hY : imageList (y : Equiv.Perm (Fin n)) = (unpack n w Y).toList) :
    btK n w (mask w) (n * w) BP nb LR TR TRI X Y =
      #(univ.filter fun g : gen2 gA gB => g * x = y * g) := by
  obtain ⟨bv, hbv, hK, -, -, -⟩ := chainK_of_chainS hQ hA hB hnd
  have hn : 1 ≤ n := hQ.1.1
  have hV := (chainK_check hn hbv hK).1
  set Q := certificate hn [gA, gB] D bv hbv
  have hGK : Q.originalSubgroup = gen2 gA gB := orig_pair hn hbv
  rw [btK_eq hK hn hbv hk64 (prep_of_imageList hX) (prep_of_imageList hY),
    ← card_subtype_eq_countP Q.originalSubgroup _ (enumeration_nodup Q hV)
      (mem_enumeration_iff Q hV) (fun g => g * (x : Equiv.Perm (Fin n)) = y * g), hGK,
    Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  ext g
  simp [Subtype.ext_iff]

theorem btK_sound (hQ : ChainS n w PS PSI LR TR TRI kS 2 nb BP S base D NS CH)
    (hA : imageList gA = (unpack n w (PS 0)).toList)
    (hB : imageList gB = (unpack n w (PS 1)).toList) (hnd : base.toList.Nodup) (hk64 : nb ≤ 64)
    (x y : gen2 gA gB) {X Y : Nat}
    (hX : imageList (x : Equiv.Perm (Fin n)) = (unpack n w X).toList)
    (hY : imageList (y : Equiv.Perm (Fin n)) = (unpack n w Y).toList)
    (_hXc : canonK n w (mask w) (n * w) X = true) (_hYc : canonK n w (mask w) (n * w) Y = true) :
    btK n w (mask w) (n * w) BP nb LR TR TRI X Y =
      #(univ.filter fun g : gen2 gA gB => g * x = y * g) :=
  btK_proved hQ hA hB hnd hk64 x y hX hY

end CFSG.KS.SporSch.MBT

end
