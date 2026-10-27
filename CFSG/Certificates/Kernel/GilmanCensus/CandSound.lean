module

public import CFSG.Certificates.Kernel.GilmanCensus.RunProg
public import CFSG.Certificates.Kernel.GilmanCensus.ZerosSound
import all Certificates.Data.Census
public import CFSG.Certificates.Kernel.GilmanCensus.LabelSound
public import CFSG.Certificates.Kernel.GilmanCensus.XrepsSound
public import Certificates.Data.Kernel.GilmanCensus.DataOk

public section

namespace Certificates.GilmanCensusK

open Certificates.Census Std

structure Ctx (dt : Data) (dk : DK) : Prop where
  rel : Rel dt dk
  zp : zpOkK dk = true
  ok : dataOkK dk = true

theorem Ctx.F3 {dt : Data} {dk : DK} (C : Ctx dt dk) : ∀ r ∈ dk.F, ∀ x ∈ r, x < 3 := by
  have h := C.ok
  unfold dataOkK at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1

theorem zeros_rel {dt : Data} {dk : DK} (C : Ctx dt dk) (v : Array Nat) :
    zerosOf dt v = zerosK dk v.toList := zerosOf_eq_K C.rel C.zp C.F3 v

theorem foldl_ifbit_lt (N : Nat) (p : Nat → Bool) : ∀ (l : List Nat) (acc : Nat), acc < 2 ^ N →
    (∀ i ∈ l, i < N) → l.foldl (fun m i => if p i = true then m ||| bitK i else m) acc < 2 ^ N
  | [], _, h, _ => h
  | i :: l, acc, h, hl => by
    rw [List.foldl_cons]
    apply foldl_ifbit_lt N p l _ _ (fun j hj => hl j (by simp [hj]))
    split
    · rw [bitK_eq_bit]
      exact or_bit_lt N acc i (hl i (by simp)) h
    · exact h

theorem zeros_lt {dt : Data} {dk : DK} (C : Ctx dt dk) (v : Array Nat) : zerosOf dt v < 2 ^ dk.N := by
  rw [zerosOf_eq C.rel]
  unfold zerosL
  exact foldl_ifbit_lt dk.N _ _ 0 (Nat.two_pow_pos _) (fun i hi => by
    simp only [List.mem_range'] at hi
    omega)

theorem compsK_lt (dk : DK) (m : Nat) (hm : m < 2 ^ dk.N) : ∀ c ∈ compsK dk.adj m, c < 2 ^ dk.N :=
  compsA_lt dk.adj dk.N 128 m hm

@[expose] def candK (dk : DK) (x : List Nat) (zx L J : Nat) (z : List Nat) (K : Nat) : Option Cand :=
  if (J &&& (K ^^^ dk.full)) != 0 then none
  else if solvableK dk K then none
  else if (K &&& (zx ^^^ dk.full)) == 0 then none
  else
    let kk := kernelK dk K
    if kk.length > 2 then none else
    let md := if kk.length == 1 then modelK dk L K else (false, false)
    let t1 := twonodeK dk L J && !internalK dk L x
    let t2 := twonodeK dk K J && !internalK dk K z
    some (z, K, md.1, t1 || t2, md.2, kk)

theorem candsAt_eq (dk : DK) (x : List Nat) (zx L J : Nat) (z : List Nat) :
    candsAt dk x zx L J z = (compsK dk.adj (zerosK dk z)).filterMap (candK dk x zx L J z) := rfl

@[expose] def cv (c : Cand) : C4 := (c.1.toArray, c.2.1, c.2.2.1, c.2.2.2.1)

theorem arr_beq_toList (a b : Array Nat) : (a == b) = (a.toList == b.toList) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, Array.toList_inj]

@[expose] def candsL (dk : DK) (x : List Nat) (zx L J : Nat) (zs : List (List Nat)) : List Cand :=
  (zs.filter (· != x)).flatMap (candsAt dk x zx L J)

end Certificates.GilmanCensusK

end
