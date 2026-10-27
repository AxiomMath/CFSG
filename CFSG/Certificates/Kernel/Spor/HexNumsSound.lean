module

public import Certificates.Data.Kernel.Spor.HexNums
public import CFSG.Sporadic.FischerOddCore.Fi24R2Data
import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.Spor.HexText
public import CFSG.Certificates.Kernel.Spor.RawDefs

public section

namespace CFSG.KS.HexNums

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PackFld CFSG.KS.HexText
open CFSG.Sporadic.FischerOddCore

private theorem char_le (c d : Char) : (c ≤ d) ↔ c.toNat ≤ d.toNat := UInt32.le_iff_toNat_le

private theorem hexL_ite (c : Nat) : hexL c = if c < 48 then 16 else if c < 58 then c - 48 else
    if c < 97 then 16 else if c < 103 then c - 87 else 16 := by
  unfold hexL
  rw [blt_dec, blt_dec, blt_dec, blt_dec, nrec_dec, nrec_dec, nrec_dec, nrec_dec]
  rfl

private theorem hexL_eq (c : Char) : hexL c.toNat = hexVal c := by
  rw [hexL_ite]
  have hd : c.isDigit = true ↔ 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
    unfold Char.isDigit
    simp only [Bool.and_eq_true, decide_eq_true_eq, UInt32.le_iff_toNat_le]
    rfl
  have ha : ('a' ≤ c ∧ c ≤ 'f') ↔ 97 ≤ c.toNat ∧ c.toNat ≤ 102 := by
    rw [char_le, char_le]
    rfl
  unfold hexVal
  simp only [hd, ha]
  repeat' split
  all_goals omega

private def hstep (d : Nat) (acc : Array Nat × Nat × Nat) (c : Char) : Array Nat × Nat × Nat :=
  let v := hexVal c
  if v < 16 then
    if acc.2.2 + 1 = d then (acc.1.push (acc.2.1 * 16 + v), 0, 0)
    else (acc.1, acc.2.1 * 16 + v, acc.2.2 + 1)
  else acc

private theorem hexNums_eq (d : Nat) (cs : List Char) :
    hexNums d (String.ofList cs) = (cs.foldl (hstep d) (#[], 0, 0)).1 := by
  unfold hexNums
  rw [String.foldl_eq_foldl_toList, String.toList_ofList]
  rfl

private noncomputable def stepH (d w : Nat) (ch : Char) (ih : Nat → Nat → Nat → Nat → Bool)
    (k t v acc : Nat) : Bool :=
  strictB (hexL (Char.toNat ch)) (fun h =>
    bIf(Nat.blt h (nat_lit 16),
      strictB (Nat.add (Nat.mul v (nat_lit 16)) h) (fun v' =>
      bIf(Nat.beq (Nat.succ t) d,
        bIf(Nat.blt v' (Nat.shiftLeft (nat_lit 1) w),
          ih (Nat.succ k) (nat_lit 0) (nat_lit 0) (Nat.lor acc (Nat.shiftLeft v' (Nat.mul w k))),
          false),
        ih k (Nat.succ t) v' acc)),
      ih k t v acc))

private theorem run_cons (d w N F : Nat) (ch : Char) (L : List Char) (k t v acc : Nat) :
    run d w N F (ch :: L) k t v acc = stepH d w ch (run d w N F L) k t v acc := rfl

private theorem run_nil (d w N F k t v acc : Nat) :
    run d w N F [] k t v acc = bAnd(Nat.beq k N, Nat.beq acc F) := rfl

section Steps

variable {d w : Nat} {ch : Char} {ih : Nat → Nat → Nat → Nat → Bool} {k t v acc : Nat}

private theorem stepH_skip (hh : Nat.blt (hexL (Char.toNat ch)) 16 = false) :
    stepH d w ch ih k t v acc = ih k t v acc := by
  unfold stepH
  rw [strictB_eqP]
  try dsimp only
  rw [hh]

private theorem stepH_dig (hh : Nat.blt (hexL (Char.toNat ch)) 16 = true)
    (ht : Nat.beq (Nat.succ t) d = false) :
    stepH d w ch ih k t v acc =
      ih k (Nat.succ t) (Nat.add (Nat.mul v 16) (hexL (Char.toNat ch))) acc := by
  unfold stepH
  rw [strictB_eqP]
  try dsimp only
  rw [hh]
  try dsimp only
  rw [strictB_eqP]
  try dsimp only
  rw [ht]

private theorem stepH_big (hh : Nat.blt (hexL (Char.toNat ch)) 16 = true)
    (ht : Nat.beq (Nat.succ t) d = true)
    (hv : Nat.blt (Nat.add (Nat.mul v 16) (hexL (Char.toNat ch))) (Nat.shiftLeft 1 w) = false) :
    stepH d w ch ih k t v acc = false := by
  unfold stepH
  rw [strictB_eqP]
  try dsimp only
  rw [hh]
  try dsimp only
  rw [strictB_eqP]
  try dsimp only
  rw [ht]
  try dsimp only
  rw [hv]

private theorem stepH_ent (hh : Nat.blt (hexL (Char.toNat ch)) 16 = true)
    (ht : Nat.beq (Nat.succ t) d = true)
    (hv : Nat.blt (Nat.add (Nat.mul v 16) (hexL (Char.toNat ch))) (Nat.shiftLeft 1 w) = true) :
    stepH d w ch ih k t v acc =
      ih (Nat.succ k) 0 0 (Nat.lor acc
        (Nat.shiftLeft (Nat.add (Nat.mul v 16) (hexL (Char.toNat ch))) (Nat.mul w k))) := by
  unfold stepH
  rw [strictB_eqP]
  try dsimp only
  rw [hh]
  try dsimp only
  rw [strictB_eqP]
  try dsimp only
  rw [ht]
  try dsimp only
  rw [hv]

end Steps

private theorem push_get (arr : Array Nat) (x i : Nat) :
    (arr.push x)[i]! = if i < arr.size then arr[i]! else if i = arr.size then x else 0 := by
  by_cases h1 : i < arr.size
  · rw [iteT h1, getElem!_pos (arr.push x) i (by simp; omega), getElem!_pos arr i h1,
      Array.getElem_push_lt h1]
  · rw [iteF h1]
    by_cases h2 : i = arr.size
    · subst h2
      rw [iteT rfl, getElem!_pos (arr.push x) arr.size (by simp), Array.getElem_push_eq]
    · rw [iteF h2, getElem!_neg (arr.push x) i (by simp; omega)]
      rfl

private theorem run_sound (d w N F : Nat) : ∀ (L : List Char) (arr : Array Nat) (t v acc : Nat),
    Fld w acc (fun i => if i < arr.size then arr[i]! else 0) →
    (∀ i < arr.size, arr[i]! < 2 ^ w) →
    run d w N F L arr.size t v acc = true →
    (L.foldl (hstep d) (arr, v, t)).1 = unpack N w F := by
  intro L
  induction L with
  | nil =>
    intro arr t v acc hF hb hr
    rw [run_nil] at hr
    simp only [bAnd_iff] at hr
    have hN : arr.size = N := Nat.eq_of_beq_eq_true hr.1
    have hA : acc = F := Nat.eq_of_beq_eq_true hr.2
    subst hA
    rw [List.foldl_nil]
    apply Array.ext
    · simp [unpack, hN]
    · intro i h1 h2
      simp only [unpack, Array.getElem_ofFn]
      have hi : i < arr.size := h1
      rw [pg_of_fld hF (by rw [iteT hi]; exact hb i hi), iteT hi, getElem!_pos arr i hi]
  | cons ch L ih =>
    intro arr t v acc hF hb hr
    rw [run_cons] at hr
    rw [List.foldl_cons]
    have hL := hexL_eq ch
    cases hh : Nat.blt (hexL (Char.toNat ch)) 16
    · rw [stepH_skip hh] at hr
      have hn : ¬ hexVal ch < 16 := by
        rw [← hL]
        intro h
        rw [Nat.blt_eq.mpr h] at hh
        cases hh
      have e : hstep d (arr, v, t) ch = (arr, v, t) := by
        simp only [hstep, hn, ↓reduceIte]
      rw [e]
      exact ih arr t v acc hF hb hr
    · have hy : hexVal ch < 16 := by
        rw [← hL]
        exact Nat.blt_eq.mp hh
      cases ht : Nat.beq (Nat.succ t) d
      · rw [stepH_dig hh ht, hL] at hr
        have hn : ¬ t + 1 = d := false_of_beq ht
        have e : hstep d (arr, v, t) ch = (arr, v * 16 + hexVal ch, t + 1) := by
          simp only [hstep, hy, hn, ↓reduceIte]
        rw [e]
        exact ih arr (t + 1) _ acc hF hb hr
      · have ht' : t + 1 = d := Nat.eq_of_beq_eq_true ht
        cases hv : Nat.blt (Nat.add (Nat.mul v 16) (hexL (Char.toNat ch))) (Nat.shiftLeft 1 w)
        · rw [stepH_big hh ht hv] at hr
          cases hr
        · rw [stepH_ent hh ht hv, hL] at hr
          have hV : v * 16 + hexVal ch < 2 ^ w := by
            have := Nat.blt_eq.mp hv
            rw [hL, shl_eq, Nat.one_mul] at this
            exact this
          have e : hstep d (arr, v, t) ch = (arr.push (v * 16 + hexVal ch), 0, 0) := by
            simp only [hstep, hy, ht', ↓reduceIte]
          rw [e]
          have hs : (arr.push (v * 16 + hexVal ch)).size = Nat.succ arr.size := Array.size_push _
          refine ih _ 0 0 _ ?_ ?_ (by rw [hs]; exact hr)
          · refine fld_congr (fld_or hF (fld_shl arr.size (fld_one hV))) ?_
            intro i
            rw [hs, push_get]
            by_cases h1 : i < arr.size
            · have h2 : ¬ arr.size ≤ i := by omega
              have h3 : i < Nat.succ arr.size := by omega
              rw [iteT h1, iteF h2, iteT h3, iteT h1, Nat.or_zero]
            · by_cases h2 : i = arr.size
              · subst h2
                have h3 : arr.size < Nat.succ arr.size := by omega
                rw [iteF h1, iteT (Nat.le_refl arr.size), Nat.sub_self, iteT rfl, iteT h3, iteF h1,
                  iteT rfl, Nat.zero_or]
                rfl
              · have h3 : ¬ i < Nat.succ arr.size := by omega
                have h4 : i - arr.size ≠ 0 := by omega
                rw [iteF h1, iteF h3, Nat.zero_or]
                by_cases h5 : arr.size ≤ i
                · rw [iteT h5, iteF h4]
                · rw [iteF h5]
          · intro i hi
            rw [hs] at hi
            rw [push_get]
            by_cases h1 : i < arr.size
            · rw [iteT h1]
              exact hb i h1
            · have h2 : i = arr.size := by omega
              rw [iteF h1, iteT h2]
              exact hV


theorem hexNumsK_sound {cs : List Char} {d w N F : Nat} (h : hexNumsK cs d w N F = true) :
    hexNums d (String.ofList cs) = unpack N w F := by
  unfold hexNumsK at h
  simp only [bAnd_iff] at h
  rw [hexNums_eq]
  exact run_sound d w N F cs #[] 0 0 0 (fld_congr (fld_zero w) (fun i => by simp)) (by simp) h.2

theorem hexNums_of {s : String} {cs : List Char} {d w N F : Nat} (hs : s = String.ofList cs)
    (h : hexNumsK cs d w N F = true) : hexNums d s = unpack N w F := by
  rw [hs]
  exact hexNumsK_sound h

end CFSG.KS.HexNums

end
