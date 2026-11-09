module

public import Certificates.Data.Kernel.Misc.HexFlatR
import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.Spor.PK.Enc
import Mathlib.Tactic.Ring

public section

namespace CFSG.KC.Misc.HexFlat

open CFSG.KC.Enum CFSG.KS CFSG.KS.PackFld
open CFSG.KS.Text (hexV)

private noncomputable def stepHR (d n w N : Nat) (F : Nat → Nat) (ch : Char)
    (ih : Nat → Nat → Nat → Nat → Nat → Bool) (j e t v acc : Nat) : Bool :=
  bIf(Nat.beq j N, true,
    strictB (hexV (Char.toNat ch)) (fun h => bIf(Nat.blt h (nat_lit 16),
      strictB (Nat.add (Nat.mul v (nat_lit 16)) h) (fun v' =>
      bIf(Nat.beq (Nat.succ t) d,
        bIf(Nat.blt v' (Nat.shiftLeft (nat_lit 1) w),
          strictB (Nat.lor acc (Nat.shiftLeft v' (Nat.mul w e))) (fun acc' =>
            bIf(Nat.beq (Nat.succ e) n,
              bAnd(Nat.beq acc' (F j),
                ih (Nat.succ j) (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0)),
              ih j (Nat.succ e) (nat_lit 0) (nat_lit 0) acc')),
          false),
        ih j e (Nat.succ t) v' acc)),
      false)))

private theorem runHexR_cons' (d n w N : Nat) (F : Nat → Nat) (ch : Char) (L : List Char)
    (j e t v acc : Nat) :
    run d n w N F (ch :: L) j e t v acc = stepHR d n w N F ch (run d n w N F L) j e t v acc := rfl

section Steps

variable {d n w N : Nat} {F : Nat → Nat} {ch : Char} {ih : Nat → Nat → Nat → Nat → Nat → Bool}
  {j e t v acc : Nat}

private theorem stepHR_end (hj : Nat.beq j N = true) :
    stepHR d n w N F ch ih j e t v acc = true := by
  unfold stepHR
  rw [hj]

private theorem stepHR_dig (hj : Nat.beq j N = false)
    (hh : Nat.blt (hexV (Char.toNat ch)) 16 = true) (ht : Nat.beq (Nat.succ t) d = false) :
    stepHR d n w N F ch ih j e t v acc =
      ih j e (Nat.succ t) (Nat.add (Nat.mul v 16) (hexV (Char.toNat ch))) acc := by
  unfold stepHR
  rw [hj]
  try dsimp only
  rw [strictB_eqP]
  try dsimp only
  rw [hh]
  try dsimp only
  rw [strictB_eqP]
  try dsimp only
  rw [ht]

private theorem stepHR_ent (hj : Nat.beq j N = false)
    (hh : Nat.blt (hexV (Char.toNat ch)) 16 = true) (ht : Nat.beq (Nat.succ t) d = true)
    (hv : Nat.blt (Nat.add (Nat.mul v 16) (hexV (Char.toNat ch))) (Nat.shiftLeft 1 w) = true)
    (he : Nat.beq (Nat.succ e) n = false) :
    stepHR d n w N F ch ih j e t v acc =
      ih j (Nat.succ e) 0 0
        (Nat.lor acc (Nat.shiftLeft (Nat.add (Nat.mul v 16) (hexV (Char.toNat ch))) (Nat.mul w e))) := by
  unfold stepHR
  rw [hj]
  try dsimp only
  rw [strictB_eqP]
  try dsimp only
  rw [hh]
  try dsimp only
  rw [strictB_eqP]
  try dsimp only
  rw [ht]
  try dsimp only
  rw [hv]
  try dsimp only
  rw [strictB_eqP]
  try dsimp only
  rw [he]

private theorem stepHR_tab (hj : Nat.beq j N = false)
    (hh : Nat.blt (hexV (Char.toNat ch)) 16 = true) (ht : Nat.beq (Nat.succ t) d = true)
    (hv : Nat.blt (Nat.add (Nat.mul v 16) (hexV (Char.toNat ch))) (Nat.shiftLeft 1 w) = true)
    (he : Nat.beq (Nat.succ e) n = true) :
    stepHR d n w N F ch ih j e t v acc =
      bAnd(Nat.beq (Nat.lor acc (Nat.shiftLeft (Nat.add (Nat.mul v 16) (hexV (Char.toNat ch)))
        (Nat.mul w e))) (F j), ih (Nat.succ j) 0 0 0 0) := by
  unfold stepHR
  rw [hj]
  try dsimp only
  rw [strictB_eqP]
  try dsimp only
  rw [hh]
  try dsimp only
  rw [strictB_eqP]
  try dsimp only
  rw [ht]
  try dsimp only
  rw [hv]
  try dsimp only
  rw [strictB_eqP]
  try dsimp only
  rw [he]

end Steps

private theorem land_lowHR (r w : Nat) : Nat.land r (Nat.sub (Nat.shiftLeft 1 w) 1) = r % 2 ^ w := by
  have h := CFSG.KS.PK.land_mask r w
  exact h

private theorem run_of_runHexR {d n w N : Nat} {F : Nat → Nat} :
    ∀ (cs : List Char) (j e t v acc rest : Nat), F j = acc + 2 ^ (w * e) * rest →
      acc < 2 ^ (w * e) → runHexR d n w N F cs j e t v rest = true →
      run d n w N F cs j e t v acc = true
  | [], _, _, _, _, _, _, _, _, h => h
  | ch :: L, j, e, t, v, acc, rest, hF, hacc, h => by
    rw [runHexR_cons']
    change stepHexR d n w N F ch (runHexR d n w N F L) j e t v rest = true at h
    cases hj : Nat.beq j N
    · cases hh : Nat.blt (hexV (Char.toNat ch)) 16
      · simp only [stepHexR, hj, hh] at h
        exact absurd h Bool.false_ne_true
      · cases ht : Nat.beq (Nat.succ t) d
        · rw [stepHR_dig hj hh ht]
          simp only [stepHexR, hj, hh, ht] at h
          exact run_of_runHexR L _ _ _ _ _ _ hF hacc h
        · cases hb : Nat.beq (Nat.add (Nat.mul v 16) (hexV (Char.toNat ch)))
              (Nat.land rest (Nat.sub (Nat.shiftLeft 1 w) 1))
          · simp only [stepHexR, hj, hh, ht, hb] at h
            exact absurd h Bool.false_ne_true
          · have hv : Nat.add (Nat.mul v 16) (hexV (Char.toNat ch)) = rest % 2 ^ w := by
              rw [← land_lowHR]
              exact Nat.eq_of_beq_eq_true hb
            have hvlt : Nat.blt (Nat.add (Nat.mul v 16) (hexV (Char.toNat ch)))
                (Nat.shiftLeft 1 w) = true := by
              have e1 : Nat.shiftLeft 1 w = 2 ^ w := Nat.one_shiftLeft w
              rw [hv, Nat.blt_eq, e1]
              exact Nat.mod_lt _ (Nat.two_pow_pos w)
            have hacc' : Nat.lor acc (Nat.shiftLeft (Nat.add (Nat.mul v 16) (hexV (Char.toNat ch)))
                (Nat.mul w e)) = acc + rest % 2 ^ w * 2 ^ (w * e) := by
              rw [hv]
              exact CFSG.KS.PK.lor_shiftLeft_eq_add hacc
            have hdm := Nat.mod_add_div rest (2 ^ w)
            have e2 : Nat.shiftRight rest w = rest / 2 ^ w := Nat.shiftRight_eq_div_pow rest w
            have hpw : 2 ^ (w * Nat.succ e) = 2 ^ (w * e) * 2 ^ w := by
              rw [Nat.mul_succ, Nat.pow_add]
            cases he : Nat.beq (Nat.succ e) n
            · rw [stepHR_ent hj hh ht hvlt he]
              simp only [stepHexR, hj, hh, ht, hb, he] at h
              refine run_of_runHexR L _ _ _ _ _ _ ?_ ?_ h
              · rw [hacc', hpw, e2, hF]
                conv_lhs => rw [← hdm]
                ring
              · rw [hacc', hpw]
                have h1 : rest % 2 ^ w + 1 ≤ 2 ^ w := Nat.mod_lt _ (Nat.two_pow_pos w)
                have h2 : (rest % 2 ^ w + 1) * 2 ^ (w * e) ≤ 2 ^ w * 2 ^ (w * e) :=
                  Nat.mul_le_mul_right _ h1
                rw [Nat.add_mul, Nat.one_mul] at h2
                rw [Nat.mul_comm (2 ^ (w * e)) (2 ^ w)]
                omega
            · rw [stepHR_tab hj hh ht hvlt he]
              cases hz : Nat.beq (Nat.shiftRight rest w) 0
              · simp only [stepHexR, hj, hh, ht, hb, he, hz] at h
                exact absurd h Bool.false_ne_true
              · simp only [stepHexR, hj, hh, ht, hb, he, hz] at h
                have hz' : rest / 2 ^ w = 0 := by
                  rw [← e2]
                  exact Nat.eq_of_beq_eq_true hz
                have hr : rest % 2 ^ w = rest := by
                  rw [Nat.mod_eq_of_lt]
                  exact (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos w)).1 hz'
                have hq : Nat.beq (Nat.lor acc (Nat.shiftLeft (Nat.add (Nat.mul v 16)
                    (hexV (Char.toNat ch))) (Nat.mul w e))) (F j) = true := by
                  rw [hacc', hr, hF, Nat.mul_comm rest]
                  exact Nat.beq_refl _
                rw [hq]
                refine run_of_runHexR L _ _ _ _ _ _ ?_ ?_ h
                · rw [Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add]
                · rw [Nat.mul_zero, Nat.pow_zero]
                  exact Nat.zero_lt_one
    · exact stepHR_end hj

theorem hexFlat_of_hexFlatR {cs : List Char} {d n w N : Nat} {F : Nat → Nat}
    (h : hexFlatR cs d n w N F = true) : hexFlat cs d n w N F = true := by
  unfold hexFlatR at h
  unfold hexFlat
  cases hd : Nat.blt 0 d
  · simp only [hd] at h
    exact absurd h Bool.false_ne_true
  · cases hn : Nat.blt 0 n
    · simp only [hd, hn] at h
      exact absurd h Bool.false_ne_true
    · simp only [hd, hn] at h
      exact run_of_runHexR cs 0 0 0 0 0 (F 0) (by rw [Nat.mul_zero, Nat.pow_zero, Nat.one_mul,
        Nat.zero_add]) (by rw [Nat.mul_zero, Nat.pow_zero]; exact Nat.zero_lt_one) h

end CFSG.KC.Misc.HexFlat

end
