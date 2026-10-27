module

import CFSG.Certificates.Kernel.GMS78RuSC.Basic
public import Certificates.Data.Kernel.GMS78RuSClo
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KC.GMS.SC

open CFSG.KLie.CT CFSG.KC.Loop

theorem fget_lor (a b j w : Nat) :
    fget (Nat.lor a b) j w = Nat.lor (fget a j w) (fget b j w) := by
  change ((a ||| b) >>> (j * w)) &&& (pw2 w - 1) =
    (((a >>> (j * w)) &&& (pw2 w - 1)) ||| ((b >>> (j * w)) &&& (pw2 w - 1)))
  rw [Nat.shiftRight_or_distrib, Nat.and_or_distrib_right]

theorem fget_shl {v w x y : Nat} (hv : v < 2 ^ w) :
    fget (Nat.shiftLeft v (Nat.mul w y)) x w = if x = y then v else 0 := by
  rw [fget_eq']
  change (v <<< (w * y)) / 2 ^ (x * w) % 2 ^ w = _
  rw [Nat.shiftLeft_eq]
  have hpos : 0 < 2 ^ w := Nat.two_pow_pos w
  split_ifs with h
  · subst h
    rw [Nat.mul_comm w x, Nat.mul_div_cancel v (Nat.two_pow_pos _)]
    exact Nat.mod_eq_of_lt hv
  · rcases Nat.lt_or_gt_of_ne h with hlt | hgt
    · obtain ⟨d, rfl⟩ : ∃ d, y = x + d + 1 := ⟨y - x - 1, by omega⟩
      have : v * 2 ^ (w * (x + d + 1)) = (v * 2 ^ (w * d)) * 2 ^ w * 2 ^ (x * w) := by
        rw [show w * (x + d + 1) = x * w + (w * d + w) by ring, Nat.pow_add, Nat.pow_add]
        ring
      rw [this, Nat.mul_div_cancel _ (Nat.two_pow_pos _), Nat.mul_mod_left]
    · obtain ⟨d, rfl⟩ : ∃ d, x = y + d + 1 := ⟨x - y - 1, by omega⟩
      rw [show (y + d + 1) * w = w * y + (w * d + w) by ring, Nat.pow_add,
        ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel _ (Nat.two_pow_pos _),
        Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by omega) (by omega)))]
      rfl

@[expose] noncomputable def idxAux (C : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun x _ ih i => Nat.lor (Nat.shiftLeft (Nat.succ i) (Nat.mul 9 x)) (ih (Nat.succ i))) C

theorem sIdx_eq (C : List Nat) : sIdx C = idxAux C 0 := rfl

theorem idxAux_field : ∀ (C : List Nat) (i0 x : Nat), C.Nodup → i0 + C.length < 512 →
    fget (idxAux C i0) x 9 = if x ∈ C then i0 + 1 + C.idxOf x else 0
  | [], i0, x, _, _ => by simp [idxAux, fget_eq']
  | y :: C, i0, x, hnd, hlen => by
    obtain ⟨hnot, hnd'⟩ := List.nodup_cons.1 hnd
    have hlen' : i0 + 1 + C.length < 512 := by simp at hlen; omega
    have e : idxAux (y :: C) i0 = Nat.lor (Nat.shiftLeft (Nat.succ i0) (Nat.mul 9 y))
      (idxAux C (Nat.succ i0)) := rfl
    rw [e, fget_lor, fget_shl (by simp at hlen; omega), idxAux_field C (Nat.succ i0) x hnd' hlen']
    by_cases hxy : x = y
    · subst hxy
      simp [hnot, List.idxOf_cons_self]
    · have hyx : y ≠ x := fun h => hxy h.symm
      simp [hxy, List.idxOf_cons, hyx, List.mem_cons]
      split_ifs <;> omega

theorem sIdx_le {C : List Nat} (hnd : C.Nodup) (hlen : C.length = 256) (x : Nat) :
    fget (sIdx C) x 9 ≤ 256 := by
  rw [sIdx_eq, idxAux_field C 0 x hnd (by omega)]
  split_ifs with h
  · have := List.idxOf_lt_length_of_mem h
    omega
  · omega

end CFSG.KC.GMS.SC

end
