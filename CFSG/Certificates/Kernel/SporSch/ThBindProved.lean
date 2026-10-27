
module

public import CFSG.Certificates.Kernel.SporSch.ThRowsDefs
public import Certificates.Data.Kernel.SporSch.ThRows

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.Sporadic.Th.Native CFSG.Sporadic.ThSchreier

theorem v4N_eq_toNat (x : V4) : v4N x = x.toNat := by
  obtain ⟨a, b, c, d⟩ := x
  change Nat.lor a.toNat (Nat.lor (b.toNat <<< 64) (Nat.lor (c.toNat <<< 128) (d.toNat <<< 192))) =
    a.toNat + 2 ^ 64 * b.toNat + 2 ^ 128 * c.toNat + 2 ^ 192 * d.toNat
  have ha := UInt64.toNat_lt a
  have hb := UInt64.toNat_lt b
  have hc := UInt64.toNat_lt c
  have orShl : ∀ {x k : Nat} (y : Nat), x < 2 ^ k → x ||| y <<< k = x + 2 ^ k * y := by
    intro x k y hx
    rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hx, Nat.shiftLeft_eq, Nat.add_comm,
      Nat.mul_comm]
  have e3 : c.toNat <<< 128 ||| d.toNat <<< 192 = (c.toNat + 2 ^ 64 * d.toNat) <<< 128 := by
    rw [show (192 : Nat) = 64 + 128 from rfl, Nat.shiftLeft_add d.toNat 64 128,
      ← Nat.shiftLeft_or_distrib, orShl _ hc]
  have e2 : b.toNat <<< 64 ||| (c.toNat + 2 ^ 64 * d.toNat) <<< 128 =
      (b.toNat + 2 ^ 64 * (c.toNat + 2 ^ 64 * d.toNat)) <<< 64 := by
    rw [show (128 : Nat) = 64 + 64 from rfl, Nat.shiftLeft_add _ 64 64,
      ← Nat.shiftLeft_or_distrib, orShl _ hb]
  change a.toNat ||| (b.toNat <<< 64 ||| (c.toNat <<< 128 ||| d.toNat <<< 192)) = _
  rw [e3, e2, orShl _ ha]
  ring

theorem v4OfNat_v4N (x : V4) : v4OfNat (v4N x) = x := by
  apply V4.toNat_injective
  rw [v4OfNat_toNat, v4N_eq_toNat, Nat.mod_eq_of_lt (V4.toNat_lt x)]

theorem v4N_sound_proved {x : V4} {n : Nat} (h : v4N x = n) : x = v4OfNat n := by
  rw [← h, v4OfNat_v4N]

theorem strictB_eq' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem v4From_spec {R : Nat → Nat} : ∀ (l : List V4) (i : Nat), v4From R l i = true →
    ∀ j (hj : j < l.length), v4N l[j] = R (i + j)
  | [], _, _, j, hj => by simp at hj
  | x :: l, i, h, j, hj => by
    have e : v4From R (x :: l) i = strictB (R i) (fun r => Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false (v4From R l (Nat.succ i))
          (Nat.blt r (Nat.shiftLeft (nat_lit 1) (nat_lit 248)))) (Nat.beq (v4N x) r)) := rfl
    rw [e, strictB_eq'] at h
    cases h1 : Nat.beq (v4N x) (R i)
    · rw [h1] at h
      exact absurd h Bool.false_ne_true
    · rw [h1] at h
      dsimp only at h
      cases h2 : Nat.blt (R i) (Nat.shiftLeft 1 248)
      · rw [h2] at h
        exact absurd h Bool.false_ne_true
      · rw [h2] at h
        dsimp only at h
        cases j with
        | zero => simpa using Nat.eq_of_beq_eq_true h1
        | succ j =>
          rw [List.getElem_cons_succ, v4From_spec l (i + 1) h j (by simpa using hj)]
          congr 1
          omega

theorem lenV_eq : ∀ l : List V4, lenV l = l.length
  | [] => rfl
  | _ :: l => by
    change Nat.succ (lenV l) = _
    rw [lenV_eq l]
    rfl

theorem v4Bind_sound_proved {a : Array V4} {R : Nat → Nat} (h : v4BindK a.toList R = true) :
    a = rowsV R := by
  have e : v4BindK a.toList R = Bool.rec (motive := fun _ => Bool) false
      (v4From R a.toList (nat_lit 0)) (Nat.beq (lenV a.toList) (nat_lit 248)) := rfl
  rw [e] at h
  cases h1 : Nat.beq (lenV a.toList) 248
  · rw [h1] at h
    exact absurd h Bool.false_ne_true
  · rw [h1] at h
    have hlen : a.size = 248 := by
      have := Nat.eq_of_beq_eq_true h1
      rwa [lenV_eq, Array.length_toList] at this
    apply Array.ext
    · simp only [hlen, rowsV, Array.size_ofFn]
    · intro j h1' h2'
      simp only [rowsV, Array.getElem_ofFn]
      have := v4From_spec a.toList 0 h j (by simpa using h1')
      rw [Array.getElem_toList, Nat.zero_add] at this
      rw [← this, v4OfNat_v4N]

end CFSG.KS.SporSch

end
