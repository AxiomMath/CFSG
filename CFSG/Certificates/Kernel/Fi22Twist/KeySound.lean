module

public import CFSG.Certificates.Kernel.Fi22Twist.LeafSound
import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.KC.Fi22Twist

open CFSG.KC.Enum

theorem ap_lt (p x : Nat) : ap p x < 4096 := by
  change (p >>> (12 * x)) &&& 4095 < 4096
  have := Nat.and_le_right (n := p >>> (12 * x)) (m := 4095)
  omega

theorem or_add {A B s : Nat} (hA : A < 2 ^ s) (hB : 2 ^ s ∣ B) : A ||| B = A + B := by
  obtain ⟨x, rfl⟩ := hB
  rw [Nat.mul_comm, ← Nat.shiftLeft_eq, or_shift hA, Nat.shiftLeft_eq]

theorem kAp_sum (g c : Nat) : kAp g c = ap g (cg c 0) + ap g (cg c 1) * 2 ^ 12 +
    ap g (cg c 2) * 2 ^ 24 + ap g (cg c 3) * 2 ^ 36 + ap g (cg c 4) * 2 ^ 48 +
    ap g (cg c 5) * 2 ^ 60 := by
  have h0 := ap_lt g (cg c 0)
  have h1 := ap_lt g (cg c 1)
  have h2 := ap_lt g (cg c 2)
  have h3 := ap_lt g (cg c 3)
  have h4 := ap_lt g (cg c 4)
  have h5 := ap_lt g (cg c 5)
  change ((ap g (cg c 0) ||| ap g (cg c 1) <<< 12) |||
      (ap g (cg c 2) <<< 24 ||| ap g (cg c 3) <<< 36)) |||
      (ap g (cg c 4) <<< 48 ||| ap g (cg c 5) <<< 60) = _
  generalize ap g (cg c 0) = a0 at h0 ⊢
  generalize ap g (cg c 1) = a1 at h1 ⊢
  generalize ap g (cg c 2) = a2 at h2 ⊢
  generalize ap g (cg c 3) = a3 at h3 ⊢
  generalize ap g (cg c 4) = a4 at h4 ⊢
  generalize ap g (cg c 5) = a5 at h5 ⊢
  rw [Nat.shiftLeft_eq a1 12, Nat.shiftLeft_eq a2 24, Nat.shiftLeft_eq a3 36,
    Nat.shiftLeft_eq a4 48, Nat.shiftLeft_eq a5 60]
  have e1 : a0 ||| a1 * 2 ^ 12 = a0 + a1 * 2 ^ 12 :=
    or_add (by simp only [Nat.reducePow]; omega) (Dvd.intro_left _ rfl)
  have e2 : a2 * 2 ^ 24 ||| a3 * 2 ^ 36 = a2 * 2 ^ 24 + a3 * 2 ^ 36 :=
    or_add (by simp only [Nat.reducePow]; omega) (Dvd.intro_left _ rfl)
  have e3 : a4 * 2 ^ 48 ||| a5 * 2 ^ 60 = a4 * 2 ^ 48 + a5 * 2 ^ 60 :=
    or_add (by simp only [Nat.reducePow]; omega) (Dvd.intro_left _ rfl)
  have e4 : (a0 + a1 * 2 ^ 12) ||| (a2 * 2 ^ 24 + a3 * 2 ^ 36) =
      a0 + a1 * 2 ^ 12 + (a2 * 2 ^ 24 + a3 * 2 ^ 36) :=
    or_add (s := 24) (by simp only [Nat.reducePow]; omega) (by simp only [Nat.reducePow]; omega)
  have e5 : (a0 + a1 * 2 ^ 12 + (a2 * 2 ^ 24 + a3 * 2 ^ 36)) ||| (a4 * 2 ^ 48 + a5 * 2 ^ 60) =
      a0 + a1 * 2 ^ 12 + (a2 * 2 ^ 24 + a3 * 2 ^ 36) + (a4 * 2 ^ 48 + a5 * 2 ^ 60) :=
    or_add (s := 48) (by simp only [Nat.reducePow]; omega) (by simp only [Nat.reducePow]; omega)
  rw [e1, e2, e3, e4, e5]
  simp only [Nat.add_assoc]

theorem kAp_cg (g c : Nat) {l : Nat} (hl : l < 6) : cg (kAp g c) l = ap g (cg c l) := by
  have h0 := ap_lt g (cg c 0)
  have h1 := ap_lt g (cg c 1)
  have h2 := ap_lt g (cg c 2)
  have h3 := ap_lt g (cg c 3)
  have h4 := ap_lt g (cg c 4)
  have h5 := ap_lt g (cg c 5)
  rw [kAp_sum, cg_eq]
  interval_cases l <;> simp only [Nat.reducePow, Nat.reduceMul] <;> omega

theorem cg_baseKey (l : Nat) : cg baseKey l = bp l := rfl

theorem commK_pt {G D : Nat → Nat} {gof j m : Nat} (h : commK G D gof j m = true) :
    ∀ e, (e = 9 ∨ e = 3 ∨ e = 1) → ∀ l < 6,
      ap (G (gof + m)) (ap (D (27 * j + e)) (bp l)) =
        ap (D (27 * j + e)) (ap (G (gof + m)) (bp l)) := by
  intro e he l hl
  have k : cg (kAp (G (Nat.add gof m)) (kAp (D (Nat.add (Nat.mul 27 j) e)) baseKey)) l =
      cg (kAp (D (Nat.add (Nat.mul 27 j) e)) (kAp (G (Nat.add gof m)) baseKey)) l :=
    congrArg (fun N => cg N l) (commK_sound h e he)
  rw [kAp_cg _ _ hl, kAp_cg _ _ hl, kAp_cg _ _ hl, kAp_cg _ _ hl, cg_baseKey] at k
  exact k

end CFSG.KC.Fi22Twist

end
