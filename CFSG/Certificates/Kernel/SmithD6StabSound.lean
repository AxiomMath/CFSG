module

public import Certificates.Data.Kernel.SmithD6.StabK
public import CFSG.Certificates.Kernel.KeyTreeChunksSound

public section

namespace CFSG.KD.SmithD6Stab

open CFSG.KC.Loop CFSG.KC.KeyTree

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem cntGo_eq : ∀ (l : List Nat) (a : Nat),
    cntGo l a = a + (l.map fun k => 2 ^ (19 * clsK k)).sum
  | [], a => rfl
  | k :: l, a => by
    change strictN (Nat.add a (Nat.pow 2 (Nat.mul 19 (clsK k)))) (cntGo l) = _
    rw [strictN_eq, cntGo_eq l, List.map_cons, List.sum_cons]
    simp only [Nat.add_eq, Nat.pow_eq, Nat.mul_eq]
    omega

theorem firstGo_sound (r : Nat → Nat) : ∀ l : List Nat,
    firstGo r l = true → ∀ k ∈ l, r (clsK k) ≤ k
  | [] => by simp
  | k :: l => fun h => by
    obtain ⟨h1, h2⟩ := band_true (a := Nat.ble (r (clsK k)) k) (b := firstGo r l) h
    have := firstGo_sound r l h2
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact Nat.le_of_ble_eq_true h1
    · exact this x hx

theorem clsK_le (k : Nat) : clsK k ≤ 5 := by
  unfold clsK clsP
  repeat' split
  all_goals omega

theorem sum_lanes (l : List Nat) : (l.map fun k => 2 ^ (19 * clsK k)).sum =
    l.countP (fun k => clsK k == 0) + l.countP (fun k => clsK k == 1) * 2 ^ 19 +
    l.countP (fun k => clsK k == 2) * 2 ^ 38 + l.countP (fun k => clsK k == 3) * 2 ^ 57 +
    l.countP (fun k => clsK k == 4) * 2 ^ 76 + l.countP (fun k => clsK k == 5) * 2 ^ 95 := by
  induction l with
  | nil => rfl
  | cons k l ih =>
    simp only [List.map_cons, List.sum_cons, List.countP_cons, ih]
    have h := clsK_le k
    generalize clsK k = c at h ⊢
    obtain rfl | rfl | rfl | rfl | rfl | rfl : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 := by
      omega
    all_goals simp
    all_goals omega

end CFSG.KD.SmithD6Stab

end
