module

public import CFSG.Certificates.Kernel.Trace6091.TwinEq
public import Certificates.Data.Kernel.Trace6091.Scan
public import CFSG.Monster.B.Rep4371.GlueDefs

public section

namespace CFSG.KC.Trace6091

open CFSG.KC CFSG.KC.KDense CFSG.Monster.B CFSG.Monster.B.Rep4371 CFSG.Monster.AxisCount

theorem popcN_succ : ∀ k a, Model.popcN (k + 1) a = Model.popcN k a + (a.testBit k).toNat
  | 0, a => by
    simp only [Model.popcN, Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one a with h | h <;> simp [h]
  | k + 1, a => by
    rw [Model.popcN, popcN_succ k (a / 2), Model.popcN, Nat.testBit_succ]
    omega

theorem popcT_eq (a : Nat) : ∀ k, popcT k a = Model.popcN k a
  | 0 => rfl
  | k + 1 => by
    rw [popcN_succ, ← popcT_eq a k, ← bitN_eq]
    rfl

theorem pW_eq (c : Nat) : pW (wordT c) = (Model.pN c).toNat := by
  unfold pW Model.pN
  rw [popcT_eq, wordT_eq]
  change (Model.popcN 24 (Model.wordN c) >>> 2) &&& 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rcases Nat.mod_two_eq_zero_or_one (Model.popcN 24 (Model.wordN c) / 2 ^ 2) with h | h <;>
    simp [h]

theorem beq_eq_decide (x y : Nat) : Nat.beq x y = decide (x = y) :=
  Bool.eq_iff_iff.mpr (by simp [Nat.beq_eq])

theorem octTab_twin : (List.range 4096).filter (fun a => Nat.beq (popcT 24 (wordT a)) 8) =
    (List.range 759).map octT := by
  decide +kernel

theorem evenTab_twin : (List.range 128).filter (fun m => Nat.beq (popcT 8 m % 2) 0) =
    (List.range 64).map evenT := by
  decide +kernel

theorem octTab_eq : Native.octTab () = ((List.range 759).map octT).toArray := by
  unfold Native.octTab
  have h : (List.range 4096).filter (fun a => Native.popcN 24 (Native.wordN a) == 8) =
      (List.range 4096).filter (fun a => Nat.beq (popcT 24 (wordT a)) 8) :=
    List.filter_congr fun a _ => by
      rw [beq_eq_decide, popcT_eq, wordT_eq, native_popcN, native_wordN]
      exact Bool.eq_iff_iff.mpr (by simp only [beq_iff_eq, decide_eq_true_eq])
  rw [h, octTab_twin]

theorem evenTab_eq : Native.evenTab () = ((List.range 64).map evenT).toArray := by
  unfold Native.evenTab
  have h : (List.range 128).filter (fun m => Native.popcN 8 m % 2 == 0) =
      (List.range 128).filter (fun m => Nat.beq (popcT 8 m % 2) 0) :=
    List.filter_congr fun m _ => by
      rw [beq_eq_decide, popcT_eq, native_popcN]
      exact Bool.eq_iff_iff.mpr (by simp only [beq_iff_eq, decide_eq_true_eq])
  rw [h, evenTab_twin]

theorem octTab_get (o : Nat) (ho : o < 759) : (Native.octTab ())[o]! = octT o := by
  rw [octTab_eq]
  simp [ho]

theorem evenTab_get (m : Nat) (hm : m < 64) : (Native.evenTab ())[m]! = evenT m := by
  rw [evenTab_eq]
  simp [hm]

end CFSG.KC.Trace6091

end
