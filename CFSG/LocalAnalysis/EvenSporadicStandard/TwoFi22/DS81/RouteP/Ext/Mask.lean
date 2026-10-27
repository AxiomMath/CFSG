module

public import Certificates.Data.RouteP.M24Defect

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu Certificates.RouteP.M24Defect

@[expose] def bp (m w : ℕ) : ZMod 2 := dotProduct (bvec 11 m) (bvec 11 w)

theorem bp_xor_right (m a b : ℕ) : bp m (a ^^^ b) = bp m a + bp m b := by
  simp only [bp, bvec_xor, dotProduct_add]

theorem bp_xor_left (a b w : ℕ) : bp (a ^^^ b) w = bp a w + bp b w := by
  simp only [bp, bvec_xor, add_dotProduct]

theorem bp_zero_right (m : ℕ) : bp m 0 = 0 := by
  simp only [bp, bvec_zero, dotProduct_zero]

theorem bp_zero_left (w : ℕ) : bp 0 w = 0 := by
  simp only [bp, bvec_zero, zero_dotProduct]

theorem bvec_xorMasks (n : ℕ) : ∀ l : List ℕ, bvec n (xorMasks l) = (l.map (bvec n)).sum
  | [] => by simp [xorMasks, bvec_zero]
  | m :: l => by simp only [xorMasks, bvec_xor, bvec_xorMasks n l, List.map_cons, List.sum_cons]

theorem bp_xorMasks_right (m : ℕ) : ∀ l : List ℕ, bp m (xorMasks l) = (l.map (bp m)).sum
  | [] => by simp [xorMasks, bp_zero_right]
  | a :: l => by
    simp only [xorMasks, bp_xor_right, bp_xorMasks_right m l, List.map_cons, List.sum_cons]

theorem bp_xorMasks_left (w : ℕ) : ∀ l : List ℕ, bp (xorMasks l) w = (l.map fun m => bp m w).sum
  | [] => by simp [xorMasks, bp_zero_left]
  | a :: l => by
    simp only [xorMasks, bp_xor_left, bp_xorMasks_left w l, List.map_cons, List.sum_cons]

theorem xorMasks_lt {n : ℕ} : ∀ {l : List ℕ}, (∀ m ∈ l, m < 2 ^ n) → xorMasks l < 2 ^ n
  | [], _ => by simp [xorMasks]
  | a :: l, h => by
    rw [xorMasks]
    exact Nat.xor_lt_two_pow (h a List.mem_cons_self)
      (xorMasks_lt fun m hm => h m (List.mem_cons_of_mem a hm))

theorem xorMasks_append (l l' : List ℕ) : xorMasks (l ++ l') = xorMasks l ^^^ xorMasks l' := by
  induction l with
  | nil => simp [xorMasks]
  | cons a l ih => simp only [List.cons_append, xorMasks, ih, Nat.xor_assoc]

theorem xorMasks_map_xor {α : Type*} (L : List α) (f g : α → ℕ) :
    xorMasks (L.map fun x => f x ^^^ g x) = xorMasks (L.map f) ^^^ xorMasks (L.map g) := by
  induction L with
  | nil => simp [xorMasks]
  | cons a L ih =>
    simp only [List.map_cons, xorMasks, ih]
    ac_rfl

theorem bvec_eq_of_lt {n a b : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) (h : bvec n a = bvec n b) :
    a = b := bvec_inj ha hb h

theorem lamApply_xor (v w : ℕ × ℕ) (i : ℕ) :
    lamApply (v.1 ^^^ w.1, v.2 ^^^ w.2) i = lamApply v i ^^^ lamApply w i := by
  unfold lamApply
  rw [← xorMasks_map_xor]
  congr 1
  refine List.map_congr_left fun e _ => ?_
  split_ifs
  · exact actM_xor _ _ _
  · exact actM_xor _ _ _

theorem xorMasks_map_zero {α : Type*} (L : List α) : xorMasks (L.map fun _ => 0) = 0 := by
  induction L with
  | nil => rfl
  | cons a L ih => simp only [List.map_cons, xorMasks, ih, Nat.xor_zero]

theorem lamApply_zero (i : ℕ) : lamApply (0, 0) i = 0 := by
  unfold lamApply
  have : ∀ e : HA × ℕ, actM (matA e.1.fwd) (if e.2 = 0 then 0 else 0) = 0 := by
    intro e
    simp only [ite_self]
    exact XorLin.map_zero (actM_xor _)
  simp only [this]
  exact xorMasks_map_zero _

theorem lamApply_lt (v : ℕ × ℕ) (i : ℕ) : lamApply v i < 2 ^ 11 := by
  unfold lamApply
  refine xorMasks_lt fun m hm => ?_
  simp only [List.mem_map] at hm
  obtain ⟨e, -, rfl⟩ := hm
  refine actM_lt (fun c hc => ?_) _
  simp only [matA, matOf, List.mem_map] at hc
  obtain ⟨j, -, rfl⟩ := hc
  exact act11_lt _ _

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
