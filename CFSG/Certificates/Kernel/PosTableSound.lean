module

public import Certificates.Data.CFSGNative.HS.SmallF2

public section

namespace CFSG.KC.PosTable

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Th.Native

theorem posTable_eq_foldl (d : Nat) (pts : Array Nat) :
    posTable d pts = (List.range pts.size).foldl (fun pos i => pos.set! pts[i]! (UInt32.ofNat i))
      (Array.replicate (1 <<< d) none32) := by
  unfold posTable
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Std.Legacy.Range.size]
  simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, bind_pure, List.range_eq_range']
  rfl

theorem posTable_get {d : Nat} {pts : Array Nat} (hlt : ∀ i < pts.size, pts[i]! < 2 ^ d)
    (hinj : ∀ i < pts.size, ∀ j < pts.size, pts[i]! = pts[j]! → i = j)
    (hs : pts.size ≤ 2 ^ 32) {i : Nat} (hi : i < pts.size) :
    ((posTable d pts)[pts[i]!]!).toNat = i := by
  have key : ∀ k ≤ pts.size,
      ((List.range k).foldl (fun pos i => pos.set! pts[i]! (UInt32.ofNat i))
        (Array.replicate (1 <<< d) none32)).size = 2 ^ d ∧
      ∀ i < k, ((List.range k).foldl (fun pos i => pos.set! pts[i]! (UInt32.ofNat i))
        (Array.replicate (1 <<< d) none32))[pts[i]!]! = UInt32.ofNat i := by
    intro k
    induction k with
    | zero => intro _; simp [Nat.one_shiftLeft]
    | succ k ih =>
      intro hk
      obtain ⟨hsz, hget⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      refine ⟨by rw [Array.size_set!, hsz], fun j hj => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hlt' | rfl
      · have hne : pts[j]! ≠ pts[k]! := fun e => by
          have := hinj j (by omega) k (by omega) e
          omega
        rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hne)]
        exact hget j hlt'
      · rw [Array.getElem!_set!_self _ _ _ (by rw [hsz]; exact hlt j (by omega))]
  rw [posTable_eq_foldl, (key _ (Nat.le_refl _)).2 i hi, UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by omega)

end CFSG.KC.PosTable

end
