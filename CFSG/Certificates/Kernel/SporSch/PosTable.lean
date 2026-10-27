module

public import CFSG.Certificates.Kernel.RankThree.F2Mat
public import Certificates.Data.CFSGNative.HS.SmallF2

public section

namespace CFSG.KS.MatRep

open CFSG.RankThree.Native.F2 CFSG.Sporadic.SmallF2.Native

theorem posTable_eq_foldl (d : ℕ) (pts : Array ℕ) :
    posTable d pts = (List.range pts.size).foldl
      (fun pos i => pos.set! pts[i]! (UInt32.ofNat i))
      (Array.replicate (1 <<< d) (CFSG.Sporadic.Th.Native.none32 ())) := by
  unfold posTable
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Std.Legacy.Range.size]
  simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, bind_pure, List.range_eq_range']
  rfl

theorem posTable_get {d : ℕ} {pts : Array ℕ} (hnd : pts.toList.Nodup)
    (hlt : ∀ v ∈ pts, v < 2 ^ d) (hsz : pts.size < 2 ^ 32) {j : ℕ} (hj : j < pts.size) :
    ((posTable d pts)[pts[j]!]!).toNat = j := by
  have hget : ∀ i (hi : i < pts.size), pts[i]! < 1 <<< d := fun i hi => by
    rw [Nat.one_shiftLeft, getElem!_pos pts i hi]
    exact hlt _ (Array.getElem_mem hi)
  have key : ∀ k ≤ pts.size, ((List.range k).foldl (fun pos i => pos.set! pts[i]! (UInt32.ofNat i))
      (Array.replicate (1 <<< d) (CFSG.Sporadic.Th.Native.none32 ()))).size = 1 <<< d ∧
      ∀ i < k, ((List.range k).foldl (fun pos i => pos.set! pts[i]! (UInt32.ofNat i))
        (Array.replicate (1 <<< d) (CFSG.Sporadic.Th.Native.none32 ())))[pts[i]!]! =
          UInt32.ofNat i := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      obtain ⟨hs, hi⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      refine ⟨by rw [Array.size_set!, hs], fun i hik => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hik with hil | rfl
      · have hne : pts[i]! ≠ pts[k]! := by
          intro e
          rw [getElem!_pos pts i (by omega), getElem!_pos pts k (by omega)] at e
          have := (List.Nodup.getElem_inj_iff hnd (i := i) (j := k)
            (hi := by simp; omega) (hj := by simp; omega)).1 (by simpa using e)
          omega
        rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hne)]
        exact hi i hil
      · rw [Array.getElem!_set!_self _ _ _ (by rw [hs]; exact hget i (by omega))]
  rw [posTable_eq_foldl, (key pts.size le_rfl).2 j hj, UInt32.toNat_ofNat',
    Nat.mod_eq_of_lt (by omega)]

theorem foldl_xor_eq (g : ℕ → ℕ) : ∀ (L : List ℕ) (a : ℕ),
    L.foldl (fun acc j => acc ^^^ g j) a = a ^^^ L.foldr (fun j acc => g j ^^^ acc) 0
  | [], a => by simp
  | j :: L, a => by
    rw [List.foldl_cons, foldl_xor_eq g L, List.foldr_cons, Nat.xor_assoc]

theorem vecMulN_eq_vmul {d : ℕ} {R : Array ℕ} {M : ℕ} (hR : ∀ k < d, row d M k = R[k]?.getD 0)
    (v : ℕ) : vecMulN d R v = vmul d v M := by
  unfold vecMulN vmul
  have h1 : (fun acc j => if v.testBit j then acc ^^^ (R[j]?.getD 0) else acc) =
      fun acc j => acc ^^^ (if v.testBit j then R[j]?.getD 0 else 0) := by
    funext acc j
    split <;> simp
  rw [h1, foldl_xor_eq, Nat.zero_xor]
  have : ∀ L : List ℕ, (∀ k ∈ L, k < d) →
      L.foldr (fun j acc => (if v.testBit j then R[j]?.getD 0 else 0) ^^^ acc) 0 =
        L.foldr (fun k acc => if v.testBit k then row d M k ^^^ acc else acc) 0 := by
    intro L hL
    induction L with
    | nil => rfl
    | cons k L ih =>
      rw [List.foldr_cons, List.foldr_cons, ih fun j hj => hL j (List.mem_cons_of_mem _ hj),
        hR k (hL k List.mem_cons_self)]
      split <;> simp
  exact this _ fun k hk => List.mem_range.1 hk

end CFSG.KS.MatRep

end
