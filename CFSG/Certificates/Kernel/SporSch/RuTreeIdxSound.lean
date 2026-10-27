module

public import CFSG.Sporadic.Schreier.RuTreeEltA
public import Std.Data.HashMap.Lemmas

public section

namespace CFSG.KS.RuTree

open CFSG.Sporadic.RuSchreier

theorem treeSets_inj {S : Array (List Nat)} (h : ruSortedStrict S = true) {i j : Nat}
    (hi : i < S.size) (hj : j < S.size) (e : S[i]! = S[j]!) : i = j := by
  unfold ruSortedStrict at h
  rw [decide_eq_true_iff] at h
  have hp : (S.toList.mergeSort fun x y => decide (x ≤ y)).Pairwise (· < ·) :=
    (List.isChain_iff_pairwise (R := fun x y : List Nat => x < y)).1 h
  have hnd : S.toList.Nodup :=
    (List.mergeSort_perm S.toList fun x y => decide (x ≤ y)).nodup_iff.1
      (hp.imp (fun hab => ne_of_lt hab))
  have hinj := List.nodup_iff_injective_getElem.1 hnd
  have := @hinj ⟨i, by simpa using hi⟩ ⟨j, by simpa using hj⟩
    (by simpa [getElem!_def, Array.getElem?_eq_getElem, hi, hj] using e)
  exact congrArg Fin.val this

theorem ruTreeIdx_get (h : ruSortedStrict ruTreeSets = true) (hsz : ruTreeSets.size = 593775)
    {j : Nat} (hj : j < 593775) : ruTreeIdx[ruTreeSets[j]!]? = some j := by
  have key : ∀ N, N ≤ 593775 → ∀ j < N,
      ((List.range N).foldl (fun m j => m.insert ruTreeSets[j]! j)
        (Std.HashMap.emptyWithCapacity 1048576))[ruTreeSets[j]!]? = some j := by
    intro N
    induction N with
    | zero => intro _ j hj; omega
    | succ N ih =>
      intro hN j hj
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        Std.HashMap.getElem?_insert]
      by_cases hjN : j = N
      · subst hjN
        simp
      · have hne : (ruTreeSets[N]! == ruTreeSets[j]!) = false := by
          rw [beq_eq_false_iff_ne]
          intro e
          exact hjN (treeSets_inj h (by omega) (by omega) e).symm
        rw [hne]
        exact ih (by omega) j (by omega)
  have e : ruTreeIdx = (List.range 593775).foldl (fun m j => m.insert ruTreeSets[j]! j)
      (Std.HashMap.emptyWithCapacity 1048576) := by
    rw [ruTreeIdx, ← Array.foldl_toList, Array.toList_range]
  rw [e]
  exact key 593775 (Nat.le_refl _) j hj

end CFSG.KS.RuTree

end
