module

public import CFSG.Certificates.Kernel.Spor.RawOrbEval
public import Certificates.Data.Kernel.SporSch.PairCl
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

public section

namespace CFSG.KS.SporSch.Tab

open CFSG.KS CFSG.KS.Raw

theorem lsum (m : Nat) (f : Nat → Nat) :
    ((List.range m).map f).sum = ∑ i ∈ Finset.range m, f i := by
  induction m with
  | zero => rfl
  | succ m ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ,
      List.map_singleton, List.sum_singleton]

theorem foldUp_add {m : Nat} {f : Nat → Nat → Nat} (c : Nat → Nat)
    (h : ∀ i < m, ∀ s, f i s = s + c i) (s : Nat) :
    foldUp m f s = s + ∑ i ∈ Finset.range m, c i := by
  rw [Orb.foldUp_eq]
  induction m generalizing s with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, ih (fun i hi => h i (by omega)), List.foldl_cons,
      List.foldl_nil, h m (by omega), Finset.sum_range_succ, Nat.add_assoc]

end CFSG.KS.SporSch.Tab

namespace CFSG.KS.SporSch

open CFSG.KC.Enum

theorem strictN_val (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem sumN_eq (m : Nat) (f : Nat → Nat) : sumN m f = ((List.range m).map f).sum := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change strictN (sumN m f) (fun a => Nat.add (f m) a) = _
    rw [strictN_val, ih, List.range_succ, List.map_append, List.sum_append, List.map_singleton,
      List.sum_singleton]
    exact Nat.add_comm _ _

end CFSG.KS.SporSch

end
