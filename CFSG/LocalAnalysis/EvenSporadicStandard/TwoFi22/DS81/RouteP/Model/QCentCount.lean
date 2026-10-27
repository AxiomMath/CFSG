module

public import Certificates.Data.RouteP.QCent
public import CFSG.Perm.ChainSpec
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model

open CFSG.Sporadic.Th.Native
open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native

theorem qcentCount_eq (p : ℕ → Bool) (n acc : ℕ) :
    qcentCount p n acc = acc + ((Finset.range n).filter fun k => p k = true).card := by
  induction n generalizing acc with
  | zero => rw [qcentCount.eq_1]; simp
  | succ n ih =>
    rw [qcentCount.eq_2, ih, Finset.range_add_one, Finset.filter_insert]
    split_ifs with hp
    · rw [Finset.card_insert_of_notMem]
      · omega
      · exact fun h => Finset.notMem_range_self (Finset.mem_of_mem_filter n h)
    · omega

theorem ncard_filter_tree {G : Type*} [Group G] {n : ℕ} [MulAction G (Fin n)]
    {T : CFSG.Perm.Native.Tree} {lv : Array ℕ} {lG : ℕ → G} {r : ℕ}
    (hT : CFSG.Perm.TreeFacts n T lv lG r) (q : ℕ → Bool) :
    {y : Fin n | (∃ k < T.pts.size, ap T.pts k = y.val) ∧ q y.val = true}.ncard =
      ((Finset.range T.pts.size).filter fun k => q (ap T.pts k) = true).card := by
  classical
  have hcongr :
      {y : Fin n | (∃ k < T.pts.size, ap T.pts k = y.val) ∧ q y.val = true}.ncard =
        (((Finset.range T.pts.size).filter fun k => q (ap T.pts k) = true : Finset ℕ) :
          Set ℕ).ncard := by
    refine Set.ncard_congr (fun (a : Fin n) _ => ap T.pos a.val) ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_coe]
      obtain ⟨k, hk, hka⟩ := ha.1
      have hpos : ap T.pos a.val = k := by rw [← hka, hT.pos_pts k hk]
      rw [hpos]
      exact ⟨hk, by rw [hka]; exact ha.2⟩
    · intro a b ha hb hab
      obtain ⟨j, hj, hja⟩ := ha.1
      obtain ⟨k, hk, hkb⟩ := hb.1
      have hj' : ap T.pos a.val = j := by rw [← hja, hT.pos_pts j hj]
      have hk' : ap T.pos b.val = k := by rw [← hkb, hT.pos_pts k hk]
      rw [hj', hk'] at hab
      exact Fin.ext (hja.symm.trans ((congrArg (fun i => ap T.pts i) hab).trans hkb))
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_coe] at hb
      exact ⟨⟨ap T.pts b, hT.pts_lt b hb.1⟩, ⟨⟨b, hb.1, rfl⟩, hb.2⟩, hT.pos_pts b hb.1⟩
  rw [hcongr, Set.ncard_coe_finset]

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
