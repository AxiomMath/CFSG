module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Offend
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.N3SplitFix

public section

namespace CFSG.EvenSmallLie.OmegaEight.N3Split

open CFSG.EvenSmallLie.OmegaEight.Stage2

@[expose] def filterFix (y : ℕ) (fix : List ℕ) : List ℕ :=
  if fix.length ≤ 24 then fix.filter fun v => mulVecK y v == v
  else
    let T := imgTab y 12
    fix.filter fun v => T.getD v 0 == v

theorem filterFix_eq {y : ℕ} {fix : List ℕ} (h : ∀ v ∈ fix, v < 4096) :
    filterFix y fix = fix.filter fun v => mulVecK y v == v := by
  unfold filterFix
  split_ifs
  · rfl
  · exact List.filter_congr fun v hv => by rw [imgTab_getD y 12 v (h v hv)]

theorem lt_of_mem_filter {p : ℕ → Bool} {fix : List ℕ} (h : ∀ v ∈ fix, v < 4096) :
    ∀ v ∈ fix.filter p, v < 4096 := fun v hv => h v (List.mem_filter.1 hv).1

@[expose] def nodeF (B : ℕ) : ℕ → List ℕ → List ℕ → List ℕ → Bool
  | 0, _, _, _ => false
  | fuel + 1, span, fix, rest =>
    decide (span.length * fix.length ≤ B) &&
      rest.tails.all fun
        | [] => true
        | y :: ys => !(newGen span y) ||
          nodeF B fuel (span ++ span.map (mulK y)) (filterFix y fix)
            (ys.filter fun z => mulK y z == mulK z y)

theorem nodeF_eq (B : ℕ) : ∀ (fuel : ℕ) (span fix rest : List ℕ), (∀ v ∈ fix, v < 4096) →
    nodeF B fuel span fix rest = node B fuel span fix rest
  | 0, _, _, _, _ => rfl
  | fuel + 1, span, fix, rest, h => by
    rw [nodeF, node]
    congr 1
    refine congrArg (rest.tails.all ·) (funext fun l => ?_)
    rcases l with _ | ⟨y, ys⟩
    · rfl
    · simp only
      rw [filterFix_eq h, nodeF_eq B fuel _ _ _ (lt_of_mem_filter h)]

@[expose] def rootCheckF (B r : ℕ) (C base : List ℕ) : Bool :=
  nodeF B 8 [idK, r] (filterFix r base) C

@[expose] def allRootsF (B : ℕ) (I base : List ℕ) : Bool :=
  I.all fun r => rootCheckF B r (commOf I r) base

theorem allRootsF_eq {B : ℕ} {I base : List ℕ} (h : ∀ v ∈ base, v < 4096) :
    allRootsF B I base = allRoots B I base := by
  unfold allRootsF allRoots
  refine congrArg (I.all ·) (funext fun r => ?_)
  rw [rootCheckF, rootCheck, filterFix_eq h, nodeF_eq B 8 _ _ _ (lt_of_mem_filter h)]

theorem lt_of_mem_range {v : ℕ} (hv : v ∈ List.range 4096) : v < 4096 := List.mem_range.1 hv

end CFSG.EvenSmallLie.OmegaEight.N3Split
