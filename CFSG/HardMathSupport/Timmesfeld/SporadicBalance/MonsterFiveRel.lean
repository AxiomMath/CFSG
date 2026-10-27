module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveData
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.WordCheck

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFive

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Generated CFSG.AGLEmbedding.Norton
  CFSG.AGLEmbedding.Norton.MON5_7

@[expose] def repW (e : ℕ) (w : List Native.Gen) : List Native.Gen := (List.replicate e w).flatten

@[expose] def powW (k e : ℕ) : List Native.Gen :=
  if 2 ≤ e ∧ e ≤ 4 ∧ ¬ (fivePowW[k]!)[e]!.isEmpty then (fivePowW[k]!)[e]!
  else repW e fiveGens[k]!

@[expose] def rhsW (v : Array ℕ) : List Native.Gen :=
  (List.range 9).reverse.flatMap fun k => powW k v[k]!

@[expose] def powEqs : List (List Native.Gen × List Native.Gen) :=
  (List.range 9).flatMap fun k => (List.range' 2 3).filterMap fun e =>
    if (fivePowW[k]!)[e]!.isEmpty then none else some ((fivePowW[k]!)[e]!, repW e fiveGens[k]!)

@[expose] def pwEqs : List (List Native.Gen × List Native.Gen) :=
  (List.range 9).map fun i => (repW 5 fiveGens[i]!, rhsW fivePw[i]!)

@[expose] def cwEqs : List (List Native.Gen × List Native.Gen) :=
  (List.range 9).flatMap fun i => ((List.range 9).filter (i < ·)).map fun j =>
    (fiveGens[j]! ++ fiveGens[i]!, fiveGens[i]! ++ rhsW fiveCw[i * 9 + j]!)

@[expose] def relEqs : List (List Native.Gen × List Native.Gen) := powEqs ++ pwEqs ++ cwEqs

@[expose] def relSeg (lo n : ℕ) : List (List Native.Gen × List Native.Gen) :=
  (relEqs.drop lo).take n

@[expose] def relTail (lo : ℕ) : List (List Native.Gen × List Native.Gen) := relEqs.drop lo

@[expose] def normEqs : List (List Native.Gen × List Native.Gen) :=
  (List.range 3).flatMap fun j => (List.range 9).map fun i =>
    (fiveGens[i]! ++ fiveNW[j]!, fiveNW[j]! ++ rhsW (fiveNImg[j]!)[i]!)

@[expose] def normSeg (lo n : ℕ) : List (List Native.Gen × List Native.Gen) :=
  (normEqs.drop lo).take n

@[expose] def normTail (lo : ℕ) : List (List Native.Gen × List Native.Gen) := normEqs.drop lo

section Sound


theorem gw_repW (e : ℕ) (w : List Native.Gen) : gw (repW e w) = gw w ^ e := by
  induction e with
  | zero => simp [repW, gw_nil]
  | succ e ih =>
    have : repW (e + 1) w = w ++ repW e w := by simp [repW, List.replicate_succ]
    rw [this, gw_append, ih, pow_succ]

theorem gw_powW (h : agreeAll powEqs = true) (k : ℕ) (hk : k < 9) (e : ℕ) :
    gw (powW k e) = gw fiveGens[k]! ^ e := by
  unfold powW
  split_ifs with hs
  · obtain ⟨h2, h4, hne⟩ := hs
    have hmem : ((fivePowW[k]!)[e]!, repW e fiveGens[k]!) ∈ powEqs := by
      unfold powEqs
      rw [List.mem_flatMap]
      refine ⟨k, List.mem_range.2 hk, ?_⟩
      rw [List.mem_filterMap]
      refine ⟨e, List.mem_range'_1.2 ⟨h2, by omega⟩, ?_⟩
      simp [hne]
    have := agreeAll_sound h _ hmem
    simp only at this
    rw [this, gw_repW]
  · exact gw_repW e _

theorem gw_flatMap_rev (w : ℕ → List Native.Gen) :
    ∀ l : List ℕ, gw (l.reverse.flatMap w) = (l.map fun k => gw (w k)).prod
  | [] => by simp [gw_nil]
  | a :: t => by
    rw [List.reverse_cons, List.flatMap_append, List.flatMap_singleton,
      gw_append, List.map_cons, List.prod_cons, gw_flatMap_rev w t]

theorem gw_rhsW (h : agreeAll powEqs = true) (v : Array ℕ) :
    gw (rhsW v) = ((List.range 9).map fun k => gw fiveGens[k]! ^ v[k]!).prod := by
  unfold rhsW
  rw [gw_flatMap_rev]
  congr 1
  apply List.map_congr_left
  intro k hk
  exact gw_powW h k (List.mem_range.1 hk) _

end Sound

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFive
