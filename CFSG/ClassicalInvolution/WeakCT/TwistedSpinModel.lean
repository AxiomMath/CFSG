module

public import CFSG.ClassicalInvolution.WeakCT.TwistedRankOne
public import CFSG.ClassicalInvolution.WeakCT.TwistedSpinLevi

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.Timmesfeld CFSG.Timmesfeld.LevisExtras
  CFSG.ClassicalInvolution.Models.TwistedPairs
open scoped MatrixGroups

section Model

variable {F : Type} [Field F] [Finite F] {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
  {n : ℕ}

omit [Finite F] in
theorem rankOne_minusDatum_long {k : Fin (n - 1)} (hk : k.val + 1 < n - 1) :
    CurtisTits.rankOne (minusDatum n hirr).rootGroup k = (rLong n b c hk).range :=
  rankOne_eq_range_of_param (D := minusDatum n hirr) (i := k) _ (rLong_upper hirr hk)
    (rLong_lower hirr hk) (rLong_param_upper hirr hk) (rLong_param_lower hirr hk)

theorem rankOne_minusDatum_short [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)] {k : Fin (n - 1)}
    (hk : ¬ k.val + 1 < n - 1) :
    CurtisTits.rankOne (minusDatum n hirr).rootGroup k = (shortBlock hirr n k).range :=
  rankOne_eq_range_of_param (D := minusDatum n hirr) (i := k) _ (shortBlock_upper_mem hirr hk)
    (shortBlock_lower_mem hirr hk) (shortBlock_param_upper hirr hk)
    (shortBlock_param_lower hirr hk)

theorem iSup_rankOne_minusDatum (hn : 4 ≤ n) :
    ⨆ k : Fin (minusDatum n hirr).rank, CurtisTits.rankOne (minusDatum n hirr).rootGroup k = ⊤ :=
  iSup_rankOne_eq_top_of_ct (D := minusDatum n hirr) (minusDatum_isCTGroupDatum n hirr hn) rfl

theorem commute_rankOne_minusDatum :
    ∀ i j : Fin (n - 1), i.val + 1 < j.val →
      ∀ u ∈ CurtisTits.rankOne (minusDatum n hirr).rootGroup i,
        ∀ v ∈ CurtisTits.rankOne (minusDatum n hirr).rootGroup j, u * v = v * u := by
  have := fact_shortField hirr
  intro i j hij u hu v hv
  have hi : i.val + 1 < n - 1 := by have := j.2; omega
  rw [rankOne_minusDatum_long hirr hi] at hu
  obtain ⟨A, rfl⟩ := hu
  by_cases hj : j.val + 1 < n - 1
  · rw [rankOne_minusDatum_long hirr hj] at hv
    obtain ⟨B, rfl⟩ := hv
    exact (commute_rLong_rLong hi hj hij A B).eq
  · rw [rankOne_minusDatum_short hirr hj] at hv
    obtain ⟨B, rfl⟩ := hv
    exact (commute_rLong_shortBlock hirr hi hij A B).eq

theorem linearBlockStandardPair_minusDatum (h2 : (2 : F) ≠ 0) (hn : 4 ≤ n) {i j : Fin (n - 1)}
    (hij : i.val + 1 = j.val) (hj : j.val + 1 < n - 1) :
    ∃ W, LinearBlockStandardPair F W (CurtisTits.rankOne (minusDatum n hirr).rootGroup i)
      (CurtisTits.rankOne (minusDatum n hirr).rootGroup j) := by
  have hi : i.val + 1 < n - 1 := by omega
  obtain ⟨emb, hinj, h0, h1⟩ := exists_sl3_minus h2 hn b c hij hi hj
  exact linearBlockStandardPair_of_levi emb hinj (by rw [rankOne_minusDatum_long hirr hi, h0])
    (by rw [rankOne_minusDatum_long hirr hj, h1])

theorem twistedB2BlockStandardPair_minusDatum (h2 : (2 : F) ≠ 0) (hn : 4 ≤ n) {i j : Fin (n - 1)}
    (hia : i.val + 3 = n) (hjb : j.val + 2 = n) :
    ∃ W, TwistedB2BlockStandardPair hirr W (CurtisTits.rankOne (minusDatum n hirr).rootGroup i)
      (CurtisTits.rankOne (minusDatum n hirr).rootGroup j) := by
  have := fact_shortField hirr
  have hn3 : 3 ≤ n := by omega
  have hi : i.val + 1 < n - 1 := by omega
  have hj : ¬ j.val + 1 < n - 1 := by omega
  have hinj := spinGroupMap_minusShift_injective h2 n hn3 hirr
  have hl := minusShift_comp_longBlock (b := b) (c := c) hn3 hia hi
  have hs := minusShift_comp_shortBlock hn3 hirr hjb
  refine ⟨((minusShift n hn3 b c).spinGroupMap).range, (minusShift n hn3 b c).spinGroupMap, rfl,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [(MonoidHom.ker_eq_bot_iff _).mpr hinj]
    exact bot_le
  · change Function.Injective ((minusShift n hn3 b c).spinGroupMap.comp (minusLongBlock b c))
    rw [hl]
    exact rLong_injective hi
  · change Function.Injective ((minusShift n hn3 b c).spinGroupMap.comp (shortBlock hirr 3 finOne))
    rw [hs]
    exact shortBlock_injective hirr h2 n j
  · change (minusLongBlock b c).range.map (minusShift n hn3 b c).spinGroupMap = _
    rw [← MonoidHom.range_comp, hl, rankOne_minusDatum_long hirr hi]
  · change (shortBlock hirr 3 finOne).range.map (minusShift n hn3 b c).spinGroupMap = _
    rw [← MonoidHom.range_comp, hs, rankOne_minusDatum_short hirr hj]

end Model

end CFSG.ClassicalInvolution.WeakCT
