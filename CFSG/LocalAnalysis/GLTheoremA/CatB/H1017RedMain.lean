module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017RedTwist
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017RedExcl
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017RedCases
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017RedCenter
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017RedMore

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S8
open CFSG.HardMathSupport.Timmesfeld.Coordinator

structure I1017Inputs : Prop where
  out : SporadicOuterLeTwo
  mult : CFSG.RankThree.PartTwo.Sec4.Census.SporadicMultipliers
  table : I1017TableFact
  co3 : I1017CoThreeTwist
  fi22 : I1017FiTwoTwoTwist
  fi23 : I1017FiTwoThreeTwist
  baby : I1017BabyTwist
  fi22a : I1017FiTwoTwoAttained
  fi22c : I1017CoverFiTwoTwo
  fi23a : I1017FiTwoThreeAttained
  babya : I1017BabyAttained
  rows : I1016RowFacts
  ranks : I1017RowRanks

theorem i1017_of_inputs (h : I1017Inputs) (G : Type) [Group G] [Finite G] (p : ℕ) :
    I1017At G p := by
  intro hp hp2 B x L hBmax hm4 hxB hx1 hL _ hBN hsp hcm _ hT
  obtain ⟨T, hTL, hT2, hBT, htw⟩ := hT
  have hB : IsElemAbelian p B := hBmax.1
  have hBc : Nat.card B = p ^ GLATwoLocalRank p G := hBmax.2.1
  have hxp : x ^ p = 1 := hB.2 x hxB
  obtain ⟨E, V, hE, hEc, hV2, hEV, hEtw⟩ :=
    exists_twist_pSimple h.out hp hp2 hB hxB hx1 hL hBN hsp hcm hTL hT2 hBT htw
  have hEc' : Nat.card E = p ^ (GLATwoLocalRank p G - 1) := by
    have h1 : p ^ GLATwoLocalRank p G = p ^ (GLATwoLocalRank p G - 1) * p := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hBc, h1] at hEc
    exact Nat.eq_of_mul_eq_mul_right hp.pos hEc
  have hkS : GLATwoLocalRank p G - 1 ≤ GLATwoLocalRank p (PSimple p L) :=
    le_glaTwoLocalRank_of_twist hp hE hEc' hV2 hEV hEtw
  refine ⟨?_, fun row hrow => ?_⟩
  · rcases i1017_spor_cases h.table h.co3 h.fi22 h.fi23 h.baby hp hp2 hsp hE hEc' (by omega)
        hV2 hEV hEtw with ⟨hp3, hON⟩ | ⟨row, hrp, hrs⟩ | ⟨hp3, hs, hk⟩ | ⟨hp3, hs, hk⟩
    · subst hp3
      exact Or.inr ⟨rfl, hON⟩
    · exact Or.inl (exists_rowL_of_spor h.mult hL row hrp hrs)
    · subst hp3
      exact (i1017_not_fi22 h.fi22a h.fi22c (by omega) hxp hx1 hL hs
        (card_center_pQuot_of_spor h.mult Nat.prime_three hL hs (by decide))).elim
    · subst hp3
      have hZ : Nat.card (Subgroup.center (PQuot 3 L)) = 1 := by
        rcases hs with hs | hs
        · exact center_pQuot_eq_bot_of_spor h.mult Nat.prime_three hL hs (by decide)
        · exact center_pQuot_eq_bot_of_spor h.mult Nat.prime_three hL hs (by decide)
      exact (i1017_not_fi23_baby h.fi23a h.babya (by omega) hxp hx1 hL hs hZ).elim
  ·
    have hrank : GLATwoLocalRank p (PSimple p L) ≤ row.rank - 1 := by
      have h1 := h.rows row (PSimple p L) hrow.2.1
      rwa [← hrow.1] at h1
    have hr1 : 1 ≤ row.rank := by cases row <;> decide
    obtain ⟨E', hE'L, hE'ab, hE'c⟩ := i1017_moreover h.ranks hx1 hxp hL row hrow
    refine ⟨E', hE'L.trans (sup_le_sup_left ((Subgroup.zpowers_le).2 hxB) _), hE'ab, ?_⟩
    rw [hBc]
    exact lt_of_le_of_lt (Nat.pow_le_pow_right hp.pos (by omega)) hE'c

end CFSG.LocalAnalysis.GLTheoremA.H1017

end
