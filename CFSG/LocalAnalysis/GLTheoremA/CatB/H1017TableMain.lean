module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017TableRows
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017LyFive
public import CFSG.LocalAnalysis.GLTheoremA.S8.I1016HN

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Solomon.Coordinator (sporOrd SporadicOrdersTable)


theorem twoRankLe_five_hn : TwoRankLe 5 .HN 2 := by
  intro K _ _ hcat
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  simp only [S8.sporIs] at hi
  subst hi
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.HN.nonempty_mulEquiv
  let ψ : K ≃* CFSG.Blueprint.NativeSporadic.HN := e.trans b.symm
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine glaTwoLocalRank_le_of_card_le (by norm_num) fun R E hR hR2 hEN hE => ?_
  by_contra hlt
  push Not at hlt
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 (isPGroup_of_elemAbelian hE)
  have h3 : 5 ^ 3 ≤ Nat.card E := by
    rw [hm] at hlt ⊢
    exact Nat.pow_le_pow_right (by norm_num)
      (by by_contra h; push Not at h; exact absurd hlt (not_lt.2 (Nat.pow_le_pow_right (by norm_num) (by omega))))
  have := (S8.HNRows.i1016_HN_native ψ (by norm_num) (by norm_num) hE hR2 hR hEN h3).1
  norm_num at this

structure I1017ResidualRows : Prop where
  j3 : TwoRankLe 3 .J3 2
  mclthree : TwoRankLe 3 .McL 2
  co1 : TwoRankLe 5 .Co1 2
  b : TwoRankLe 5 .B 2
  mseven : TwoRankLe 7 .M 2
  mthirteen : TwoRankLe 13 .M 2

theorem i1017TableFact_of_residual (h : I1017ResidualRows) : I1017TableFact :=
  i1017TableFact_of_rows CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds
    (i1017CubicRows_holds CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds)
    ⟨h.j3, h.mclthree, h.co1, twoRankLe_five_hn, twoRankLe_five_ly, h.b, h.mseven, h.mthirteen⟩

end CFSG.LocalAnalysis.GLTheoremA.H1017
