module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureSporLines
public import CFSG.HardMathSupport.Timmesfeld.SporadicRank.SpecExtract

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.SporadicRank

theorem wcOn_of_sylowModuleData {X : Type} [Group X] [Finite X] {p n : ℕ} [Fact p.Prime]
    {tm : List (List ℕ)} (h : SylowModuleData X p n tm)
    (hf : n < (Nat.card X).factorization p) : WCOn p X := by
  obtain ⟨D, P, hn, -, -, hP, hDP, -, hC, -⟩ := h
  refine WCOn.of_selfcentralizing_in_sylow hP hDP hC ?_
  rw [D.card_span Fact.out, hP, hn]
  exact Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt hf

theorem wcOn_of_sylowModuleCover {X : Type} [Group X] [Finite X] {p n : ℕ} [Fact p.Prime]
    {tm : List (List ℕ)} (h : SylowModuleCover X p n tm)
    (hf : n < (Nat.card X).factorization p) : WCOn p X := by
  obtain ⟨D, P, hn, -, -, hP, hDP, -, hC, -⟩ := h
  refine WCOn.of_selfcentralizing_in_sylow hP hDP hC ?_
  rw [D.card_span Fact.out, hP, hn]
  exact Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt hf

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
