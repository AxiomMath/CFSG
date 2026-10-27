module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieTools
public import CFSG.LieType.SeitzGeneration.ExtSeitzG2Odd
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuous

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross.Untw

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration

theorem pRank_le_one_of_rankLE1 {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (h : RankLE1 p K) (H : Subgroup K) : CFSG.Open.pRank p H ≤ 1 := by
  unfold CFSG.Open.pRank
  apply csSup_le
  · refine ⟨0, ⊥, bot_le, ⟨⟨⟨fun a b => Subsingleton.elim (a * b) (b * a)⟩⟩, fun x hx => ?_⟩, by simp⟩
    rw [Subgroup.mem_bot.1 hx, one_pow]
  · rintro i ⟨E, -, hE, hcard⟩
    have h1 : p ^ i ≤ p ^ 1 := by
      rw [pow_one, ← hcard]
      exact h E hE
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 h1

theorem WCOn.of_rankLE1 {K : Type} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    (h : RankLE1 p K) : WCOn p K :=
  WCOn.of_pRank_top_le_one (pRank_le_one_of_rankLE1 Fact.out h ⊤)

section G2

variable {F : Type} [Field F] [Finite F] {p : ℕ}

theorem rankLE1_G2 (hp : p.Prime) (hp5 : 5 ≤ p) (hpK : ¬ p ∣ Nat.card F)
    (hnd : ¬ p ∣ Nat.card F ^ 2 - 1) : RankLE1 p (adjointGroup Tag.G2 F) := by
  haveI : Finite (ModGL Tag.G2 F) := finite_modGL
  refine CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE1_of_pRank hp fun hdvd => ?_
  by_cases h2 : ringChar F = 2
  · haveI : CharP F 2 := h2 ▸ ringChar.charP F
    haveI : Fintype F := Fintype.ofFinite F
    obtain ⟨n, -, hn⟩ := FiniteField.card F 2
    exact CFSG.RankThree.PartOne.K128.pRank_le_one_G2 F hp hp5
      (by rw [Nat.card_eq_fintype_card]; exact hn) n.pos hdvd hnd
  · haveI : Fintype F := Fintype.ofFinite F
    obtain ⟨n, hℓ, hn⟩ := FiniteField.card F (ringChar F)
    have hodd : Odd (Nat.card F) := by
      rw [Nat.card_eq_fintype_card, hn]
      exact (hℓ.odd_of_ne_two h2).pow
    exact pRank_le_one_adjointG2_odd F hodd hp hp5 hpK hdvd hnd

end G2

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross.Untw
