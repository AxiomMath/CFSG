module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureCases
public import CFSG.RankThree.PartOne.CTP.StrongPLinear
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerActionN1Common

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Open

variable {K : Type} [Group K] [Finite K] {p : ℕ}

theorem pRank_le_of_card_le (hp : p.Prime) {H : Subgroup K} {j : ℕ} (h : Nat.card H ≤ p ^ j) :
    CFSG.Open.pRank p H ≤ j := by
  unfold CFSG.Open.pRank
  apply csSup_le
  · refine ⟨0, ⊥, bot_le, ⟨⟨⟨fun a b => Subsingleton.elim (a * b) (b * a)⟩⟩, fun x hx => ?_⟩, by simp⟩
    rw [Subgroup.mem_bot.1 hx, one_pow]
  · rintro i ⟨E, hEH, -, hcard⟩
    have h1 : p ^ i ≤ p ^ j := hcard ▸ (Subgroup.card_le_of_le hEH).trans h
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 h1

theorem WCOn.of_not_isMulCommutative
    (h : ∀ P : Sylow p K, ¬ IsMulCommutative (P : Subgroup K)) : WCOn p K :=
  fun P hP => absurd hP (h P)

theorem WCOn.of_hasNoncommPair [Fact p.Prime]
    (h : CFSG.RankThree.PartOne.StrongP.HasNoncommPair p K) : WCOn p K := by
  obtain ⟨x, y, -, -, hxy, hpg⟩ := h
  exact WCOn.of_not_isMulCommutative fun P =>
    InnerAction.not_isMulCommutative_of_noncomm_pSubgroup hpg
      (Subgroup.subset_closure (Set.mem_insert x {y}))
      (Subgroup.subset_closure (Set.mem_insert_of_mem x rfl)) hxy P.isPGroup' P.not_dvd_index

theorem WCOn.of_factorization_le_one [Fact p.Prime] (h : (Nat.card K).factorization p ≤ 1) :
    WCOn p K := by
  intro P _ hrank
  exfalso
  have hcard : Nat.card (P : Subgroup K) ≤ p ^ 1 := by
    rw [P.card_eq_multiplicity]
    exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos h
  have := pRank_le_of_card_le Fact.out hcard
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
