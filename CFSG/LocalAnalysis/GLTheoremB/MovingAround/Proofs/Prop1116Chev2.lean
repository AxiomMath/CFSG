module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop1116Design
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.RankThree.PartTwo.KFacts.KS10L27Aut

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut autBar barOf innerAut)
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple)

namespace Prop1116Design

theorem card_statedProj_two_seven {S : Type} [Group S] (h : IsLpType 2 7 S) : Nat.card S = 168 := by
  obtain ⟨F, fld, fin, hc, ⟨f⟩⟩ := h
  rw [Nat.card_congr f.toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := F) (n := 2) (by norm_num), hc]
  decide

theorem card_psl2_27_of_isL27 {X : Type} [Group X] (h : IsLTwoTwentySeven X) : Nat.card X = 9828 := by
  obtain ⟨e⟩ := h
  exact (Nat.card_congr e.toEquiv).trans CFSG.RankThree.PartTwo.KFacts.card_psl2_27

@[expose] def InputChevTwoOdd : Prop :=
  ∀ (S : Type) [Group S] (q : ℕ), q.Prime → q ≠ 2 → q ≠ 3 → IsChevSimple q S → IsChevSimple 2 S →
    (IsAltType 5 S ∧ q = 5) ∨ (IsLpType 2 7 S ∧ q = 7)

@[expose] def InputSchurFiveSeven : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ}, p.Prime → p ≠ 2 → ∀ {X L : Subgroup G},
    GLAPComponent p X L →
    (IsAltType 5 (barOf p L ⧸ Subgroup.center (barOf p L)) ∨
      IsLpType 2 7 (barOf p L ⧸ Subgroup.center (barOf p L))) → Subgroup.center (barOf p L) = ⊥

end Prop1116Design

open Prop1116Design

end CFSG.LocalAnalysis.GLTheoremB.MovingAround
