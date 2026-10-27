module

public import CFSG.Open.LocalVocabulary
public import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank
import CFSG.LocalAnalysis.SectionRank.SQT

public section

open scoped commutatorElement

namespace CFSG.GroupTheory

theorem card_quotient_frattini_le_pow_four {q : ℕ} [Fact q.Prime] {W : Type} [Group W]
    [Finite W] (hW : IsPGroup q W) (hexp : ∀ x : W, x ^ q = 1)
    (hcl : ⁅⁅(⊤ : Subgroup W), (⊤ : Subgroup W)⁆, (⊤ : Subgroup W)⁆ = ⊥)
    (hrank : CFSG.Open.pRank q (⊤ : Subgroup W) ≤ 3) :
    Nat.card (W ⧸ frattini W) ≤ q ^ 4 := by
  classical
  have hclass : _root_.commutator W ≤ Subgroup.center W := by
    simpa [_root_.commutator_def] using
      (Subgroup.commutator_top_right_eq_bot_iff_le_center
        (H := _root_.commutator W) (G := W)).mp hcl
  have hfr : frattini W = _root_.commutator W :=
    CFSG.RankThree.PartTwo.frattini_eq_commutator (p := q) hW hexp
  have hrank' : CFSG.pRank q W ≤ 3 := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top q W]
    exact hrank
  have hbound : CFSG.pRank q (W ⧸ _root_.commutator W) ≤ 4 :=
    (CFSG.RankThree.PartTwo.class_two_small_rank_order_bounds (p := q) hW hexp hclass).2.2
      hrank'
  obtain ⟨k, hk⟩ := (hW.to_quotient (_root_.commutator W)).exists_card_eq
  have hQcomm : IsMulCommutative (W ⧸ _root_.commutator W) :=
    CFSG.RankThree.PartTwo.isMulCommutative_quotient_commutator
  have hQexp : ∀ x : W ⧸ _root_.commutator W, x ^ q = 1 :=
    CFSG.RankThree.PartTwo.quotient_pow_eq_one hexp _
  have htopcomm : IsMulCommutative (⊤ : Subgroup (W ⧸ _root_.commutator W)) :=
    ⟨⟨fun a b => Subtype.ext
      (hQcomm.is_comm.comm (a : W ⧸ _root_.commutator W) b)⟩⟩
  have htopcard : Nat.card (⊤ : Subgroup (W ⧸ _root_.commutator W)) = q ^ k := by
    rw [Subgroup.card_top, hk]
  have hk_le : k ≤ CFSG.pRank q (W ⧸ _root_.commutator W) :=
    CFSG.RankThree.PartTwo.le_pRank_of_isMulCommutative (Fact.out : q.Prime) hQexp
      htopcomm htopcard
  have hk4 : k ≤ 4 := hk_le.trans hbound
  have hcard : Nat.card (W ⧸ _root_.commutator W) ≤ q ^ 4 := by
    rw [hk]
    exact Nat.pow_le_pow_right (Fact.out : q.Prime).pos hk4
  calc
    Nat.card (W ⧸ frattini W) = Nat.card (W ⧸ _root_.commutator W) := by rw [hfr]
    _ ≤ q ^ 4 := hcard

end CFSG.GroupTheory
