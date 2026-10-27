module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTwoEleven
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.HSCentralExt
public import CFSG.Sporadic.HN.Local.Main
public import CFSG.RankThree.PartTwo.Census.Sporadic.Centralizer

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup CFSG.OddStandard.AltStdBal CFSG.Blueprint CFSG.Blueprint.NativeSporadic

@[expose] def ShapeTwoTenStdHS : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (z u : G),
    Setting G L 10 → Cyc L Q z → ShapeTwo L Q z u →
      ∃ K : Subgroup G, CFSG.EvenSporadicStandard.StdHyp G K ∧ IsSporadic (K ⧸ center K) .HS

@[expose] def ShapeTwoSmallNine : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (n : ℕ) (z u : G),
    Setting G L n → Cyc L Q z → ShapeTwo L Q z u → n ≤ 9 → False

theorem card_centralizer_mulEquiv {A B : Type*} [Group A] [Group B] (φ : A ≃* B) (a : A) :
    Nat.card (centralizer ({a} : Set A)) = Nat.card (centralizer ({φ a} : Set B)) := by
  refine Nat.card_congr ⟨fun x => ⟨φ x, ?_⟩, fun y => ⟨φ.symm y, ?_⟩, ?_, ?_⟩
  · have hx := mem_centralizer_singleton_iff.1 x.2
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hx]
  · have hy := mem_centralizer_singleton_iff.1 y.2
    rw [mem_centralizer_singleton_iff]
    apply φ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hy]
  · intro x
    exact Subtype.ext (φ.symm_apply_apply x)
  · intro y
    exact Subtype.ext (φ.apply_symm_apply y)

theorem hn_card_centralizer_ne
    (g : NativeSporadic.HN)
    (hg : orderOf g = 2) :
    Nat.card (centralizer ({g} : Set NativeSporadic.HN)) ≠ 2 * Nat.factorial 10 := by
  have hg2 : g ^ 2 = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  have hg1 : g ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hg
    omega
  intro hC
  rcases CFSG.Sporadic.HN.Local.hn_involution_cover g hg2 hg1 with hc | hc
  · rw [← CFSG.RankThree.PartTwo.Census.card_centralizer_of_isConj hc,
      CFSG.Sporadic.HN.Local.hn_card_centralizer_t2] at hC
    norm_num [Nat.factorial] at hC
  · rw [← CFSG.RankThree.PartTwo.Census.card_centralizer_of_isConj hc,
      CFSG.Sporadic.HN.Local.hn_card_centralizer_t4] at hC
    norm_num [Nat.factorial] at hC

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {z u : G}

theorem false_of_stdHyp_hs_ten
    (h6 : CFSG.EvenSporadicStandard.HSMcLLyExclusion)
    (h7 : CFSG.EvenSporadicStandard.TwoHSGivesHN)
    (h : Setting G L 10) (d : Cyc L Q z) (T : ShapeTwo L Q z u) {K : Subgroup G}
    (hK : CFSG.EvenSporadicStandard.StdHyp G K) (hq : IsSporadic (K ⧸ center K) .HS) : False := by
  have hqs := hK.standard.1
  by_cases hZ : center K = ⊥
  · obtain ⟨φ⟩ := hq
    exact (h6 G K hK).1
      ⟨(QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans φ⟩
  · have hperf : Group.IsPerfect K := ⟨hqs.1⟩
    have h2 : Nat.card (center K) = 2 :=
      CFSG.EvenSporadicStandard.HSStd.Zassenhaus.card_center_eq_two_of_ne_bot hperf hq hZ
    obtain ⟨φ⟩ := h7 G K hK h2 hq
    obtain ⟨e⟩ := h.iso
    have hCz := card_centralizer_eq_two_mul_factorial h d T.card T.cent T.outer T.sq e
    rw [card_centralizer_mulEquiv φ z] at hCz
    have hord : orderOf (φ z) = 2 := by rw [MulEquiv.orderOf_eq]; exact d.order
    exact hn_card_centralizer_ne (φ z) hord hCz

theorem false_of_shapeTwo_ten_of_stdHS
    (hHS : ShapeTwoTenStdHS) (h6 : CFSG.EvenSporadicStandard.HSMcLLyExclusion)
    (h7 : CFSG.EvenSporadicStandard.TwoHSGivesHN)
    (h : Setting G L 10) (d : Cyc L Q z) (T : ShapeTwo L Q z u) : False := by
  obtain ⟨K, hK, hq⟩ := hHS G L Q z u h d T
  exact false_of_stdHyp_hs_ten h6 h7 h d T hK hq

theorem shapeTwoSmallTen_of_nine
    (h9 : ShapeTwoSmallNine) (hHS : ShapeTwoTenStdHS)
    (h6 : CFSG.EvenSporadicStandard.HSMcLLyExclusion)
    (h7 : CFSG.EvenSporadicStandard.TwoHSGivesHN) : ShapeTwoSmallTen := by
  intro G _ _ L Q n z u h d T hn
  rcases Nat.lt_or_ge n 10 with h10 | h10
  · exact h9 G L Q n z u h d T (by omega)
  · obtain rfl : n = 10 := by omega
    exact false_of_shapeTwo_ten_of_stdHS hHS h6 h7 h d T

end CFSG.OddStandard.AltStdSec
