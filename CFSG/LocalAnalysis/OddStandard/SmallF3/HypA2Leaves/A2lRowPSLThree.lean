module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lRowPSL
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCoverL4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lRows

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG.ComponentClassification Matrix CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.PartTwo.Census
open scoped MatrixGroups

theorem a2l_rowPSL_three (hC : HypA2.ChevOddInChev2) {X : Type} [Group X] [Finite X] {n : ℕ}
    (hn : 5 ≤ n) (hm : LieModel X .PSL n 3 1) : a2lDatum X := by
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := hm.statedClassicalModel (by decide)
  haveI := Fintype.ofFinite F
  obtain ⟨m, rfl⟩ : ∃ m, n = 4 + m := ⟨n - 4, by omega⟩
  have hF : Fintype.card F = 3 := by rw [← Nat.card_eq_fintype_card, hcard]; norm_num
  have h2 : (2 : F) ≠ 0 :=
    CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F (by rw [hcard]; decide)
  haveI := Fintype.ofFinite (GaloisField 3 2)
  have hE : Fintype.card (GaloisField 3 2) = 9 := by
    rw [← Nat.card_eq_fintype_card, card_galoisField_three_two]
  have hq : CFSG.IsQuasisimple SL(4, F) :=
    CFSG.RankThree.Classical2.isQuasisimple_specialLinearGroup (by norm_num)
  set J : Subgroup SL(4 + m, F) := (blockSL F 4 m).range with hJ
  let eJ : ↥J ≃* SL(4, F) := (MonoidHom.ofInjective a2l_blockSL_injective).symm
  have hqJ : CFSG.IsQuasisimple ↥J := CFSG.IsQuasisimple.of_mulEquiv eJ hq
  have hcenJ : Nat.card (center ↥J) ≤ 2 := by
    have h1 := Subgroup.card_map_of_injective (K := center ↥J) (f := eJ.toMonoidHom) eJ.injective
    have hmap : (center ↥J).map eJ.toMonoidHom = center SL(4, F) := Subgroup.map_center_eq eJ
    rw [hmap] at h1
    rw [← h1]
    classical
    exact ComponentClassification.CatFactsL4U4.card_center_SL_four_le (by rw [hF])
  have h2J : IsPGroup 2 ↥(center ↥J) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hpos : 0 < Nat.card (center ↥J) := Nat.card_pos
    rcases (show Nat.card (center ↥J) = 1 ∨ Nat.card (center ↥J) = 2 by omega) with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [h]; norm_num)
    · exact IsPGroup.of_card (n := 1) (by rw [h]; norm_num)
  let eS : ↥J ⧸ center ↥J ≃* StatedProj (StatedSL 4 F) :=
    (QuotientGroup.congr _ _ eJ (Subgroup.map_center_eq eJ)).trans
      (projectiveSpecialLinearGroupEquivStatedProj 4 F)
  have hmJ : LieModel (↥J ⧸ center ↥J) .PSL 4 3 1 :=
    Or.inl ⟨by decide, ⟨Nat.prime_three, le_rfl, by norm_num, by simp, by simp⟩, F,
      inferInstance, inferInstance, hcard, ⟨eS⟩⟩
  have hTU : HypA2.TypU ↥J := a2l_typU_of_not_inChev2 hqJ h2J
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hmJ)))))) (a2l_not_inChev2_psl43 hC hmJ)
  have hd := a2lDatum_psl_block h2 (k := 4) (m := m) (by norm_num) (by omega) (q₀ := 9)
    (by decide) (by norm_num) hE (a2lNineSL4 hF) (a2lNineSL4_injective hF)
    (a2lNineSL4_negOne hF) hq hTU
  exact a2lDatum_of_mulEquiv
    (e.trans (projectiveSpecialLinearGroupEquivStatedProj (4 + m) F).symm).symm hd

theorem a2l_rowPSL (hC : HypA2.ChevOddInChev2) : a2lRowPSL := by
  intro X _ _ n f hn hf hm
  have hf1 : 1 ≤ f := hm.admissible.2.1
  rcases Nat.lt_or_ge f 2 with hlt | hge
  · obtain rfl : f = 1 := by omega
    exact a2l_rowPSL_three hC (by omega) hm
  · exact a2l_rowPSL_two hn hge hm

end CFSG.OddStandard.SmallF3.HypA2Leaves
