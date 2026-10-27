module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.UpperE8Levi
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6Levi

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.Assembly CFSG.ComponentClassification.CatLeafProof
open scoped MatrixGroups


@[expose] def e6D4Node : Fin 4 → Fin (Tag.rank .E6) :=
  ![e6Node 4, e6Node 3, e6Node 2, e6Node 1]

theorem e6D4_adj : ∀ i j : Fin 4, Timmesfeld.edgeD 4 i j →
    e6D4Node i ≠ e6D4Node j ∧ Tag.cartan .E6 (e6D4Node i) (e6D4Node j) = -1 ∧
      Tag.cartan .E6 (e6D4Node j) (e6D4Node i) = -1 ∧
      ∃ l, ¬ (3 : ℤ) ∣ Tag.cartan .E6 (e6D4Node i) l + 2 * Tag.cartan .E6 (e6D4Node j) l := by
  decide +kernel

theorem e6D4_nadj : ∀ i j : Fin 4, i ≠ j → ¬ Timmesfeld.edgeD 4 i j →
    ¬ Timmesfeld.edgeD 4 j i →
    e6D4Node i ≠ e6D4Node j ∧ Tag.cartan .E6 (e6D4Node i) (e6D4Node j) = 0 ∧
      Tag.cartan .E6 (e6D4Node j) (e6D4Node i) = 0 := by
  decide +kernel

theorem mem_range_e6D4Node (j : Fin Tag.E6.rank) :
    j ∈ Set.range e6D4Node ↔ j.val ≠ 0 ∧ j.val ≠ 5 := by
  fin_cases j <;> decide

theorem e6D4Node_range : Set.range e6D4Node =
    {i : Fin Tag.E6.rank | i.val ≠ 0 ∧ i.val ≠ 5} := by
  ext j
  rw [mem_range_e6D4Node]
  simp

theorem rkOmPlus_four_le (Q p : ℕ) :
    CFSG.LocalAnalysis.RankThreeUC.S15.rkOmPlus 4 Q p ≤ 4 := by
  unfold CFSG.LocalAnalysis.RankThreeUC.S15.rkOmPlus
  split_ifs with h
  · have he8 : CFSG.LocalAnalysis.RankThreeUC.S15.eP Q p ∣ 8 := by simpa using h.1
    have hnot4 : ¬ CFSG.LocalAnalysis.RankThreeUC.S15.eP Q p ∣ 4 := by simpa using h.2
    have hle : CFSG.LocalAnalysis.RankThreeUC.S15.eP Q p ≤ 8 :=
      Nat.le_of_dvd (by norm_num) he8
    have hpos : 0 < CFSG.LocalAnalysis.RankThreeUC.S15.eP Q p :=
      Nat.pos_of_dvd_of_pos he8 (by norm_num)
    have h8 : CFSG.LocalAnalysis.RankThreeUC.S15.eP Q p = 8 := by
      interval_cases (CFSG.LocalAnalysis.RankThreeUC.S15.eP Q p) <;> simp_all
    rw [h8]
    norm_num
  · exact Nat.div_le_self 4 _

theorem card_le_pow_four_subsystemGroup_e6D4 {F : Type} [Field F] [Finite F] [CharP F 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E : Subgroup (ModGL TwistTag.E6.tag F)}
    (hE : E ≤ subsystemGroup TwistTag.E6.tag F {i | i.val ≠ 0 ∧ i.val ≠ 5})
    (hEel : CFSG.Open.IsElemAbelian p E) : Nat.card E ≤ p ^ 4 := by
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, -, hF⟩ := FiniteField.card F 2
  have hFn : Nat.card F = 2 ^ (n : ℕ) := by rw [← Fintype.card_eq_nat_card]; exact hF
  have hn : 1 ≤ (n : ℕ) := CFSG.Quasithin.R3c2.one_le_of_natCard_eq_two_pow hFn
  obtain ⟨O, C, hE'⟩ := exists_e6_chevalleyExtras F
  obtain ⟨ρ, hρ, hcomm, hψ⟩ := exists_levi_frame hE' rfl e6D4Node e6D4_adj e6D4_nadj
  have hadm : StatedLieAdmissible .POmegaPlus 4 2 (n : ℕ) :=
    ⟨Nat.prime_two, hn, by norm_num⟩
  obtain ⟨Ψ, -, hrange, hqs, hmodel⟩ :=
    spinPlus_frame_subgroup (n := 4) hadm (by norm_num) hFn
      (U := fun k =>
        CFSG.LieType.CurtisTits.rankOne (adjDatum (rootOperatorFamily .E6) F).rootGroup
          (e6D4Node k))
      hcomm hρ hψ
  have hqs' : CFSG.IsQuasisimple ↥Ψ.range := by
    rw [hrange]; exact hqs
  have hmodel' : LieModel (↥Ψ.range ⧸ Subgroup.center ↥Ψ.range) .POmegaPlus 4 2 (n : ℕ) := by
    rw [hrange]; exact hmodel
  have hT : CFSG.LocalAnalysis.RankThreeUC.S15.LieOddRankChev :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20x_lieOddRankChev
      CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  have hSCM : CFSG.Open.StatedClassicalModel
      (↥Ψ.range ⧸ Subgroup.center ↥Ψ.range) .POmegaPlus 4 2 (n : ℕ) :=
    hmodel'.statedClassicalModel (by decide)
  have hqsOpen : CFSG.Open.IsQuasisimple ↥Ψ.range :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff ↥Ψ.range).2.2.1.1 hqs'
  have hpr := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20w_pRank_pomegaPlus
    (K := ↥Ψ.range) hT hqsOpen hSCM (r := p) hp hp2
  have hS : CFSG.Open.pRank p (⊤ : Subgroup Ψ.range) ≤ 4 := by
    rw [hpr]
    exact rkOmPlus_four_le (2 ^ (n : ℕ)) p
  have hEmap : E ≤ Ψ.range.map (adjointGroup Tag.E6 F).subtype := by
    rw [hrange, map_subtype_iSup_rankOne e6D4Node, e6D4Node_range]
    exact hE
  exact card_le_pow_of_le_map_subtype hp hS hEmap hEel

end CFSG.LocalAnalysis.GLTheoremA
