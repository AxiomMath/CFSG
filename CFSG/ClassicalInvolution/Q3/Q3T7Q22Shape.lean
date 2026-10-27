module

public import CFSG.ClassicalInvolution.Q3.Q3T7Q2202
public import CFSG.ClassicalInvolution.Q3.Q3MTShapeB
public import CFSG.ClassicalInvolution.Q3.Q3MTG2
public import CFSG.ClassicalInvolution.Q3.Q3MTTD4
public import CFSG.ClassicalInvolution.Q3.Q3MTStar

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.MuTab

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.MuTab
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Q3.Q3MT
open scoped MatrixGroups



variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem exists_starEdge_of_s3 (hT : Q3T8.Asc77.TransSection Φ) (hne : Φ.Nonempty)
    {t : StatedLieTag} {k : ℕ} (hL : HasLieType 3 1 Φ t k)
    (hk : muKind (piSign 3 1) t k = .s3) : ∃ K ∈ Φ, (omegaStarNbr Φ K).Nonempty := by
  have hΩ : HypOmegaModU (.sl2 3 1) Φ := hT.hyp
  obtain ⟨e, ⟨M⟩⟩ := Ih8Model.exists_datum_of_hasLieType hT.hyp hT.gen hL
  rcases muKind_cases3 (piSign 3 1) t k with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | hlarge
  · rw [piSign_three_one] at hk; simp [muKind] at hk
  · rw [piSign_three_one] at hk; simp [muKind] at hk
  · rw [piSign_three_one] at hk; simp [muKind] at hk
  · have hG2 : Assembly.LowTwoRank.StatedLieTag.PSU ≠ .G2 := by decide
    have hD4 : Assembly.LowTwoRank.StatedLieTag.PSU ≠ .trialityD4 := by decide
    have he := ih8Model_exp_eq_one M hD4
    subst he
    obtain ⟨R₁, hR₁, R₂, hR₂, W, hW⟩ :=
      M.muTab_unitaryPair_psu (by norm_num : (3 : ℕ) ≠ 2) hne
    have hadj := dstarAdj_unitary3 M hΩ hG2 hD4 hR₁ hR₂ hW
    rcases hadj.2 with h | h
    · exact ⟨R₁.map M.ψ, M.map_mem hR₁, _, h⟩
    · exact ⟨R₂.map M.ψ, M.map_mem hR₂, _, h⟩
  · rw [piSign_three_one] at hk; simp [muKind] at hk
  · rw [piSign_three_one] at hk; simp [muKind] at hk
  · rw [piSign_three_one] at hk; simp [muKind] at hk
  · rw [piSign_three_one] at hk; simp [muKind] at hk
  · rw [piSign_three_one] at hk; simp [muKind] at hk
  · rw [piSign_three_one] at hk; simp [muKind] at hk
  · exact g2_omegaStarNbr_nonempty_three M hΩ hne
  · exact td4_omegaStarNbr_nonempty_three M hΩ hT.trans hne
  · rw [hlarge] at hk
    exact absurd hk (by decide)

theorem shape_psp2 (hT : Q3T8.Asc77.TransSection Φ) (hne : Φ.Nonempty)
    (hL : HasLieType 3 1 Φ .PSp 2) : KindShape Φ (muKind (piSign 3 1) .PSp 2) := by
  have hΩ : HypOmegaModU (.sl2 3 1) Φ := hT.hyp
  obtain ⟨e, ⟨M⟩⟩ := Ih8Model.exists_datum_of_hasLieType hT.hyp hT.gen hL
  have hG2 : Assembly.LowTwoRank.StatedLieTag.PSp ≠ .G2 := by decide
  have hD4 : Assembly.LowTwoRank.StatedLieTag.PSp ≠ .trialityD4 := by decide
  have he := ih8Model_exp_eq_one M hD4
  subst he
  rw [piSign_three_one, show muKind false .PSp 2 = .e4 by simp [muKind]]
  refine ⟨starSubset3 M hΩ hG2 hD4 fun R hR S hS hJ =>
    star_commutes_triv3 M hΩ hG2 hD4 (stdDich3Triv_psp M.admissible) hR hS hJ,
    noTriangle3 M hΩ hG2 hD4 ?_,
    edge_of_commuting3 M hΩ hne hG2 hD4 (exists_commuting_small_sp4 M.admissible)⟩
  intro A hA B hB S hS hAB hAS hBS cAB cAS cBS
  exact noThree_psp2 (by norm_num : (3 : ℕ) ≠ 2) M.admissible (M.cls_sub hA) (M.cls_sub hB)
    (M.cls_sub hS) hAB hAS hBS cAB cAS cBS

theorem shape_psl4 (hT : Q3T8.Asc77.TransSection Φ) (hne : Φ.Nonempty)
    (hL : HasLieType 3 1 Φ .PSL 4) : KindShape Φ (muKind (piSign 3 1) .PSL 4) := by
  have hΩ : HypOmegaModU (.sl2 3 1) Φ := hT.hyp
  obtain ⟨e, ⟨M⟩⟩ := Ih8Model.exists_datum_of_hasLieType hT.hyp hT.gen hL
  have hG2 : Assembly.LowTwoRank.StatedLieTag.PSL ≠ .G2 := by decide
  have hD4 : Assembly.LowTwoRank.StatedLieTag.PSL ≠ .trialityD4 := by decide
  have he := ih8Model_exp_eq_one M hD4
  subst he
  rw [piSign_three_one, show muKind false .PSL 4 = .e4 by simp [muKind]]
  refine ⟨starSubset3 M hΩ hG2 hD4 fun R hR S hS hJ =>
    star_commutes_lin3 M hΩ hG2 hD4 (stdDich3Lin_psl M.admissible) hR hS hJ,
    noTriangle3 M hΩ hG2 hD4 ?_,
    edge_of_commuting3 M hΩ hne hG2 hD4 (exists_commuting_small_psl4 M.admissible)⟩
  intro A hA B hB S hS hAB hAS hBS cAB cAS cBS
  exact noThree_psl4 (by norm_num : (3 : ℕ) ≠ 2) (M.cls_sub hA) (M.cls_sub hB) (M.cls_sub hS)
    hAB hAS hBS cAB cAS cBS

theorem shape_psu4 (hT : Q3T8.Asc77.TransSection Φ) (hne : Φ.Nonempty)
    (hL : HasLieType 3 1 Φ .PSU 4) : KindShape Φ (muKind (piSign 3 1) .PSU 4) := by
  have hΩ : HypOmegaModU (.sl2 3 1) Φ := hT.hyp
  obtain ⟨e, ⟨M⟩⟩ := Ih8Model.exists_datum_of_hasLieType hT.hyp hT.gen hL
  have hG2 : Assembly.LowTwoRank.StatedLieTag.PSU ≠ .G2 := by decide
  have hD4 : Assembly.LowTwoRank.StatedLieTag.PSU ≠ .trialityD4 := by decide
  have he := ih8Model_exp_eq_one M hD4
  subst he
  rw [piSign_three_one, show muKind false .PSU 4 = .s4 by simp [muKind]]
  have hMatch : ∀ A ∈ M.cls, ∀ B ∈ M.cls, ∀ S ∈ M.cls, A ≠ B → A ≠ S → B ≠ S → Commutes A B →
      Commutes A S → False := fun A hA B hB S hS hAB hAS hBS cAB cAS =>
    matching_psu4 (by norm_num : (3 : ℕ) ≠ 2) M.admissible (M.cls_sub hA) (M.cls_sub hB)
      (M.cls_sub hS) hAB hAS hBS cAB cAS
  obtain ⟨R₁, hR₁, R₂, hR₂, W, hW⟩ := M.muTab_unitaryPair_psu (by norm_num : (3 : ℕ) ≠ 2) hne
  obtain ⟨-, hnc⟩ := unitary_ne_nc3 M hG2 hD4 hR₁ hR₂ hW
  have hadj := dstarAdj_unitary3 M hΩ hG2 hD4 hR₁ hR₂ hW
  exact ⟨matching3 M hΩ hG2 hD4 hMatch,
    edge_of_commuting3 M hΩ hne hG2 hD4 (exists_commuting_small_su4 M.admissible),
    _, M.map_mem hR₁, dComp_ne3 M hΩ hG2 hD4 hMatch hR₁ hR₂ hnc hadj⟩

theorem shape_pOmegaOdd3 (hT : Q3T8.Asc77.TransSection Φ) (hne : Φ.Nonempty)
    (hL : HasLieType 3 1 Φ .POmegaOdd 3) : KindShape Φ (muKind (piSign 3 1) .POmegaOdd 3) := by
  have hΩ : HypOmegaModU (.sl2 3 1) Φ := hT.hyp
  obtain ⟨e, ⟨M⟩⟩ := Ih8Model.exists_datum_of_hasLieType hT.hyp hT.gen hL
  have hG2 : Assembly.LowTwoRank.StatedLieTag.POmegaOdd ≠ .G2 := by decide
  have hD4 : Assembly.LowTwoRank.StatedLieTag.POmegaOdd ≠ .trialityD4 := by decide
  have he := ih8Model_exp_eq_one M hD4
  subst he
  rw [piSign_three_one, show muKind false .POmegaOdd 3 = .s4 by simp [muKind]]
  have hMatch : ∀ A ∈ M.cls, ∀ B ∈ M.cls, ∀ S ∈ M.cls, A ≠ B → A ≠ S → B ≠ S → Commutes A B →
      Commutes A S → False := fun A hA B hB S hS hAB hAS hBS cAB cAS =>
    hBS (Q3W.modelLayerEq_pOmegaOdd3 A (M.cls_sub hA) B (M.cls_sub hB) S (M.cls_sub hS) cAB cAS)
  obtain ⟨R₁, hR₁m, R₂, hR₂m, W, hW⟩ := Q3W.exists_unitaryPair_odd3
  have hR₁ := M.fund_subset_cls hne hG2 hD4 hR₁m
  have hR₂ := M.fund_subset_cls hne hG2 hD4 hR₂m
  obtain ⟨-, hnc⟩ := unitary_ne_nc3 M hG2 hD4 hR₁ hR₂ hW
  have hadj := dstarAdj_unitary3 M hΩ hG2 hD4 hR₁ hR₂ hW
  exact ⟨matching3 M hΩ hG2 hD4 hMatch,
    edge_of_commuting3 M hΩ hne hG2 hD4 (exists_commuting_small_b3 M.admissible),
    _, M.map_mem hR₁, dComp_ne3 M hΩ hG2 hD4 hMatch hR₁ hR₂ hnc hadj⟩

theorem shape_pOmegaMinus4 (hT : Q3T8.Asc77.TransSection Φ) (hne : Φ.Nonempty)
    (hL : HasLieType 3 1 Φ .POmegaMinus 4) :
    KindShape Φ (muKind (piSign 3 1) .POmegaMinus 4) := by
  have hΩ : HypOmegaModU (.sl2 3 1) Φ := hT.hyp
  obtain ⟨e, ⟨M⟩⟩ := Ih8Model.exists_datum_of_hasLieType hT.hyp hT.gen hL
  have hG2 : Assembly.LowTwoRank.StatedLieTag.POmegaMinus ≠ .G2 := by decide
  have hD4 : Assembly.LowTwoRank.StatedLieTag.POmegaMinus ≠ .trialityD4 := by decide
  have he := ih8Model_exp_eq_one M hD4
  subst he
  rw [piSign_three_one, show muKind false .POmegaMinus 4 = .s4 by simp [muKind]]
  have hMatch : ∀ A ∈ M.cls, ∀ B ∈ M.cls, ∀ S ∈ M.cls, A ≠ B → A ≠ S → B ≠ S → Commutes A B →
      Commutes A S → False := fun A hA B hB S hS hAB hAS hBS cAB cAS =>
    hBS (Q3W.modelLayerEq_pOmegaMinus3 A (M.cls_sub hA) B (M.cls_sub hB) S (M.cls_sub hS) cAB cAS)
  obtain ⟨R₁, hR₁m, R₂, hR₂m, W, hW⟩ := Q3W.exists_unitaryPair_minus3
  have hR₁ := M.fund_subset_cls hne hG2 hD4 hR₁m
  have hR₂ := M.fund_subset_cls hne hG2 hD4 hR₂m
  obtain ⟨-, hnc⟩ := unitary_ne_nc3 M hG2 hD4 hR₁ hR₂ hW
  have hadj := dstarAdj_unitary3 M hΩ hG2 hD4 hR₁ hR₂ hW
  exact ⟨matching3 M hΩ hG2 hD4 hMatch,
    edge_of_commuting3 M hΩ hne hG2 hD4 (exists_commuting_small_dminus4 M.admissible),
    _, M.map_mem hR₁, dComp_ne3 M hΩ hG2 hD4 hMatch hR₁ hR₂ hnc hadj⟩

theorem shape_pOmegaPlus4 (hT : Q3T8.Asc77.TransSection Φ) (hne : Φ.Nonempty)
    (hL : HasLieType 3 1 Φ .POmegaPlus 4) :
    KindShape Φ (muKind (piSign 3 1) .POmegaPlus 4) := by
  have hΩ : HypOmegaModU (.sl2 3 1) Φ := hT.hyp
  obtain ⟨e, ⟨M⟩⟩ := Ih8Model.exists_datum_of_hasLieType hT.hyp hT.gen hL
  have hG2 : Assembly.LowTwoRank.StatedLieTag.POmegaPlus ≠ .G2 := by decide
  have hD4 : Assembly.LowTwoRank.StatedLieTag.POmegaPlus ≠ .trialityD4 := by decide
  have he := ih8Model_exp_eq_one M hD4
  subst he
  rw [piSign_three_one, show muKind false .POmegaPlus 4 = .wyl by simp [muKind]]
  have hClose : ∀ A ∈ M.cls, ∀ B ∈ M.cls, ∀ C ∈ M.cls, A ≠ B → A ≠ C → B ≠ C → Commutes A B →
      Commutes A C → Commutes B C := fun A hA B hB C hC =>
    commutes_nbrs_plus3 (M.cls_sub hA) (M.cls_sub hB) (M.cls_sub hC)
  refine ⟨?_, ?_, ?_⟩
  · intro K hK
    obtain ⟨R, hR, rfl⟩ := (M.mem_iff K).mp hK
    obtain ⟨R₂, -, R₃, -, R₄, -, -, -, -, -, -, -, -, -, -, -, -, -, hall⟩ :=
      clique_plus3 (M.cls_sub hR)
    have hsub : omegaNbr Φ (R.map M.ψ) ⊆ {R₂.map M.ψ, R₃.map M.ψ, R₄.map M.ψ} := by
      intro J hJ
      obtain ⟨S, hS, rfl⟩ := (M.mem_iff J).mp hJ.1
      obtain ⟨hRS, cRS⟩ := (omegaNbr_iff3 M hΩ hG2 hD4 hR hS).mp hJ
      rcases hall S (M.cls_sub hS) (Ne.symm hRS) cRS with rfl | rfl | rfl <;> simp
    refine (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ?_
    calc ({R₂.map M.ψ, R₃.map M.ψ, R₄.map M.ψ} : Set (Subgroup X)).ncard
        ≤ ({R₃.map M.ψ, R₄.map M.ψ} : Set (Subgroup X)).ncard + 1 := Set.ncard_insert_le _ _
      _ ≤ (({R₄.map M.ψ} : Set (Subgroup X)).ncard + 1) + 1 := by
        gcongr
        exact Set.ncard_insert_le _ _
      _ = 3 := by rw [Set.ncard_singleton]
  · obtain ⟨K₀, hK₀⟩ := hne
    obtain ⟨R, hR, -⟩ := (M.mem_iff K₀).mp hK₀
    obtain ⟨R₂, h₂, R₃, h₃, R₄, h₄, n12, n13, n14, n23, n24, n34, c12, c13, c14, c23, c24,
      c34, -⟩ := clique_plus3 (M.cls_sub hR)
    have m₂ := M.fund_subset_cls ⟨K₀, hK₀⟩ hG2 hD4 h₂
    have m₃ := M.fund_subset_cls ⟨K₀, hK₀⟩ hG2 hD4 h₃
    have m₄ := M.fund_subset_cls ⟨K₀, hK₀⟩ hG2 hD4 h₄
    let Rk : Fin 4 → Subgroup (modelUniv .POmegaPlus 4 3 1 Fact.out).K := ![R, R₂, R₃, R₄]
    have hRk : ∀ i, Rk i ∈ M.cls := by
      intro i
      fin_cases i <;> assumption
    have hneq : ∀ i j : Fin 4, i ≠ j → Rk i ≠ Rk j := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp [Rk] at hij ⊢ <;> first | assumption | exact Ne.symm ‹_›
    have hcom : ∀ i j : Fin 4, i ≠ j → Commutes (Rk i) (Rk j) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp [Rk] at hij ⊢ <;>
        first | assumption | exact Commutes.symm ‹_›
    refine ⟨fun i => (Rk i).map M.ψ, fun i => M.map_mem (hRk i), fun i j h => ?_,
      fun i j hij => ih8_commutes_map M.ψ (hcom i j hij)⟩
    by_contra hij
    exact hneq i j hij (map_inj3 M hG2 hD4 (hRk i) (hRk j) h)
  · obtain ⟨R₁, hR₁m, R₂, hR₂m, W, hW⟩ := Q3W.exists_unitaryPair_plus3
    have hR₁ := M.fund_subset_cls hne hG2 hD4 hR₁m
    have hR₂ := M.fund_subset_cls hne hG2 hD4 hR₂m
    obtain ⟨-, hnc⟩ := unitary_ne_nc3 M hG2 hD4 hR₁ hR₂ hW
    have hadj := dstarAdj_unitary3 M hΩ hG2 hD4 hR₁ hR₂ hW
    exact ⟨R₁.map M.ψ, M.map_mem hR₁, dComp_ne_closed3 M hΩ hG2 hD4 hClose hR₁ hR₂ hnc hadj⟩

theorem kindShape_of_shapes (hT : Q3T8.Asc77.TransSection Φ) (hne : Φ.Nonempty)
    {t : StatedLieTag} {k : ℕ} (hL : HasLieType 3 1 Φ t k)
    (hsix : (t = .PSp ∧ k = 2) ∨ (t = .PSL ∧ k = 4) ∨ (t = .PSU ∧ k = 4) ∨
      (t = .POmegaOdd ∧ k = 3) ∨ (t = .POmegaPlus ∧ k = 4) ∨ (t = .POmegaMinus ∧ k = 4)) :
    KindShape Φ (muKind (piSign 3 1) t k) := by
  rcases hsix with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact shape_psp2 hT hne hL
  · exact shape_psl4 hT hne hL
  · exact shape_psu4 hT hne hL
  · exact shape_pOmegaOdd3 hT hne hL
  · exact shape_pOmegaPlus4 hT hne hL
  · exact shape_pOmegaMinus4 hT hne hL

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.MuTab
