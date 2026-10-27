module

public import CFSG.ClassicalInvolution.Q3.Q3MTKind
public import CFSG.ClassicalInvolution.Q3.Q3MTModel5
public import CFSG.ClassicalInvolution.Q3.Q3MTOrth
public import CFSG.ClassicalInvolution.Q3.Q3EXOrthLarge
public import CFSG.ClassicalInvolution.Uniform.U3Edge
public import CFSG.ClassicalInvolution.Q3.Q3CPOmega
public import CFSG.ClassicalInvolution.Q3.Q3CPSix67
public import CFSG.ClassicalInvolution.Q3.Q3MTDatum
public import CFSG.ClassicalInvolution.Q3.Q3ZFraStd
public import CFSG.Sporadic.J4.QT2LocProof
public import CFSG.Sporadic.J4.QTOutChar

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3MT

open CFSG.Open hiding StatedLieTag
open CFSG.Assembly CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.MuTab
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Q3.Q3W
open scoped MatrixGroups


theorem smallShape3_pOmegaOdd3 : SmallShape3 .POmegaOdd 3 := by
  intro G _ _ _ Ω hΩ hA hne htrans hL
  obtain ⟨e, ⟨M⟩⟩ := exists_datum_of_hasLieTypeU hΩ hne hL
  have hG2 : LowTwoRank.StatedLieTag.POmegaOdd ≠ .G2 := by decide
  have hD4 : LowTwoRank.StatedLieTag.POmegaOdd ≠ .trialityD4 := by decide
  have he := ih8Model_exp_eq_one M hD4
  subst he
  rw [show muKind false .POmegaOdd 3 = .s4 by simp [muKind]]
  have hMatch : ∀ A ∈ M.cls, ∀ B ∈ M.cls, ∀ S ∈ M.cls, A ≠ B → A ≠ S → B ≠ S → Commutes A B →
      Commutes A S → False := fun A hA B hB S hS hAB hAS hBS cAB cAS =>
    hBS (modelLayerEq_pOmegaOdd3 A (M.cls_sub hA) B (M.cls_sub hB) S (M.cls_sub hS) cAB cAS)
  obtain ⟨R₁, hR₁m, R₂, hR₂m, W, hW⟩ := exists_unitaryPair_odd3
  have hR₁ := M.fund_subset_cls hne hG2 hD4 hR₁m
  have hR₂ := M.fund_subset_cls hne hG2 hD4 hR₂m
  obtain ⟨-, hnc⟩ := unitary_ne_nc3 M hG2 hD4 hR₁ hR₂ hW
  have hadj := dstarAdj_unitary3 M hΩ hG2 hD4 hR₁ hR₂ hW
  exact ⟨matching3 M hΩ hG2 hD4 hMatch,
    edge_of_commuting3 M hΩ hne hG2 hD4 (exists_commuting_small_b3 M.admissible),
    _, M.map_mem hR₁, dComp_ne3 M hΩ hG2 hD4 hMatch hR₁ hR₂ hnc hadj⟩

theorem smallShape3_pOmegaMinus4 : SmallShape3 .POmegaMinus 4 := by
  intro G _ _ _ Ω hΩ hA hne htrans hL
  obtain ⟨e, ⟨M⟩⟩ := exists_datum_of_hasLieTypeU hΩ hne hL
  have hG2 : LowTwoRank.StatedLieTag.POmegaMinus ≠ .G2 := by decide
  have hD4 : LowTwoRank.StatedLieTag.POmegaMinus ≠ .trialityD4 := by decide
  have he := ih8Model_exp_eq_one M hD4
  subst he
  rw [show muKind false .POmegaMinus 4 = .s4 by simp [muKind]]
  have hMatch : ∀ A ∈ M.cls, ∀ B ∈ M.cls, ∀ S ∈ M.cls, A ≠ B → A ≠ S → B ≠ S → Commutes A B →
      Commutes A S → False := fun A hA B hB S hS hAB hAS hBS cAB cAS =>
    hBS (modelLayerEq_pOmegaMinus3 A (M.cls_sub hA) B (M.cls_sub hB) S (M.cls_sub hS) cAB cAS)
  obtain ⟨R₁, hR₁m, R₂, hR₂m, W, hW⟩ := exists_unitaryPair_minus3
  have hR₁ := M.fund_subset_cls hne hG2 hD4 hR₁m
  have hR₂ := M.fund_subset_cls hne hG2 hD4 hR₂m
  obtain ⟨-, hnc⟩ := unitary_ne_nc3 M hG2 hD4 hR₁ hR₂ hW
  have hadj := dstarAdj_unitary3 M hΩ hG2 hD4 hR₁ hR₂ hW
  exact ⟨matching3 M hΩ hG2 hD4 hMatch,
    edge_of_commuting3 M hΩ hne hG2 hD4 (exists_commuting_small_dminus4 M.admissible),
    _, M.map_mem hR₁, dComp_ne3 M hΩ hG2 hD4 hMatch hR₁ hR₂ hnc hadj⟩

section Plus

theorem clique_plus3 {R : Subgroup (modelUniv .POmegaPlus 4 3 1 Fact.out).K}
    (hR : R ∈ ModelFund 3 .POmegaPlus 4 1) :
    ∃ R₂ ∈ ModelFund 3 .POmegaPlus 4 1, ∃ R₃ ∈ ModelFund 3 .POmegaPlus 4 1,
      ∃ R₄ ∈ ModelFund 3 .POmegaPlus 4 1, R ≠ R₂ ∧ R ≠ R₃ ∧ R ≠ R₄ ∧ R₂ ≠ R₃ ∧ R₂ ≠ R₄ ∧
        R₃ ≠ R₄ ∧ Commutes R R₂ ∧ Commutes R R₃ ∧ Commutes R R₄ ∧ Commutes R₂ R₃ ∧
        Commutes R₂ R₄ ∧ Commutes R₃ R₄ ∧
        ∀ S ∈ ModelFund 3 .POmegaPlus 4 1, S ≠ R → Commutes R S →
          S = R₂ ∨ S = R₃ ∨ S = R₄ := by
  have hadm : StatedLieAdmissible .POmegaPlus 4 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl⟩
  have hCF := Q3W.EX.cliqueFour_fund_plus_four3 hadm
  obtain ⟨R₂, h₂, R₃, h₃, R₄, h₄, n12, n13, n14, n23, n24, n34, c12, c13, c14, c23, c24, c34⟩ :=
    Q3W.plusFourCliqueFacts3.clique R hR
  obtain ⟨F₄, -, -, -, -, -, -, hall⟩ := hCF ⟨R, hR⟩ ⟨R₂, h₂⟩ ⟨R₃, h₃⟩
    (fun h => n12 (congrArg Subtype.val h)) (fun h => n13 (congrArg Subtype.val h))
    (fun h => n23 (congrArg Subtype.val h)) c12 c13 c23
  have h4eq : R₄ = F₄.1 := by
    rcases hall ⟨R₄, h₄⟩ c14 with h | h | h
    · exact absurd (congrArg Subtype.val h).symm n24
    · exact absurd (congrArg Subtype.val h).symm n34
    · exact congrArg Subtype.val h
  refine ⟨R₂, h₂, R₃, h₃, R₄, h₄, n12, n13, n14, n23, n24, n34, c12, c13, c14, c23, c24, c34, ?_⟩
  intro S hS _ hc
  rcases hall ⟨S, hS⟩ hc with h | h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (Or.inl (congrArg Subtype.val h))
  · exact Or.inr (Or.inr ((congrArg Subtype.val h).trans h4eq.symm))

theorem commutes_nbrs_plus3 {A B C : Subgroup (modelUniv .POmegaPlus 4 3 1 Fact.out).K}
    (hA : A ∈ ModelFund 3 .POmegaPlus 4 1) (hB : B ∈ ModelFund 3 .POmegaPlus 4 1)
    (hC : C ∈ ModelFund 3 .POmegaPlus 4 1) (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (cAB : Commutes A B) (cAC : Commutes A C) : Commutes B C := by
  obtain ⟨R₂, -, R₃, -, R₄, -, -, -, -, n23, n24, n34, -, -, -, c23, c24, c34, hall⟩ :=
    clique_plus3 hA
  rcases hall B hB (Ne.symm hAB) cAB with rfl | rfl | rfl <;>
    rcases hall C hC (Ne.symm hAC) cAC with rfl | rfl | rfl
  all_goals first
    | exact absurd rfl hBC
    | assumption
    | exact Commutes.symm ‹_›

section Dcomp

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {t : LowTwoRank.StatedLieTag}
  {k e : ℕ}

theorem dComp_ne_closed3 (M : Ih8Model 3 1 Ω t k e) (hΩ : HypOmegaModU (.sl2 3 1) Ω)
    (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    (hClose : ∀ A ∈ M.cls, ∀ B ∈ M.cls, ∀ C ∈ M.cls, A ≠ B → A ≠ C → B ≠ C → Commutes A B →
      Commutes A C → Commutes B C)
    {R₀ S₀ : Subgroup (modelUniv t k 3 e Fact.out).K} (hR₀ : R₀ ∈ M.cls) (hS₀ : S₀ ∈ M.cls)
    (hnc : ¬ Commutes R₀ S₀) (hstar : dstarAdj Ω (R₀.map M.ψ) (S₀.map M.ψ)) :
    dComp Ω (R₀.map M.ψ) ≠ dstarComp Ω (R₀.map M.ψ) := by
  have hne : R₀.map M.ψ ≠ S₀.map M.ψ := by
    rcases hstar.2 with h | h
    · exact h.2.1.symm
    · exact h.2.1
  intro heq
  have h1 : S₀.map M.ψ ∈ dComp Ω (R₀.map M.ψ) := by
    rw [heq]
    exact Relation.ReflTransGen.single hstar
  have key : ∀ J, Relation.ReflTransGen
      (fun X Y : Subgroup G => Y ∈ Ω ∧ Disconnected.dAdj Ω X Y) (R₀.map M.ψ) J →
      J = R₀.map M.ψ ∨ ∃ T ∈ M.cls, T ≠ R₀ ∧ Commutes R₀ T ∧ J = T.map M.ψ := by
    intro J hJ
    induction hJ with
    | refl => exact Or.inl rfl
    | @tail b c _ hbc ih =>
      obtain ⟨B', hB', rfl⟩ := (M.mem_iff c).mp hbc.1
      rcases ih with rfl | ⟨T, hT, hTR, hRT, rfl⟩
      · obtain ⟨hne', hc'⟩ := (dAdj_iff3 M hΩ hG2 hD4 hR₀ hB').mp hbc.2
        exact Or.inr ⟨B', hB', hne'.symm, hc', rfl⟩
      · obtain ⟨hTB, hcTB⟩ := (dAdj_iff3 M hΩ hG2 hD4 hT hB').mp hbc.2
        by_cases hBR : B' = R₀
        · exact Or.inl (by rw [hBR])
        · exact Or.inr ⟨B', hB', hBR, hClose T hT R₀ hR₀ B' hB' hTR hTB (Ne.symm hBR)
            hRT.symm hcTB, rfl⟩
  rcases key _ h1 with h | ⟨T, hT, hTR, hRT, hS⟩
  · exact hne h.symm
  · have := map_inj3 M hG2 hD4 hS₀ hT hS
    exact hnc (this ▸ hRT)

end Dcomp

theorem smallShape3_pOmegaPlus4 : SmallShape3 .POmegaPlus 4 := by
  intro G _ _ _ Ω hΩ hA hne htrans hL
  obtain ⟨e, ⟨M⟩⟩ := exists_datum_of_hasLieTypeU hΩ hne hL
  have hG2 : LowTwoRank.StatedLieTag.POmegaPlus ≠ .G2 := by decide
  have hD4 : LowTwoRank.StatedLieTag.POmegaPlus ≠ .trialityD4 := by decide
  have he := ih8Model_exp_eq_one M hD4
  subst he
  rw [show muKind false .POmegaPlus 4 = .wyl by simp [muKind]]
  have hClose : ∀ A ∈ M.cls, ∀ B ∈ M.cls, ∀ C ∈ M.cls, A ≠ B → A ≠ C → B ≠ C → Commutes A B →
      Commutes A C → Commutes B C := fun A hA B hB C hC =>
    commutes_nbrs_plus3 (M.cls_sub hA) (M.cls_sub hB) (M.cls_sub hC)
  refine ⟨?_, ?_, ?_⟩
  · intro K hK
    obtain ⟨R, hR, rfl⟩ := (M.mem_iff K).mp hK
    obtain ⟨R₂, -, R₃, -, R₄, -, -, -, -, -, -, -, -, -, -, -, -, -, hall⟩ :=
      clique_plus3 (M.cls_sub hR)
    have hsub : omegaNbr Ω (R.map M.ψ) ⊆ {R₂.map M.ψ, R₃.map M.ψ, R₄.map M.ψ} := by
      intro J hJ
      obtain ⟨S, hS, rfl⟩ := (M.mem_iff J).mp hJ.1
      obtain ⟨hRS, cRS⟩ := (omegaNbr_iff3 M hΩ hG2 hD4 hR hS).mp hJ
      rcases hall S (M.cls_sub hS) (Ne.symm hRS) cRS with rfl | rfl | rfl <;> simp
    refine (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ?_
    calc ({R₂.map M.ψ, R₃.map M.ψ, R₄.map M.ψ} : Set (Subgroup G)).ncard
        ≤ ({R₃.map M.ψ, R₄.map M.ψ} : Set (Subgroup G)).ncard + 1 := Set.ncard_insert_le _ _
      _ ≤ (({R₄.map M.ψ} : Set (Subgroup G)).ncard + 1) + 1 := by
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
  · obtain ⟨R₁, hR₁m, R₂, hR₂m, W, hW⟩ := exists_unitaryPair_plus3
    have hR₁ := M.fund_subset_cls hne hG2 hD4 hR₁m
    have hR₂ := M.fund_subset_cls hne hG2 hD4 hR₂m
    obtain ⟨-, hnc⟩ := unitary_ne_nc3 M hG2 hD4 hR₁ hR₂ hW
    have hadj := dstarAdj_unitary3 M hΩ hG2 hD4 hR₁ hR₂ hW
    exact ⟨R₁.map M.ψ, M.map_mem hR₁, dComp_ne_closed3 M hΩ hG2 hD4 hClose hR₁ hR₂ hnc hadj⟩

end Plus

end CFSG.ClassicalInvolution.Q3.Q3MT
