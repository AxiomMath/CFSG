module

public import CFSG.ClassicalInvolution.Asc77.AscMuTabSmallB
public import CFSG.ClassicalInvolution.Asc77.AscIHSectD
public import CFSG.ClassicalInvolution.RouteD.ExoticD4Model
public import CFSG.ClassicalInvolution.RouteD.ExoticSingleClique
public import CFSG.ClassicalInvolution.Balance.BootNoTripleStrong
public import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceGlue
public import CFSG.ClassicalInvolution.RouteD.G2D4Ih8
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Outer

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
open CFSG.ClassicalInvolution.RouteD.Gaps (commutes_symm)

namespace MuTab

section Model

variable {p : ℕ} [Fact p.Prime]

theorem clique_plus (hp2 : p ≠ 2) {e : ℕ} (hq : 5 ≤ p ^ e)
    (hadm : StatedLieAdmissible .POmegaPlus 4 p e)
    {R : Subgroup (modelUniv .POmegaPlus 4 p e Fact.out).K} (hR : R ∈ ModelFund p .POmegaPlus 4 e) :
    ∃ R₂ ∈ ModelFund p .POmegaPlus 4 e, ∃ R₃ ∈ ModelFund p .POmegaPlus 4 e,
      ∃ R₄ ∈ ModelFund p .POmegaPlus 4 e, R ≠ R₂ ∧ R ≠ R₃ ∧ R ≠ R₄ ∧ R₂ ≠ R₃ ∧ R₂ ≠ R₄ ∧
        R₃ ≠ R₄ ∧ Commutes R R₂ ∧ Commutes R R₃ ∧ Commutes R R₄ ∧ Commutes R₂ R₃ ∧
        Commutes R₂ R₄ ∧ Commutes R₃ R₄ ∧
        ∀ S ∈ ModelFund p .POmegaPlus 4 e, S ≠ R → Commutes R S → S = R₂ ∨ S = R₃ ∨ S = R₄ := by
  have hCF := cliqueFour_fund_plus_four hp2 hq hadm
  obtain ⟨R₂, h₂, R₃, h₃, R₄, h₄, n12, n13, n14, n23, n24, n34, c12, c13, c14, c23, c24, c34⟩ :=
    (plusFourCliqueFacts hp2 hq).clique R hR
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

theorem commutes_nbrs_plus (hp2 : p ≠ 2) {e : ℕ} (hq : 5 ≤ p ^ e)
    (hadm : StatedLieAdmissible .POmegaPlus 4 p e)
    {A B C : Subgroup (modelUniv .POmegaPlus 4 p e Fact.out).K}
    (hA : A ∈ ModelFund p .POmegaPlus 4 e) (hB : B ∈ ModelFund p .POmegaPlus 4 e)
    (hC : C ∈ ModelFund p .POmegaPlus 4 e) (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (cAB : Commutes A B) (cAC : Commutes A C) : Commutes B C := by
  obtain ⟨R₂, -, R₃, -, R₄, -, -, -, -, n23, n24, n34, -, -, -, c23, c24, c34, hall⟩ :=
    clique_plus hp2 hq hadm hA
  rcases hall B hB (Ne.symm hAB) cAB with rfl | rfl | rfl <;>
    rcases hall C hC (Ne.symm hAC) cAC with rfl | rfl | rfl
  all_goals first
    | exact absurd rfl hBC
    | assumption
    | exact commutes_symm ‹_›

end Model

end MuTab

namespace Ih8Model

section Datum

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {t : StatedLieTag} {k e : ℕ} (M : Ih8Model p f Ω t k e)

include M

theorem muTab_dComp_ne_of_closed (hΩ : HypOmegaMod p f Ω) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    (hClose : ∀ A ∈ M.cls, ∀ B ∈ M.cls, ∀ C ∈ M.cls, A ≠ B → A ≠ C → B ≠ C → Commutes A B →
      Commutes A C → Commutes B C)
    {R₀ S₀ : Subgroup (modelUniv t k p e Fact.out).K} (hR₀ : R₀ ∈ M.cls) (hS₀ : S₀ ∈ M.cls)
    (hRS : R₀ ≠ S₀) (hnc : ¬ Commutes R₀ S₀)
    (hstar : S₀.map M.ψ ∈ dstarComp Ω (R₀.map M.ψ)) :
    dComp Ω (R₀.map M.ψ) ≠ dstarComp Ω (R₀.map M.ψ) := by
  intro heq
  have h1 : S₀.map M.ψ ∈ dComp Ω (R₀.map M.ψ) := by
    rw [heq]
    exact hstar
  have key : ∀ J, Relation.ReflTransGen (fun X Y : Subgroup G => Y ∈ Ω ∧ dAdj Ω X Y)
      (R₀.map M.ψ) J → J = R₀.map M.ψ ∨ ∃ T ∈ M.cls, T ≠ R₀ ∧ Commutes R₀ T ∧ J = T.map M.ψ := by
    intro J hJ
    induction hJ with
    | refl => exact Or.inl rfl
    | @tail b c _ hbc ih =>
      obtain ⟨B', hB', rfl⟩ := (M.mem_iff c).mp hbc.1
      rcases ih with rfl | ⟨T, hT, hTR, hRT, rfl⟩
      · obtain ⟨hne', hc'⟩ := (M.muTab_dAdj_iff hΩ hp2 hq hG2 hD4 hR₀ hB').mp hbc.2
        exact Or.inr ⟨B', hB', hne'.symm, hc', rfl⟩
      · obtain ⟨hTB, hcTB⟩ := (M.muTab_dAdj_iff hΩ hp2 hq hG2 hD4 hT hB').mp hbc.2
        by_cases hBR : B' = R₀
        · exact Or.inl (by rw [hBR])
        · exact Or.inr ⟨B', hB', hBR, hClose T hT R₀ hR₀ B' hB' hTR hTB (Ne.symm hBR)
            (commutes_symm hRT) hcTB, rfl⟩
  rcases key _ h1 with h | ⟨T, hT, hTR, hRT, hS⟩
  · exact hRS (M.muTab_map_inj hp2 hq hD4 hS₀ hR₀ h).symm
  · have := M.muTab_map_inj hp2 hq hD4 hS₀ hT hS
    exact hnc (this ▸ hRT)

end Datum

end Ih8Model

section Pair

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)} {e : ℕ}

theorem Ih8Model.muTab_linearPair_pOmegaPlus (M : Ih8Model p f Ω .POmegaPlus 4 e)
    (hne : Ω.Nonempty) :
    ∃ R₁ ∈ M.cls, ∃ R₂ ∈ M.cls, ∃ W, WeakCT.LinearBlockStandardPair (GaloisField p e) W R₁ R₂ := by
  let i₀ : Fin (modelUniv .POmegaPlus 4 p e Fact.out).D.rank := ⟨0, by show 0 < 4; omega⟩
  have hγ : ModelFacts.IsLongestRoot (modelUniv .POmegaPlus 4 p e Fact.out).D (Pi.single i₀ 1) :=
    ModelFacts.isLongestRoot_single .POmegaPlus 4 p e Fact.out trivial M.admissible i₀ trivial
  obtain ⟨δ, hδ, -, hW⟩ := ModelFacts.exists_standardPair_partner_POmegaPlus p e 4 M.admissible hγ
  exact M.muTab_pair_of_partner hne (by decide) (by decide) hγ ⟨δ, hδ, hW⟩

end Pair

namespace MuTab

section Wyl

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {e : ℕ}

theorem shapeWyl_pOmegaPlus4 (M : Ih8Model p f Ω .POmegaPlus 4 e) (hΩ : HypOmegaMod p f Ω)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hne : Ω.Nonempty) (hstar : T3.DStarConnected Ω) :
    ShapeWyl Ω := by
  have hG2 : StatedLieTag.POmegaPlus ≠ .G2 := by decide
  have hD4 : StatedLieTag.POmegaPlus ≠ .trialityD4 := by decide
  have hq' : 5 ≤ p ^ e := (M.exp_eq_f hD4) ▸ hq
  have hClose : ∀ A ∈ M.cls, ∀ B ∈ M.cls, ∀ C ∈ M.cls, A ≠ B → A ≠ C → B ≠ C → Commutes A B →
      Commutes A C → Commutes B C := fun A hA B hB C hC =>
    commutes_nbrs_plus hp2 hq' M.admissible (M.cls_sub hA) (M.cls_sub hB) (M.cls_sub hC)
  refine ⟨?_, ?_, ?_⟩
  · intro K hK
    obtain ⟨R, hR, rfl⟩ := (M.mem_iff K).mp hK
    obtain ⟨R₂, -, R₃, -, R₄, -, -, -, -, -, -, -, -, -, -, -, -, -, hall⟩ :=
      clique_plus hp2 hq' M.admissible (M.cls_sub hR)
    have hsub : omegaNbr Ω (R.map M.ψ) ⊆ {R₂.map M.ψ, R₃.map M.ψ, R₄.map M.ψ} := by
      intro J hJ
      obtain ⟨S, hS, rfl⟩ := (M.mem_iff J).mp hJ.1
      obtain ⟨hRS, cRS⟩ := (M.muTab_omegaNbr_iff hΩ hp2 hq hG2 hD4 hR hS).mp hJ
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
      c34, -⟩ := clique_plus hp2 hq' M.admissible (M.cls_sub hR)
    have m₂ := M.fund_subset_cls ⟨K₀, hK₀⟩ hG2 hD4 h₂
    have m₃ := M.fund_subset_cls ⟨K₀, hK₀⟩ hG2 hD4 h₃
    have m₄ := M.fund_subset_cls ⟨K₀, hK₀⟩ hG2 hD4 h₄
    let Rk : Fin 4 → Subgroup (modelUniv .POmegaPlus 4 p e Fact.out).K := ![R, R₂, R₃, R₄]
    have hRk : ∀ i, Rk i ∈ M.cls := by
      intro i
      fin_cases i <;> assumption
    have hneq : ∀ i j : Fin 4, i ≠ j → Rk i ≠ Rk j := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp [Rk] at hij ⊢ <;> first | assumption | exact Ne.symm ‹_›
    have hcom : ∀ i j : Fin 4, i ≠ j → Commutes (Rk i) (Rk j) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp [Rk] at hij ⊢ <;>
        first | assumption | exact commutes_symm ‹_›
    refine ⟨fun i => (Rk i).map M.ψ, fun i => M.map_mem (hRk i), fun i j h => ?_,
      fun i j hij => ih8_commutes_map M.ψ (hcom i j hij)⟩
    by_contra hij
    exact hneq i j hij (M.muTab_map_inj hp2 hq (by decide) (hRk i) (hRk j) h)
  · obtain ⟨R₁, hR₁, R₂, hR₂, W, hW⟩ := M.muTab_linearPair_pOmegaPlus hne
    obtain ⟨hRS, hnc⟩ := M.muTab_linear_ne_nc hp2 hq hD4 hR₁ hR₂ hW
    exact ⟨R₁.map M.ψ, M.map_mem hR₁, M.muTab_dComp_ne_of_closed hΩ hp2 hq hG2 hD4 hClose hR₁ hR₂
      hRS hnc (hstar _ (M.map_mem hR₁) _ (M.map_mem hR₂))⟩

theorem muKind_pOmegaPlus_four (π : Bool) : muKind π .POmegaPlus 4 = .wyl := by
  cases π <;> simp [muKind]

theorem smallShape_pOmegaPlus4_of (hstar : Ih8D4Star p f) : SmallShape p f .POmegaPlus 4 := by
  intro hp2 hq X _ _ Φ hS hne _ hL
  obtain ⟨e, ⟨M⟩⟩ := exists_datum_of_hasLieType hS hL
  have hΩ := hS.hyp
  rw [muKind_pOmegaPlus_four]
  exact shapeWyl_pOmegaPlus4 M hΩ hp2 hq hne (hstar hp2 hq X Φ e hΩ ⟨M⟩)

end Wyl

end MuTab

end CFSG.ClassicalInvolution.Asc77
