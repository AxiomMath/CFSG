module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitGeneral

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

@[expose] def FooteHyp (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G) : Prop :=
  Assembly.KProper Blueprint.Catalog G ∧ FooteCoreHypothesis G ∧ IsTwoComponentAt t L ∧
    FootePointedMaximal t L ∧ FooteFamilyType L ∧ 2 ≤ CFSG.pRank 2 ↥L

@[expose] def FooteCounterexample (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G) :
    Prop :=
  FooteHyp G t L ∧ ¬ FooteConclusion t L (conjClosure L (pLayer G 2))

@[expose] def FooteMinimal (G : Type) [Group G] [Finite G] : Prop :=
  (∃ (t : G) (L : Subgroup G), FooteCounterexample G t L) ∧
    ∀ (G' : Type) [Group G'] [Finite G'], Nat.card G' < Nat.card G →
      ∀ (t' : G') (L' : Subgroup G'), ¬ FooteCounterexample G' t' L'

@[expose] def footeFamilyOf {G : Type} [Group G] (L : Subgroup G) : Set (Subgroup G) :=
  {A | (∃ z : G, FootePointedMaximal z A) ∧
    Nonempty (A ⧸ Open.fusionZStar A ≃* L ⧸ Open.fusionZStar L)}

@[expose] def FooteInitialReductions : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), FooteMinimal G →
    FooteCounterexample G t L →
    IsSimpleGroup G ∧ (∀ A ∈ footeFamilyOf L, CFSG.pRank 2 ↥A = 2) ∧
      ∃ A ∈ footeFamilyOf L, 2 ≤ CFSG.pRank 2 ↥(coreActionKernel A)

@[expose] def FooteRankBound : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), FooteMinimal G →
    FooteCounterexample G t L → IsSimpleGroup G →
    (∀ A ∈ footeFamilyOf L, CFSG.pRank 2 ↥A = 2) →
    ∀ A ∈ footeFamilyOf L, CFSG.pRank 2 ↥(coreActionKernel A) ≤ 2

@[expose] def FooteRankTwoExclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), FooteMinimal G →
    FooteCounterexample G t L → IsSimpleGroup G →
    (∀ A ∈ footeFamilyOf L, CFSG.pRank 2 ↥A = 2) →
    (∃ A ∈ footeFamilyOf L, 2 ≤ CFSG.pRank 2 ↥(coreActionKernel A)) →
    (∀ A ∈ footeFamilyOf L, CFSG.pRank 2 ↥(coreActionKernel A) ≤ 2) → False

theorem exists_footeMinimal_of_counterexample {G : Type} [Group G] [Finite G] {t : G}
    {L : Subgroup G} (h : FooteCounterexample G t L) :
    ∃ (G₀ : Type) (_ : Group G₀) (_ : Finite G₀), FooteMinimal G₀ := by
  classical
  let p : ℕ → Prop := fun n => ∃ (G' : Type) (_ : Group G') (_ : Finite G') (t' : G')
    (L' : Subgroup G'), Nat.card G' = n ∧ FooteCounterexample G' t' L'
  have hp : ∃ n, p n := ⟨Nat.card G, G, inferInstance, inferInstance, t, L, rfl, h⟩
  obtain ⟨G₀, hG₀, hfin, t₀, L₀, hcard, hce⟩ := Nat.find_spec hp
  refine ⟨G₀, hG₀, hfin, ⟨t₀, L₀, hce⟩, fun G' _ _ hlt t' L' hce' => ?_⟩
  exact Nat.find_min hp (hcard ▸ hlt) ⟨G', inferInstance, inferInstance, t', L', rfl, hce'⟩

theorem footeGeneralStatement_of_steps (h31 : FooteInitialReductions) (h4 : FooteRankBound)
    (h5 : FooteRankTwoExclusion) : FooteGeneralStatement := by
  intro G _ _ hKp hcore t L htL hmax htype hrank
  by_contra hcon
  have hce : FooteCounterexample G t L := ⟨⟨hKp, hcore, htL, hmax, htype, hrank⟩, hcon⟩
  obtain ⟨G₀, _, _, hmin⟩ := exists_footeMinimal_of_counterexample hce
  obtain ⟨t₀, L₀, hce₀⟩ := hmin.1
  obtain ⟨hsimple, hrank2, hC⟩ := h31 G₀ t₀ L₀ hmin hce₀
  exact h5 G₀ t₀ L₀ hmin hce₀ hsimple hrank2 hC (h4 G₀ t₀ L₀ hmin hce₀ hsimple hrank2)

end CFSG.ComponentClassification.FooteLit
