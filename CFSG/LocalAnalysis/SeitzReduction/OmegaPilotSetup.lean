module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSetup
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataQuotient
import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalOrthogonal
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointSchreier

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.EvenSmallLie
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus coordinateQuadMinus coordinatePlusWitnessEquiv coordinateMinusWitnessEquiv)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977 (HypothesisOne)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointSchreier
  (orthogonal_geometry_classical_model_Schreier)

section Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_kernel_of_hypothesisOne (hset : SeitzSetting G L) (hI : HypothesisOne L) :
    ∃ t : G, orderOf t = 2 ∧ t ∈ centralizer (L : Set G) ∧ t ∉ L ∧
      (∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) ∧
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t ∧
      centralizer ({t} : Set G) ≤ normalizer (L : Set G) := by
  have hI' : HypothesisOne (L ⧸ center L) :=
    hypothesisOne_of_mulEquiv (quotientCenterMulEquiv hset.center_eq_bot).symm hI
  obtain ⟨t, ht, htC, hsyl, hKt, hCtN, -⟩ :=
    F4Pilot.kernel hset.standardSetting hset.center_eq_bot hI'
  refine ⟨t, ht, htC, ?_, hsyl, hKt, hCtN⟩
  exact LinearPilot.not_mem_of_mem_centralizer hset.center_eq_bot htC fun h1 => by
    rw [h1, orderOf_one] at ht
    exact absurd ht (by decide)

theorem exists_setup_plus (hset : SeitzSetting G L) {n f : ℕ}
    (hL : CFSG.Blueprint.LieModel L .POmegaPlus n 2 f) :
    4 ≤ n ∧ 1 ≤ f ∧
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ f ∧
        Nonempty (L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) ∧
        Group.IsSolvable (Outer L) ∧
          ∃ t : G, orderOf t = 2 ∧ t ∈ centralizer (L : Set G) ∧ t ∉ L ∧
            (∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) ∧
            centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t ∧
            centralizer ({t} : Set G) ≤ normalizer (L : Set G) := by
  have hI := hypothesisOne_of_lieModel_POmegaPlus hL
  obtain ⟨t, ht, htC, htL, hsyl, hKt, hCtN⟩ := exists_kernel_of_hypothesisOne hset hI
  rcases hL with ⟨-, hst⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
  · obtain ⟨⟨-, hf, hn⟩, K, _, _, hK, ⟨e⟩⟩ := id hst
    have := LinearPilot.charP_two_of_card_eq_two_pow hK
    exact ⟨hn, hf, K, inferInstance, inferInstance, inferInstance, hK,
      ⟨coordinatePlusWitnessEquiv K e⟩,
      (orthogonal_geometry_classical_model_Schreier .POmegaPlus (Or.inr (Or.inl rfl)) hst).2.2,
      t, ht, htC, htL, hsyl, hKt, hCtN⟩
  · simp [CFSG.Blueprint.chevalleyExceptionalTags] at ht'
  · simp [CFSG.Blueprint.reeTitsTags] at ht'
  · cases ht'

theorem exists_setup_minus (hset : SeitzSetting G L) {n f : ℕ}
    (hL : CFSG.Blueprint.LieModel L .POmegaMinus n 2 f) :
    ∃ hn : 4 ≤ n, 1 ≤ f ∧
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (b c : K),
        (∀ s : K, s ^ 2 + b * s + c ≠ 0) ∧ Nat.card K = 2 ^ f ∧
        Nonempty (L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) ∧
        Group.IsSolvable (Outer L) ∧
          ∃ t : G, orderOf t = 2 ∧ t ∈ centralizer (L : Set G) ∧ t ∉ L ∧
            (∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) ∧
            centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t ∧
            centralizer ({t} : Set G) ≤ normalizer (L : Set G) := by
  have hI := hypothesisOne_of_lieModel_POmegaMinus hL
  obtain ⟨t, ht, htC, htL, hsyl, hKt, hCtN⟩ := exists_kernel_of_hypothesisOne hset hI
  rcases hL with ⟨-, hst⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
  · obtain ⟨⟨-, hf, hn⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := id hst
    have := LinearPilot.charP_two_of_card_eq_two_pow hK
    exact ⟨hn, hf, K, inferInstance, inferInstance, inferInstance, b, c, hirr, hK,
      ⟨coordinateMinusWitnessEquiv K (by omega) b c e⟩,
      (orthogonal_geometry_classical_model_Schreier .POmegaMinus (Or.inr (Or.inr rfl)) hst).2.2,
      t, ht, htC, htL, hsyl, hKt, hCtN⟩
  · simp [CFSG.Blueprint.chevalleyExceptionalTags] at ht'
  · simp [CFSG.Blueprint.reeTitsTags] at ht'
  · cases ht'

end Setup

theorem seitzExclusion_highPOmegaPlus_of_forall
    (h : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
      ∀ (n f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f → 4 ≤ n →
        (n, f) ≠ (4, 1) → ∀ (_ : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) (t : G),
          orderOf t = 2 → centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
            False) :
    SeitzExclusion HighPOmegaPlus := by
  rintro G _ _ L hset ⟨n, f, hn, hnf, hL⟩
  obtain ⟨-, -, K, _, _, _, hK, ⟨e⟩, -, t, ht, -, -, -, hKt, -⟩ := exists_setup_plus hset hL
  exact h G L hset n f K hK hn hnf e t ht hKt

theorem seitzExclusion_highPOmegaMinus_of_forall
    (h : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
      ∀ (n f : ℕ) (hn : 4 ≤ n) (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K),
        (∀ s : K, s ^ 2 + b * s + c ≠ 0) → Nat.card K = 2 ^ f → (n, f) ≠ (4, 1) →
        ∀ (_ : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) (t : G),
          orderOf t = 2 → centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
            False) :
    SeitzExclusion HighPOmegaMinus := by
  rintro G _ _ L hset ⟨n, f, -, hnf, hL⟩
  obtain ⟨hn, -, K, _, _, _, b, c, hirr, hK, ⟨e⟩, -, t, ht, -, -, -, hKt, -⟩ :=
    exists_setup_minus hset hL
  exact h G L hset n f hn K b c hirr hK hnf e t ht hKt

theorem seitzExclusion_highPOmegaPlus_of_cases
    (h4 : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
      ∀ (n f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f → 2 ≤ f →
        4 ≤ n → ∀ (_ : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) (t : G),
          orderOf t = 2 → centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
            False)
    (h2 : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
      ∀ (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 → 5 ≤ n →
        ∀ (_ : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) (t : G), orderOf t = 2 →
          centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t → False) :
    SeitzExclusion HighPOmegaPlus := by
  refine seitzExclusion_highPOmegaPlus_of_forall
    fun G _ _ L hset n f K _ _ _ hK hn hnf e t ht hKt => ?_
  rcases LinearPilot.card_eq_two_or_four_le hK with ⟨rfl, hK2⟩ | ⟨hf, -⟩
  · refine h2 G L hset n K hK2 ?_ e t ht hKt
    by_contra hn5
    exact hnf (by rw [show n = 4 by omega])
  · exact h4 G L hset n f K hK hf hn e t ht hKt

theorem seitzExclusion_highPOmegaMinus_of_cases
    (h4 : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
      ∀ (n f : ℕ) (hn : 4 ≤ n) (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K),
        (∀ s : K, s ^ 2 + b * s + c ≠ 0) → Nat.card K = 2 ^ f → 2 ≤ f →
        ∀ (_ : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) (t : G),
          orderOf t = 2 → centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
            False)
    (h2 : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
      ∀ (n : ℕ) (hn : 5 ≤ n) (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K),
        (∀ s : K, s ^ 2 + b * s + c ≠ 0) → Nat.card K = 2 →
        ∀ (_ : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) (t : G),
          orderOf t = 2 → centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
            False) :
    SeitzExclusion HighPOmegaMinus := by
  refine seitzExclusion_highPOmegaMinus_of_forall
    fun G _ _ L hset n f hn K _ _ _ b c hirr hK hnf e t ht hKt => ?_
  rcases LinearPilot.card_eq_two_or_four_le hK with ⟨rfl, hK2⟩ | ⟨hf, -⟩
  · have hn5 : 5 ≤ n := by
      by_contra hn5
      exact hnf (by rw [show n = 4 by omega])
    exact h2 G L hset n hn5 K b c hirr hK2 e t ht hKt
  · exact h4 G L hset n f hn K b c hirr hK hf e t ht hKt

end CFSG.SeitzReduction.OmegaPilot
