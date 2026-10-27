module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotHR8Kind
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotHR7iii
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

@[expose] def OmegaPlusResidualInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f → 2 ≤ f →
      Even f → 6 ≤ n → ∀ (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) (t : G),
      orderOf t = 2 → centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∃ S : Sylow 2 G, (S : Subgroup G) ≤ centralizer ({t} : Set G) ∧
        ∃ y ∈ (S : Subgroup G), ∃ w ∈ (S : Subgroup G), y * w * y⁻¹ * w⁻¹ ∉ L) →
      ∃ x : G, ∃ z ∈ L ⊓ CFSG.conjugate L x, x⁻¹ * t * x = t * z ∧
        (∃ hz : z ∈ L, IsLongRoot _ (e ⟨z, hz⟩)) ∧
        (∃ hz : z ∈ CFSG.conjugate L x,
          IsLongRoot _ (((conjugateMulEquiv L x).symm.trans e) ⟨z, hz⟩)) ∧
        ∀ l ∈ CFSG.conjugate L x, t * l * t⁻¹ = z * l * z⁻¹

@[expose] def OmegaPlusSwapRowInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f →
      4 ≤ Nat.card K → 6 ≤ n → ∀ (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K))
      (t : G), orderOf t = 2 → centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin n, ∀ htX : t ∈ centralizer (modelToG e (pairTorus (K := K) k) : Set G),
        NeighbourOvergroupOmega (QuotientGroup.mk'
            (oddCore (centralizer (modelToG e (pairTorus (K := K) k) : Set G))) ⟨t, htX⟩)
          (((modelToG e (pairPerp (K := K) k)).subgroupOf
              (centralizer (modelToG e (pairTorus (K := K) k) : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (modelToG e (pairTorus (K := K) k) :
              Set G))))) (n - 1) f) →
      (∀ k : Fin n, OmegaRowAt t (modelToG e (pairTorus (K := K) k))
        (modelToG e (pairPerp (K := K) k)) .swap) → False

@[expose] def OmegaPlusFourInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f → 2 ≤ f →
      ∀ (_ : L ≃* matrixProjectiveDerived (coordinateQuadPlus 4 K)) (t : G), orderOf t = 2 →
        centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t → False

@[expose] def OmegaPlusFiveInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f → 2 ≤ f →
      ∀ (_ : L ≃* matrixProjectiveDerived (coordinateQuadPlus 5 K)) (t : G), orderOf t = 2 →
        centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t → False

@[expose] def OmegaPlusTwoInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 → 5 ≤ n →
      ∀ (_ : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) (t : G), orderOf t = 2 →
        centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t → False

section HR7

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem not_normal_neighbour_pairTorus_of_residualInput (hres : OmegaPlusResidualInput)
    (hset : SeitzSetting G L) {n f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) (hn : 6 ≤ n)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) (k : Fin n) :
    ¬ (((modelToG e (pairPerp (K := K) k)).subgroupOf
        (centralizer (modelToG e (pairTorus (K := K) k) : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (modelToG e (pairTorus (K := K) k) :
          Set G))))).Normal := by
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hf2 : 2 ≤ f := (LinearPilot.four_le_card_iff_two_le hKc).1 hq
  rcases Nat.even_or_odd f with hfe | hfo
  · by_cases habel : ∀ S : Sylow 2 G, (S : Subgroup G) ≤ centralizer ({t} : Set G) →
        ∀ y ∈ (S : Subgroup G), ∀ z ∈ (S : Subgroup G), y * z * y⁻¹ * z⁻¹ ∈ L
    · exact not_normal_neighbour_pairTorus_of_habel hset hKc hq (by omega) e htC ht habel k rfl rfl
    · push Not at habel
      obtain ⟨S, hS, y, hy, w, hw, hyw⟩ := habel
      exact not_normal_neighbour_pairTorus_of_twoSided hset hKc hq (by omega) e htC ht
        (hres G L hset n f K hKc hf2 hfe hn e t ht hKt ⟨S, hS, y, hy, w, hw, hyw⟩) k rfl rfl
  · exact not_normal_neighbour_pairTorus_of_odd hset hfo hKc hq (by omega) e htC ht k rfl rfl

end HR7

end CFSG.SeitzReduction.OmegaPilot
