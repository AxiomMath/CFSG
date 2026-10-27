module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphBasic
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotHR8Kind
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotFieldYModel

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadMinus)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (fieldAutT)
open CFSG.SeitzReduction.TwistedE6Pilot (coordinateQuadMinus_fieldMap_of_fixed)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

@[expose] def OmegaMinusSwapRowInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K) (hn : 6 ≤ n),
      Nat.card K = 2 ^ f → 4 ≤ Nat.card K → (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
      ∀ (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) (t : G),
      orderOf t = 2 → centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin (n - 1), ∀ htX : t ∈ centralizer
          (modelToG e (minusPairTorus (K := K) (by omega) b c k) : Set G),
        NeighbourOvergroupOmega (QuotientGroup.mk' (oddCore (centralizer
            (modelToG e (minusPairTorus (K := K) (by omega) b c k) : Set G))) ⟨t, htX⟩)
          (((modelToG e (minusPairPerp (K := K) (by omega) b c k)).subgroupOf
              (centralizer (modelToG e (minusPairTorus (K := K) (by omega) b c k) :
                Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer
              (modelToG e (minusPairTorus (K := K) (by omega) b c k) : Set G))))) (n - 1) f) →
      (∀ k : Fin (n - 1), OmegaRowAt t (modelToG e (minusPairTorus (K := K) (by omega) b c k))
        (modelToG e (minusPairPerp (K := K) (by omega) b c k)) .swap) → False

@[expose] def OmegaMinusFieldRowEndInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n : ℕ) (hn : 6 ≤ n) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
    ∀ (G₀ : Subgroup G), L ≤ G₀ → ∀ htN : t ∈ normalizer (G₀ : Set G),
    ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (σ : F ≃+* F), orderOf σ = 2 →
    ∀ (β γ : F) (hβ : σ β = β) (hγ : σ γ = γ), (∀ s : F, σ s = s → s ^ 2 + β * s + γ ≠ 0) →
    ∀ ψ : G₀ ≃* matrixProjectiveDerived (coordinateQuadMinus n F (by omega) β γ),
      MulAut.congr ψ (G₀.normalizerMonoidHom ⟨t, htN⟩) =
        fieldAutT (coordinateQuadMinus n F (by omega) β γ) σ
          (coordinateQuadMinus_fieldMap_of_fixed (by omega) hβ hγ) →
      (∀ g : G, g⁻¹ * t * g ∈ normalizer (G₀ : Set G) → g ∈ normalizer (G₀ : Set G)) → False

@[expose] def OmegaMinusFourInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K),
      (∀ s : K, s ^ 2 + b * s + c ≠ 0) → Nat.card K = 2 ^ f → 2 ≤ f →
      ∀ (_ : L ≃* matrixProjectiveDerived (coordinateQuadMinus 4 K (by norm_num) b c)) (t : G),
        orderOf t = 2 → centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t → False

@[expose] def OmegaMinusTwoInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n : ℕ) (hn : 5 ≤ n) (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K),
      (∀ s : K, s ^ 2 + b * s + c ≠ 0) → Nat.card K = 2 →
      ∀ (_ : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) (t : G),
        orderOf t = 2 → centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t → False

@[expose] def OmegaMinusGraphCoordinateInput : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (n : ℕ) (hn : 5 ≤ n) (β γ : F) (σ : F ≃+* F),
    orderOf σ = 2 → ∀ (hβ : σ β = β) (hγ : σ γ = γ), (∀ s : F, σ s = s → s ^ 2 + β * s + γ ≠ 0) →
    ∃ E : Subgroup (MulAut (matrixProjectiveDerived (coordinateQuadMinus n F (by omega) β γ))),
      E.index = 2 ∧ (∀ x, MulAut.conj x ∈ E) ∧
      fieldAutT (coordinateQuadMinus n F (by omega) β γ) σ
        (coordinateQuadMinus_fieldMap_of_fixed (by omega) hβ hγ) ∉ E

theorem omegaMinusFieldRowEndInput_of_graphCoordinate (hχ : OmegaMinusGraphCoordinateInput) :
    OmegaMinusFieldRowEndInput := by
  intro G _ _ L hset n hn t ht hKt G₀ hLG htN F _ _ _ σ hσ β γ hβ hγ hirr ψ hψ huniq
  have : IsSimpleGroup G := hset.1
  obtain ⟨E, hE2, hEInn, hEσ⟩ := hχ F n (by omega) β γ σ hσ hβ hγ hirr
  have : E.Normal := Subgroup.normal_of_index_eq_two hE2
  have : E.FiniteIndex := ⟨by rw [hE2]; norm_num⟩
  have hρt : F4Pilot.normalizerMulAut ψ ⟨t, htN⟩ =
      fieldAutT (coordinateQuadMinus n F (by omega) β γ) σ
        (coordinateQuadMinus_fieldMap_of_fixed (by omega) hβ hγ) := hψ
  have hQ : ¬ 4 ∣ Nat.card (MulAut (matrixProjectiveDerived
      (coordinateQuadMinus n F _ β γ)) ⧸ E) := by
    change ¬ 4 ∣ E.index
    rw [hE2]
    decide
  refine EPilot.false_of_simple_of_mulAut_hom ψ htN ht huniq (QuotientGroup.mk' E) hQ
    (fun x => (QuotientGroup.eq_one_iff _).2 (hEInn x)) ?_
  rw [hρt]
  exact fun h => hEσ ((QuotientGroup.eq_one_iff _).1 h)

end CFSG.SeitzReduction.OmegaPilot
