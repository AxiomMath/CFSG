module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBInputs
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOModel
public import CFSG.LieType.Steinberg.CentralExt.SpinPlusCenter
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataSemilinear

public section

namespace CFSG.ComponentClassification.Burgoyne

open Matrix CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.TBLit
open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.UnbalancingLocal
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus
  coordinateQuadMinus)
open CFSG.LieType.Universal.Spin
open scoped MatrixGroups

@[expose] def BurgoynePropBSpinPlusKleinInput : Prop :=
  ∀ (F : Type) [Field F] [Finite F], ringChar F ≠ 2 → ∀ (n : ℕ) (hn : 6 ≤ n), Even n →
    ∀ (L : Type) [Group L] [Finite L] (α : spinGroup (quadPlus n F) →* L),
      Function.Surjective α → ∀ c : L, PropBHypII L c →
        c = α (CFSG.LieType.Steinberg.CentralExt.SpinPlusClosed.negOneS F (by omega : 3 ≤ n))

@[expose] def BurgoynePropBDrExcInput : Prop :=
  ∀ (J : Type) [Group J] [Finite J] (K : Subgroup J) [K.Normal] (t : J) (Y : Subgroup J)
    (c : K ⧸ pPrimeCore 2 K), PropBHyp J K t Y c →
    ∀ (τ : StatedLieTag) (n p f : ℕ), τ = .POmegaMinus ∨ (τ = .POmegaPlus ∧ 5 ≤ n) →
      LieModel (GeneralizedFitting.subgroup
        (conjQuotAction K (centralPreimage (pPrimeCore 2 K))).range) τ n p f →
    ∀ (F : Type) [Field F] [Finite F], ringChar F ≠ 2 → Nat.card F = p ^ f →
    ∀ R : GL (Fin (2 * n)) F, (R : Matrix (Fin (2 * n)) (Fin (2 * n)) F)ᵀ = R →
      (τ = .POmegaPlus ∧ ∀ v, O.oQ R v = coordinateQuadPlus n F v) ∨
      (τ = .POmegaMinus ∧ ∃ (hn : 1 ≤ n) (b c₀ : F), (∀ s : F, s ^ 2 + b * s + c₀ ≠ 0) ∧
        ∀ v, O.oQ R v = coordinateQuadMinus n F hn b c₀ v) →
    ∀ θ : GeneralizedFitting.subgroup (conjQuotAction K (centralPreimage (pPrimeCore 2 K))).range
      ≃* StatedProj (matrixDerived (O.oQ R)),
    ∀ g : similarityPairs (O.oQ R), g.val.right = 1 →
      socleAction θ ((conjQuotAction K (centralPreimage (pPrimeCore 2 K))).rangeRestrict t) =
        O.oκ _ g →
      (g.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) F)ᵀ * R =
        (-1 : F) • ((R : Matrix (Fin (2 * n)) (Fin (2 * n)) F) * g.val.left) → False

@[expose] def BurgoynePropBPlusFourInput : Prop :=
  ∀ (J : Type) [Group J] [Finite J] (K : Subgroup J) [K.Normal] (t : J) (Y : Subgroup J)
    (c : K ⧸ pPrimeCore 2 K), PropBHyp J K t Y c → ∀ p f : ℕ, p ≠ 2 →
    LieModel (GeneralizedFitting.subgroup
      (conjQuotAction K (centralPreimage (pPrimeCore 2 K))).range) .POmegaPlus 4 p f →
    ∃ u : K ⧸ pPrimeCore 2 K, orderOf u = 2 ∧ ∃ S₁ S₂ : Subgroup (K ⧸ pPrimeCore 2 K),
      S₁ ≤ centralizer ({u} : Set _) ∧ IsPComponent 2 (S₁.subgroupOf (centralizer ({u} : Set _))) ∧
      S₂ ≤ centralizer ({u} : Set _) ∧ IsPComponent 2 (S₂.subgroupOf (centralizer ({u} : Set _))) ∧
      (∃ p n : ℕ, ∃ _ : Fact p.Prime, p ≠ 2 ∧ 0 < n ∧
        Nonempty (S₁ ≃* SL(2, GaloisField p n)) ∧ Nonempty (S₂ ≃* SL(2, GaloisField p n))) ∧
      ⁅S₁, S₂⁆ = ⊥ ∧ S₁ ⊓ S₂ = ⊥ ∧
      (center ↥(S₁ ⊔ S₂)).map (S₁ ⊔ S₂).subtype = zpowers u ⊔ zpowers c ∧
      ActsProperlyVia (conjQuotAction K (pPrimeCore 2 K)) t Y S₁ ⊥ ∧
      ActsProperlyVia (conjQuotAction K (pPrimeCore 2 K)) t Y S₂ ⊥

end CFSG.ComponentClassification.Burgoyne
