module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmega

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.OmegaRadical
open CFSG.ClassicalGroups.Orthogonal (elementaryGroup)

@[expose] def SpTwoOmegaStepOneInput (κ : Sp2mKind) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 → 4 ≤ n →
    ∀ (e : L ≃* StatedSp (n + 1) K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin (n + 1), NsKindSp e t k κ) → NsRowGlobal e t (q2GlobalKind κ) →
      ∀ (g : G) (hg : g⁻¹ * t * g ∈ normalizer (nsGlobal e : Set G)),
        (nsGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩ ∉
          (MulAut.conj : nsGlobal e →* MulAut (nsGlobal e)).range

@[expose] def SpTwoOmegaBClassInput (κ : Sp2mKind) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 → 4 ≤ n →
    ∀ (e : L ≃* StatedSp (n + 1) K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin (n + 1), NsKindSp e t k κ) → NsRowGlobal e t (q2GlobalKind κ) →
      ∀ (g : G) (hg : g⁻¹ * t * g ∈ normalizer (nsGlobal e : Set G))
        (K' : Type) [Field K'] [Finite K'] (Q : QuadraticForm K' (Fin (2 * (n + 1 + 1)) → K')),
        Nat.card K' = 2 ^ 1 → Q.polarBilin.Nondegenerate →
        (∃ T : Submodule K' (Fin (2 * (n + 1 + 1)) → K'), Module.finrank K' T = 3 ∧
          ∀ x ∈ T, Q x = 0) →
        ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
          elementaryGroup Q →
        ∀ (ε : nsGlobal e ≃* matrixProjectiveDerived Q) (β : MulAut (matrixProjectiveDerived Q))
          (s : matrixIsometries Q), s * s = 1 →
          Odd (((s : GL (Fin (2 * (n + 1 + 1))) K') :
            Matrix (Fin (2 * (n + 1 + 1))) (Fin (2 * (n + 1 + 1))) K') - 1).rank →
          3 ≤ (((s : GL (Fin (2 * (n + 1 + 1))) K') :
            Matrix (Fin (2 * (n + 1 + 1))) (Fin (2 * (n + 1 + 1))) K') - 1).rank →
          β⁻¹ * MulAut.congr ε ((nsGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩) * β ≠
            matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s)

end CFSG.SeitzReduction.SymplecticPilot
