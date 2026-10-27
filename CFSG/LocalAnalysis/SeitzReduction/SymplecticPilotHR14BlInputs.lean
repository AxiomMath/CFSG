module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphOmegaRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14BlShape

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ClassicalGroups.Orthogonal (elementaryGroup)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)

@[expose] def SpOmegaModelBType {X : Type*} [Group X] {K' : Type} [Field K'] {d : ℕ}
    {Q : QuadraticForm K' (Fin d → K')} (ε : X ≃* matrixProjectiveDerived Q) (α : MulAut X)
    (j : ℕ) : Prop :=
  ∃ (β : MulAut (matrixProjectiveDerived Q)) (s : matrixIsometries Q), s * s = 1 ∧
    (((s : GL (Fin d) K') : Matrix (Fin d) (Fin d) K') - 1).rank = 2 * j + 1 ∧
    β⁻¹ * MulAut.congr ε α * β = matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s)

@[expose] def SpOmegaBTorusInput (κ : Sp2mKind) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ n → Nat.card K = 2 ^ f →
    2 ≤ f → ∀ (e : L ≃* StatedSp n K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin n, RootKindSp e t f k κ) → SpOmegaRowGlobal e t f κ →
      ∀ j : ℕ, 1 ≤ j → 2 * j < n →
        centralizerPerfectCore (modelToG e (spATorus K n j)) ≤ centralizer ({t} : Set G)

end CFSG.SeitzReduction.SymplecticPilot
