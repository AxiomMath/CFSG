module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockLinCuts

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Lin

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.AGLEmbedding.LeviBlock
open scoped commutatorElement

variable (K : Type) [Field K] (n : ℕ) (I : Set ℕ)

noncomputable abbrev projFlag : Subgroup (projectiveSL n K) :=
  (flagStabilizer n K I).map (proj n K)

noncomputable abbrev projUni : Subgroup (projectiveSL n K) :=
  ((linLeviHom K n I).ker.map (flagStabilizer n K I).subtype).map (proj n K)

variable {K n}

@[expose] def NormFix (α : MulAut (projectiveSL n K)) : Prop :=
  (projFlag K n I).map α.toMonoidHom = projFlag K n I ∧
    ∀ a : Fin n, 2 ≤ linBlockLen n I a → ∀ x : flagStabilizer n K I,
      (∀ b : Fin n, b ≠ a → linLeviHom K n I x b = 1) →
      α (proj n K x) * (proj n K x)⁻¹ ∈ projUni K n I

@[expose] def LinModelComm : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ) (I : Set ℕ), 3 ≤ n →
    (∀ i ∈ I, 1 ≤ i ∧ i < n) → (∃ a : Fin n, 2 ≤ linBlockLen n I a) →
    ∀ α₁ α₂ : MulAut (projectiveSL n K), Odd (orderOf α₁) → Odd (orderOf α₂) →
      Odd (orderOf ⁅α₁, α₂⁆) → NormFix I α₁ → NormFix I α₂ → ⁅α₁, α₂⁆ = 1

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Lin
