module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.TBAssembly
public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.AdjDispIso

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw CFSG.LieType.Steinberg
  CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc TensorProduct


variable {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] [CharP K 2]
  (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))

include hf hK hσ in
theorem tw78_finrank_big {k : Type} [Field k] [Finite k] [CharP k 2] [Algebra K k] {m : ℕ}
    {ρ : Representation k ↥(TwistedE6.fixedGroup K σ) (Fin m → k)} (hρ : IsSimpleRep ρ)
    {y : Fin m → k} {χ : ↥(TwistedE6.fixedGroup K σ) → k} {J : Finset TwN}
    (ht : IsCoverType (twistedE6CoverRankOne hf hK σ hσ) ρ y χ J)
    (h78 : Tw78Type hf K hK σ hσ k χ J) : m = 78 := by
  obtain ⟨b, β, hβ⟩ := twE6_iso_78 hf hK σ hσ hρ ht h78
  have h1 := LinearEquiv.finrank_eq β
  rw [finrank_frobTwist, Module.finrank_fin_fun, Module.finrank_baseChange, finrank_adj78] at h1
  exact h1.symm

include hf hK hσ in
theorem tw78Dim_holds : Tw78Dim hf K hK σ hσ :=
  fun k _ _ _ _ m ρ y χ J hρ ht h78 => tw78_finrank_big hf K hK σ hσ hρ ht h78

include hf hK hσ in
theorem twTypeBoundStmt_holds_wide (hF1 : TwF1Residual hf K hK σ hσ) (hF2 : TwExistsDigitF2) :
    TwTypeBoundStmt hf K hK σ hσ :=
  twTypeBoundStmt_holds hf K hK σ hσ hF1 hF2 (tw78Dim_holds hf K hK σ hσ)

end CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6
