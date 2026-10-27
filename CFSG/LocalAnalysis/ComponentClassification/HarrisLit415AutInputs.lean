module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Blueprint.Catalog
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup

@[expose] def AutPSL2RCentralizerInput : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (p n : ℕ), p.Prime → p ≠ 2 →
    Blueprint.LieModel Y .PSL 2 p n →
    ∀ R : Subgroup Y, (∃ Q : Sylow 2 Y, (Q : Subgroup Y) = R) → 8 ≤ Nat.card R →
    ∀ a : MulAut Y, (∃ k : ℕ, orderOf a = 2 ^ k) → (∀ x ∈ R, a x = x) → a * a = 1

@[expose] def AutPSL2RDerivedInput : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (p n : ℕ), p.Prime → p ≠ 2 →
    Blueprint.LieModel Y .PSL 2 p n →
    ∀ R : Subgroup Y, (∃ Q : Sylow 2 Y, (Q : Subgroup Y) = R) → 8 ≤ Nat.card R →
    ∀ δ ∈ R, 2 * orderOf δ = Nat.card R →
    ∀ P : Subgroup (MulAut Y), IsPGroup 2 P → (∀ x ∈ R, MulAut.conj x ∈ P) →
      ⁅P, P⁆ ≤ (zpowers δ).map (MulAut.conj : Y →* MulAut Y)

@[expose] def AutPSL2InvolutionCentralizerInput : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (p n : ℕ), p.Prime → p ≠ 2 →
    Blueprint.LieModel Y .PSL 2 p n → ∀ y : Y, orderOf y = 2 →
      IsPGroup 2 (↥(MulAction.stabilizer (MulAut Y) y) ⧸
        pPrimeCore 2 ↥(MulAction.stabilizer (MulAut Y) y))

end CFSG.ComponentClassification.HarrisLit
