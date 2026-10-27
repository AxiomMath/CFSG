module

public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsAlpha

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T266

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

@[expose] def T266U6Fact (n : ℕ) : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (S A : Subgroup Ω),
    Odd n → 1 < n → S.Normal → CFSG.Open.IsQuasisimple ↥S → GLAPPrimeCore 3 ↥S = ⊥ →
    (∃ k : ℕ, Nat.card (Subgroup.center (PQuot 3 S)) = 3 ^ k) →
    catalogIs (PSimple 3 S) (S10.isU6n n) →
    IsElemAbelian 3 A → S ⊔ A = ⊤ →
    3 ^ GLATwoLocalRank 3 Ω ≤ Nat.card A →
    3 ^ 2 * Nat.card ↥(A ⊓ centModSubgroup 3 S) ≤ Nat.card A →
    InnDiagOn 3 A S →
    (∃ T : Subgroup Ω, T ≤ S ∧ IsPGroup 2 T ∧ A ≤ Subgroup.normalizer (T : Set Ω) ∧
      (⁅T, A⁆ : Subgroup Ω) ≠ ⊥) →
    (∀ E : Subgroup Ω, S10.IsE0 A S E → ¬ ∀ g ∈ E, CentMod 3 S g) →
    ∃ (E₀ : Subgroup Ω) (y : Ω), E₀ ≤ A ∧ Nat.card A ≤ 3 * Nat.card E₀ ∧ y ∈ E₀ ∧
      GLAPLayer 3 (S ⊓ Subgroup.centralizer (E₀ : Set Ω)) ≠ ⊥ ∧ ¬ CentMod 3 S y ∧
      ∃ J : Subgroup Ω, GLAPComponent 3 (S ⊓ Subgroup.centralizer ({y} : Set Ω)) J ∧
        catalogIs (PSimple 3 J) (S10.isUrn n) ∧
      ∃ T : Subgroup Ω, T ≤ S ⊓ Subgroup.centralizer ({y} : Set Ω) ∧ IsPGroup 2 T ∧
        A ≤ Subgroup.normalizer (T : Set Ω) ∧ (⁅T, A⁆ : Subgroup Ω) ≠ ⊥ ∧
        IsEmpty (T ≃* QuaternionGroup 2)

end CFSG.LocalAnalysis.GLTheoremA.T266

end
