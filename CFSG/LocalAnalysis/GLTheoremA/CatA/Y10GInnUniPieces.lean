module

public import CFSG.LieType.SemisimpleCentralizers.HeldUnitaryComponents
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni

open CFSG.Open CFSG.LieType.SemisimpleCentralizers.Held CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.Y10F
open scoped commutatorElement

@[expose] def UniScalar : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (Q d : ℕ) (τ : K ≃+* K) (hτ : ∀ x, τ (τ x) = x),
    (∀ x, τ x = x ^ Q) → Nat.card K = Q ^ 2 → 3 ≤ d → (d, Q) ≠ (3, 2) →
      ∀ B : GL (Fin d) K, (∀ g : GL (Fin d) K, g ∈ StatedSU d Q K → ∃ c : K,
        (B : Matrix (Fin d) (Fin d) K) * (g : Matrix (Fin d) (Fin d) K) *
          ((B⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = c • (g : Matrix (Fin d) (Fin d) K)) →
      ∃ c : K, (B : Matrix (Fin d) (Fin d) K) = c • (1 : Matrix (Fin d) (Fin d) K)

@[expose] def UniLabelDict : Prop :=
  ∀ (J : Type) [Group J] [Finite J] (labJ : GLALabel) (a m : ℕ) (E : Type) [Field E] [Finite E]
    (τ' : E ≃+* E) (hτ' : ∀ x, τ' (τ' x) = x), 2 ≤ a → (∀ x, τ' x = x ^ (2 ^ m)) →
      Nat.card E = (2 ^ m) ^ 2 → HasLabel J (fun l : GLALabel => l = labJ) →
        Nonempty (J ⧸ Subgroup.center J ≃* heldSU a E τ' hτ' ⧸ Subgroup.center (heldSU a E τ' hτ')) →
          (canonLabel labJ).n = m

end CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni

end
