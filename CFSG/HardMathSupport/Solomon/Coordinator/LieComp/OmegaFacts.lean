module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Export
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.RankThree.Classical2

@[expose] def OmegaFactorFacts : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (V : Type) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V), (QuadraticMap.polarBilin Q).Nondegenerate →
    ∀ L : Subgroup ↥(orthDerived Q), L.Normal → CFSG.IsQuasisimple ↥L →
      ∃ (X : Type) (_ : Group X) (_ : Finite X), LieFactorData (ringChar K) X ∧
        ∃ f : X →* ↥L, Function.Surjective f ∧ f.ker ≤ Subgroup.center X

@[expose] def OrthFactorOver (ℓ q : ℕ) (X : Type) [Group X] : Prop :=
  (∃ (m j : ℕ) (E : Type) (_ : Field E) (_ : Fintype E), 2 ≤ m ∧ 1 ≤ j ∧ ringChar E = ℓ ∧
      Fintype.card E = q ^ j ∧ (m = 2 → 4 ≤ Fintype.card E) ∧
      Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin m) E))
  ∨ (∃ (m j q' : ℕ) (E : Type) (_ : Field E) (_ : Fintype E), 3 ≤ m ∧ 1 ≤ j ∧
      ringChar E = ℓ ∧ q' = q ^ j ∧ Fintype.card E = q' ^ 2 ∧ (m, q') ≠ (3, 2) ∧
      Nonempty (X ≃* ↥(CFSG.Open.StatedSU m q' E)))
  ∨ (∃ (K' : Type) (_ : Field K') (_ : Fintype K'), Nat.card K' = q ∧ ringChar K' = ℓ ∧
      ∃ s : ℕ, 2 ≤ s ∧ (s, Nat.card K') ≠ (2, 2) ∧
        Nonempty (X ≃* ↥(CFSG.Open.StatedSp s K')))
  ∨ (∃ (K' : Type) (_ : Field K') (_ : Fintype K') (V : Type) (_ : AddCommGroup V)
        (_ : Module K' V) (_ : FiniteDimensional K' V) (Q : QuadraticForm K' V),
      Nat.card K' = q ∧ ringChar K' = ℓ ∧ (QuadraticMap.polarBilin Q).Nondegenerate ∧
      7 ≤ Module.finrank K' V ∧
      (∃ U : Submodule K' V, Module.finrank K' U = 3 ∧ ∀ u ∈ U, Q u = 0) ∧
      Nonempty (X ≃* ↥(orthDerived Q)))

@[expose] def OmegaFactorField : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (V : Type) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V), (QuadraticMap.polarBilin Q).Nondegenerate →
    ∀ L : Subgroup ↥(orthDerived Q), L.Normal → CFSG.IsQuasisimple ↥L →
      ∃ (X : Type) (_ : Group X) (_ : Finite X),
        LieFactorData (ringChar K) X ∧ OrthFactorOver (ringChar K) (Nat.card K) X ∧
        ∃ f : X →* ↥L, Function.Surjective f ∧ f.ker ≤ Subgroup.center X

@[expose] def OmegaAltSixFacts : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (V : Type) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V), (QuadraticMap.polarBilin Q).Nondegenerate →
    ∀ L : Subgroup ↥(orthDerived Q), L.Normal → CFSG.IsQuasisimple ↥L →
      Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* alternatingGroup (Fin 6)) →
        ringChar K = 3 ∧ Module.finrank K V ≤ 4

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
