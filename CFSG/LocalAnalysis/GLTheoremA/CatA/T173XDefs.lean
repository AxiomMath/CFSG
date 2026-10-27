module

public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.LocalAnalysis.GLTheoremA.S10.CatDistinct
public import CFSG.LocalAnalysis.GLTheoremA.S12.Inputs123

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173X

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA

section Std

variable {G₀ : Type} [Group G₀]

@[expose] def stdLayer (d : G₀) : Subgroup G₀ := GLALayer (Subgroup.centralizer ({d} : Set G₀))

@[expose] def IsStdElt (p : ℕ) (A : Subgroup G₀) (d : G₀) : Prop :=
  d ∈ A ∧ d ≠ 1 ∧ d ^ p = 1 ∧
    IsComponentOf (stdLayer d) (Subgroup.centralizer ({d} : Set G₀)) ∧
    A ⊓ Subgroup.centralizer (stdLayer d : Set G₀) = Subgroup.zpowers d

@[expose] def innerClosure (A : Subgroup G₀) (d : G₀) : Subgroup G₀ :=
  closureIn (stdLayer d) (Subgroup.normalizer (A : Set G₀))

@[expose] def stdFamily (p : ℕ) (A : Subgroup G₀) (d : G₀) : Subgroup G₀ :=
  ⨆ (e : G₀) (_ : IsStdElt p A e ∧ Nonempty (PSimple p (stdLayer e) ≃* PSimple p (stdLayer d))), stdLayer e

@[expose] def StdVanishes (A : Subgroup G₀) (d : G₀) : Prop :=
  ¬ ∃ T : Subgroup G₀, T ≠ ⊥ ∧ IsPGroup 2 T ∧ innerClosure A d ⊔ A ≤ Subgroup.normalizer (T : Set G₀)

@[expose] def StdExtends (p : ℕ) (A : Subgroup G₀) (d : G₀) : Prop :=
  A = (A ⊓ stdLayer d) ⊔ (A ⊓ Subgroup.centralizer (stdLayer d : Set G₀)) ∧
    ∃ y : G₀, y ∈ Subgroup.centralizer (A : Set G₀) ∧ y ∈ Subgroup.centralizer (stdLayer d : Set G₀) ∧
      y ^ p = 1 ∧ y ∉ A

variable [Finite G₀]

@[expose] def StdTyped (p : ℕ) (A : Subgroup G₀) (d : G₀) : Prop :=
  stdFamily p A d ≤ innerClosure A d ∧ Type126 p (⊤ : Subgroup G₀) (stdLayer d) (innerClosure A d)

end Std

instance instFiniteOrthDerivedT173X {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (Q : QuadraticForm F V) : Finite ↥(CFSG.RankThree.Classical2.orthDerived Q) := by
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (V ≃ₗ[F] V) :=
    Finite.of_injective (fun f : V ≃ₗ[F] V => (f : V → V)) DFunLike.coe_injective
  infer_instance

@[expose] def ModelFactSplit : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (Q : QuadraticForm F V) (l p : ℕ), (QuadraticMap.polarBilin Q).Nondegenerate → Module.finrank F V = 2 * l →
    4 ≤ l → p.Prime → p ≠ 2 → p ∣ Nat.card F - 1 →
    ∀ (A : Subgroup ↥(CFSG.RankThree.Classical2.orthDerived Q)) (d : ↥(CFSG.RankThree.Classical2.orthDerived Q)),
      GLAIsBmax p A → IsStdElt p A d → StdVanishes A d

@[expose] def ModelFactFrameD : Prop :=
  CatDistinct.OrderBridge → ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (Q : QuadraticForm F V) (l : ℕ), (QuadraticMap.polarBilin Q).Nondegenerate → Module.finrank F V = 2 * l →
    4 ≤ l → Odd l → CFSG.GroupTheory.WeirSylow.IsPlusType Q → Nat.card F = 2 →
    ∀ (A : Subgroup ↥(CFSG.RankThree.Classical2.orthDerived Q)) (d : ↥(CFSG.RankThree.Classical2.orthDerived Q)),
      GLAIsBmax 3 A → IsStdElt 3 A d → StdVanishes A d ∨ StdTyped 3 A d

@[expose] def ModelFactFrameTD : Prop :=
  CatDistinct.OrderBridge → ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (Q : QuadraticForm F V) (l p : ℕ), (QuadraticMap.polarBilin Q).Nondegenerate → Module.finrank F V = 2 * l →
    4 ≤ l → Even l → ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q → p.Prime → p ≠ 2 → p ∣ Nat.card F + 1 →
    ∀ (A : Subgroup ↥(CFSG.RankThree.Classical2.orthDerived Q)) (d : ↥(CFSG.RankThree.Classical2.orthDerived Q)),
      GLAIsBmax p A → IsStdElt p A d → StdVanishes A d ∨ StdTyped p A d

@[expose] def ModelFactMixedD : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (Q : QuadraticForm F V) (l : ℕ), (QuadraticMap.polarBilin Q).Nondegenerate → Module.finrank F V = 2 * l →
    4 ≤ l → Even l → CFSG.GroupTheory.WeirSylow.IsPlusType Q → Nat.card F = 2 →
    ∀ (A : Subgroup ↥(CFSG.RankThree.Classical2.orthDerived Q)) (d : ↥(CFSG.RankThree.Classical2.orthDerived Q)),
      GLAIsBmax 3 A → IsStdElt 3 A d → StdVanishes A d ∨ StdExtends 3 A d

@[expose] def ModelFactMixedTD : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (Q : QuadraticForm F V) (l p : ℕ), (QuadraticMap.polarBilin Q).Nondegenerate → Module.finrank F V = 2 * l →
    4 ≤ l → Odd l → ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q → p.Prime → p ≠ 2 → p ∣ Nat.card F + 1 →
    ∀ (A : Subgroup ↥(CFSG.RankThree.Classical2.orthDerived Q)) (d : ↥(CFSG.RankThree.Classical2.orthDerived Q)),
      GLAIsBmax p A → IsStdElt p A d → StdVanishes A d ∨ StdExtends p A d

end CFSG.LocalAnalysis.GLTheoremA.T173X

end
