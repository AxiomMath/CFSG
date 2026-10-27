module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCoreInner

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup

@[expose] def FooteL2OutAbelian : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f →
    Blueprint.LieModel S .PSL 2 p f →
      ∀ φ ψ : MulAut S, ∃ s : S, φ * ψ * φ⁻¹ * ψ⁻¹ = MulAut.conj s

@[expose] def FooteL2AbelianCore : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f →
    Blueprint.LieModel S .PSL 2 p f → ∀ i : MulAut S, orderOf i = 2 →
      ∀ x y : ↥(pPrimeCore 2 ↥(MonoidHom.eqLocus i.toMonoidHom (MonoidHom.id S))),
        x * y = y * x

@[expose] def FooteL2NineOddInner : Prop :=
  ∀ (S : Type) [Group S] [Finite S], Blueprint.LieModel S .PSL 2 3 2 → OddOuterInner S

@[expose] def FooteL2InvolutionSolvable : Prop :=
  ∀ (S : Type) [Group S] [Finite S],
    (Nonempty (S ≃* alternatingGroup (Fin 7)) ∨
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ Blueprint.LieModel S .PSL 2 p f) →
    ∀ s : S, orderOf s = 2 → Group.IsSolvable ↥(centralizer ({s} : Set S))

@[expose] def FooteL2RankThree : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f → p ^ f ≠ 9 →
    Blueprint.LieModel S .PSL 2 p f → ∀ E : Subgroup (MulAut S), (∀ e ∈ E, e * e = 1) →
      8 ≤ Nat.card E →
        ∃ e ∈ E, e ≠ 1 ∧
          ¬ Group.IsSolvable ↥(MonoidHom.eqLocus e.toMonoidHom (MonoidHom.id S))

end CFSG.ComponentClassification.FooteLit
