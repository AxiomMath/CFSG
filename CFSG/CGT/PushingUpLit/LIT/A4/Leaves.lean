module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.CGT.PushingUpLit.A4

open CFSG.Open

@[expose] def NoTwoQuotient (G : Type*) [Group G] : Prop :=
  ∀ (N : Subgroup G) [N.Normal], IsPGroup 2 (G ⧸ N) → N = ⊤

@[expose] def HaradaTransfer211 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], NoTwoQuotient G →
    ∀ M M₁ S A : Subgroup G, M₁ ≤ M → M₁.relIndex M = 2 → S ≤ M → IsPGroup 2 S →
      ¬ 2 ∣ S.relIndex M → A ≤ S → (A.subgroupOf S).Normal →
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → (∀ a ∈ A, a ^ 4 = 1) →
      Subgroup.normalizer (A : Set G) ≤ M →
      (∀ g : G, A.map (MulAut.conj g).toMonoidHom ≤ M →
        ∃ m ∈ M, A.map (MulAut.conj g).toMonoidHom = A.map (MulAut.conj m).toMonoidHom) →
      ∃ g : G, g ∉ M ∧ M.relIndex (A.map (MulAut.conj g).toMonoidHom) ≤ 2 ∧
        ¬ (A.map (MulAut.conj g).toMonoidHom ⊓ M ≤ M₁)

end CFSG.CGT.PushingUpLit.A4
