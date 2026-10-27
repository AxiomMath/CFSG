module

public import CFSG.GH74.GLS.C3.Layer2.L5C0

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2
  CFSG.GH74.GLS.C3.Layer2.Model

structure FusionHyp
    (M : Type) [Group M] [Finite M] (emb : ↥T5 →* M) (E : M → M → Prop) :
    Prop where
  equiv : Equivalence E
  conj : ∀ a s : M, E a (s * a * s⁻¹)
  f5 : ∀ (g : Amb 5), g ∈ Fgrp 5 → ∀ t s : ↥T5, g * (t : Amb 5) * g⁻¹ = (s : Amb 5) →
    E (emb t) (emb s)
  nbar : ∀ A ∈ n24L, ∀ i : Fin 16, E (emb (elT i)) (emb (elT (A i)))
  xmax : ∀ x' : M, E (emb x0T5) x' → Nat.card (Subgroup.centralizer ({x'} : Set M)) ≤ 32
  scp : ∀ t t' : M, t * t = 1 → E t t' →
    (∀ t'' : M, E t' t'' →
      Nat.card (Subgroup.centralizer ({t''} : Set M)) ≤
        Nat.card (Subgroup.centralizer ({t'} : Set M))) →
    ∃ φ : ↥(Subgroup.centralizer ({t} : Set M)) →* ↥(Subgroup.centralizer ({t'} : Set M)),
      Function.Injective φ ∧
        (φ ⟨t, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩ : M) = t' ∧
        ∀ s, E (φ s : M) (s : M)
  thompson : ∀ H : Subgroup M, H.index = 2 → ∀ u : M, u ∉ H → u * u = 1 →
    ∃ u' ∈ H, E u' u ∧ ∀ u'' : M, E u' u'' →
      Nat.card (Subgroup.centralizer ({u''} : Set M)) ≤
        Nat.card (Subgroup.centralizer ({u'} : Set M))

@[expose] def RExact
    (M : Type) [Group M] (emb : ↥T5 →* M) (E : M → M → Prop) : Prop :=
  ∀ a b : Fin 16, E (emb (elT a)) (emb (elT b)) → ∃ A ∈ n24L, A a = b

end CFSG.GH74.GLS.C3.Layer2.L5
