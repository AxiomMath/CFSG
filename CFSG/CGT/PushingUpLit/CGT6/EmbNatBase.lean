module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CGT.PushingUpLit.BHS6.Basic
public import CFSG.CGT.PushingUpLit.Transport

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS6

@[expose] def altAct (n : ℕ) :
    alternatingGroup (Fin n) → ↥(G6.coreMod n) → ↥(G6.coreMod n) :=
  fun s v => G6.coreAct n (s : Equiv.Perm (Fin n)) v

@[expose] def IsNatSectionWith {V : Type*} [CommGroup V] {S M : Type*} [Group S] [Group M]
    (act : S → M → M) {X : Subgroup (MulAut V)} (θ : X ≃* S) (P Z : Subgroup V) : Prop :=
  (∀ x ∈ X, ∀ p ∈ P, x p ∈ P) ∧ ∃ β : ↥P →* M, Function.Surjective β ∧
    β.ker = Z.subgroupOf P ∧
    ∀ (x : X) (p : ↥P) (hp : (x : MulAut V) p ∈ P),
      β ⟨(x : MulAut V) p, hp⟩ = act (θ x) (β p)

@[expose] def orbitSpan {V : Type*} [CommGroup V] (X : Subgroup (MulAut V)) (v : V) :
    Subgroup V :=
  Subgroup.closure {w | ∃ x ∈ X, w = x v}

end CFSG.CGT.PushingUpLit.CGT6
