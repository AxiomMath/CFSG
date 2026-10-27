module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Background.G6Natural

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.G6

variable {V : Type*} [CommGroup V]

@[expose] def IsSymNatSection (X : Subgroup (MulAut V)) (P Z : Subgroup V) (n : ℕ) : Prop :=
  (∀ x ∈ X, ∀ p ∈ P, x p ∈ P) ∧ ∃ (θ : X ≃* Equiv.Perm (Fin n)) (β : ↥P →* coreMod n),
    Function.Surjective β ∧ β.ker = Z.subgroupOf P ∧
    ∀ (x : X) (p : ↥P) (hp : (x : MulAut V) p ∈ P),
      β ⟨(x : MulAut V) p, hp⟩ = coreAct n (θ x) (β p)

@[expose] def IsAltNatSection (X : Subgroup (MulAut V)) (P Z : Subgroup V) (n : ℕ) : Prop :=
  (∀ x ∈ X, ∀ p ∈ P, x p ∈ P) ∧
    ∃ (θ : X ≃* alternatingGroup (Fin n)) (β : ↥P →* coreMod n),
    Function.Surjective β ∧ β.ker = Z.subgroupOf P ∧
    ∀ (x : X) (p : ↥P) (hp : (x : MulAut V) p ∈ P),
      β ⟨(x : MulAut V) p, hp⟩ = coreAct n ((θ x : alternatingGroup (Fin n)) : Equiv.Perm (Fin n))
        (β p)

@[expose] def IsSLNatSection (X : Subgroup (MulAut V)) (P Z : Subgroup V) (k : ℕ) : Prop :=
  (∀ x ∈ X, ∀ p ∈ P, x p ∈ P) ∧
    ∃ (θ : X ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 k))
      (β : ↥P →* Multiplicative (Fin 2 → GaloisField 2 k)),
    Function.Surjective β ∧ β.ker = Z.subgroupOf P ∧
    ∀ (x : X) (p : ↥P) (hp : (x : MulAut V) p ∈ P),
      β ⟨(x : MulAut V) p, hp⟩ = Multiplicative.ofAdd
        ((θ x : Matrix (Fin 2) (Fin 2) (GaloisField 2 k)).mulVec (Multiplicative.toAdd (β p)))

end CFSG.CGT.PushingUpLit.BHS
