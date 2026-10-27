module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

@[expose] def IsOm6P (L : Subgroup G) : Prop :=
  IsQuasisimple L ∧ IsOmega6Plus L

@[expose] def IsOm6M (L : Subgroup G) : Prop :=
  IsQuasisimple L ∧ IsOmega6Minus L

@[expose] def IsOm5Q (L : Subgroup G) : Prop :=
  IsQuasisimple L ∧ IsOmega5 L

@[expose] def twoRes (H : Subgroup G) : Subgroup G :=
  Subgroup.closure {g | g ∈ H ∧ Odd (orderOf g)}

@[expose] def twoPrimeRes (H : Subgroup G) : Subgroup G :=
  Subgroup.closure {g | g ∈ H ∧ ∃ k : ℕ, orderOf g = 2 ^ k}

@[expose] def XOut (L : Subgroup G) (s : G) : Subgroup G :=
  twoPrimeRes (twoRes (L ⊓ centralizer ({s} : Set G)))

@[expose] def InnerOn (L : Subgroup G) (s : G) : Prop :=
  s ∈ L ⊔ centralizer (L : Set G)

@[expose] def InducesProjective (L : Subgroup G) (n : ℕ) (ε : ℤˣ) (s : G) : Prop :=
  ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 3) V) (_ : FiniteDimensional (ZMod 3) V)
    (Q : QuadraticForm (ZMod 3) V) (hQ : Q.Nondegenerate)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) (x : ProjSim Q),
    Module.finrank (ZMod 3) V = n ∧ quadSign Q = ε ∧
      InducesViaP L (Subgroup.center ↥L) hQ e s x ∧ SimIsProjective x

@[expose] def TypesInModel (L : Subgroup G) (n : ℕ) (ε : ℤˣ) (r : ℕ) (α : ℤˣ) (r' : ℕ) (α' : ℤˣ)
    (s s' : G) : Prop :=
  ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 3) V) (_ : FiniteDimensional (ZMod 3) V)
    (Q : QuadraticForm (ZMod 3) V) (hQ : Q.Nondegenerate)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) (x x' : ProjSim Q),
    Module.finrank (ZMod 3) V = n ∧ quadSign Q = ε ∧
      InducesViaP L (Subgroup.center ↥L) hQ e s x ∧ SimHasType x r α ∧
      InducesViaP L (Subgroup.center ↥L) hQ e s' x' ∧ SimHasType x' r' α'

end CFSG.OddStandard.SmallF3.Omega
