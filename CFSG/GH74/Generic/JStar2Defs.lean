module

public import CFSG.GH74.Generic.JMaxDefs

public section

namespace CFSG.GH74.Generic

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup

@[expose] def IsAltQuot (K : Type) [Group K] : Prop :=
  (∃ n : ℕ, 5 ≤ n ∧ Nonempty (K ⧸ center K ≃* alternatingGroup (Fin n))) ∧ ¬ OfLieType K

section Pairs

variable {G : Type} [Group G]

@[expose] def IsILoG2 (x : G) (M : Subgroup G) : Prop :=
  IsILo 2 x M ∧ InG2 (↥M ⧸ pPrimeCore 2 ↥M)

variable (G) in
@[expose] noncomputable def depthOfG : ℕ :=
  sInf {d : ℕ | ∃ (x : G) (M : Subgroup G), IsILoG2 x M ∧ d2 (↥M ⧸ pPrimeCore 2 ↥M) = d}

@[expose] def IsJ2 (x : G) (M : Subgroup G) : Prop :=
  IsILoG2 x M ∧ d2 (↥M ⧸ pPrimeCore 2 ↥M) = depthOfG G ∧ IsTwoTerminal x M

@[expose] def IsJ2Alt (x : G) (M : Subgroup G) : Prop :=
  IsJ2 x M ∧ IsAltQuot (↥M ⧸ pPrimeCore 2 ↥M)

@[expose] def IsJ2Circ (x : G) (M : Subgroup G) : Prop :=
  IsJ2 x M ∧ (1 < pRank 2 ↥(CxK x M) ∨ ∀ (x' : G) (M' : Subgroup G), IsJ2 x' M' → pRank 2 ↥(CxK x' M') ≤ 1)

end Pairs

end CFSG.GH74.Generic
