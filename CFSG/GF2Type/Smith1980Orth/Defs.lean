module

public import CFSG.LargeExtraspecial.S3Basic
public import CFSG.Open.TimmesfeldLargeExtraspecialMilestoneDefs
public import CFSG.Blueprint.Catalog
public import CFSG.Blueprint.ThreeFourPlusTranspositionClass

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open CFSG.LargeExtraspecial CFSG.Open CFSG.Blueprint

structure OrthData {G : Type*} [Group G] [Finite G] (S : Setting G) where
  q : QuadraticForm (ZMod 2) (Fin S.width → ZMod 2)
  nondeg : timmesfeldNondegenerate q
  four_le : 4 ≤ S.width
  even : Even S.width
  iso : Nonempty (S.Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldOmega q) ∨
    Nonempty (S.Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldIsometries q)

@[expose] def IdentInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G) (O : OrthData S),
    6 ≤ S.width → ThreeFourPlusClass G {g | IsConj S.z g} →
    (∃ a b : G, IsConj S.z a ∧ IsConj S.z b ∧ orderOf (a * b) = 4) →
    S.M.index % 4 = 3 →
      (timmesfeldPlusType O.q → LieModel G .POmegaPlus ((S.width + 4) / 2) 2 1) ∧
        (¬ timmesfeldPlusType O.q → LieModel G .POmegaMinus ((S.width + 4) / 2) 2 1)

@[expose] def IdentW4Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G) (O : OrthData S),
    S.width = 4 → ThreeFourPlusClass G {g | IsConj S.z g} →
    (∃ a b : G, IsConj S.z a ∧ IsConj S.z b ∧ orderOf (a * b) = 4) →
    S.M.index % 4 = 3 →
      (timmesfeldPlusType O.q → LieModel G .POmegaPlus 4 2 1) ∧
        (¬ timmesfeldPlusType O.q → LieModel G .POmegaMinus 4 2 1)

@[expose] def AltInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Setting G), OrthData S →
    ∀ n : ℕ, ¬ Nonempty (G ≃* alternatingGroup (Fin n))

@[expose] def FourW4Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), OrthData S →
    S.width = 4 → ∃ a b : G, IsConj S.z a ∧ IsConj S.z b ∧ orderOf (a * b) = 4

end CFSG.GF2Type.Smith1980Orth
