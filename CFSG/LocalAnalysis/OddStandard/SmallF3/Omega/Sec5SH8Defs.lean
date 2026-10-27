module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
public import CFSG.GroupTheory.PCore.Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.GorensteinWalter (PSL2 IsOddPrimePower)

structure Sec5SH8Linear {X : Type} [Group X] (P : Sylow 2 X) (F : Type) [Field F] [Finite F]
    (J : Subgroup X) : Prop where
  isOddPrimePower_card : IsOddPrimePower (Nat.card F)
  five_le_card : 5 ≤ Nat.card F
  normal : J.Normal
  nonempty_equiv : Nonempty (J ≃* PSL2 F)
  centralizer_eq_bot : Subgroup.centralizer (J : Set X) = ⊥
  eq_top_or_index_two : J = ⊤ ∨ J.index = 2
  central_involution_mem : ∀ z ∈ (P : Subgroup X), orderOf z = 2 →
    (∀ g ∈ (P : Subgroup X), z * g = g * z) → z ∈ J

@[expose] def Sec5SH8Shape {X : Type} [Group X] (P : Sylow 2 X) : Prop :=
  (P : Subgroup X) = ⊤ ∨ Nonempty (X ≃* alternatingGroup (Fin 7)) ∨
    Nonempty (X ≃* Equiv.Perm (Fin 4)) ∨
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (J : Subgroup X), Sec5SH8Linear P F J

@[expose] def Sec5SH8Statement : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.oddCore X = ⊥ →
    ∀ P : Sylow 2 X, Nonempty (↥P ≃* DihedralGroup 4) →
      Subgroup.normalClosure ((P : Subgroup X) : Set X) = ⊤ → Sec5SH8Shape P

end CFSG.OddStandard.SmallF3.Omega
