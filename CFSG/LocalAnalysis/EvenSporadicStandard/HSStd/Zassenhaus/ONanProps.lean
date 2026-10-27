module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Basic
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

@[expose] def ONanList (N : Type) [Group N] : Prop :=
  LieModel N .PSU 3 5 1 ∨ LieModel N .PSL 3 7 1 ∨ IsSporadic N .M22 ∨ IsSporadic N .M23 ∨
    IsSporadic N .M24 ∨ IsSporadic N .HS ∨ IsSporadic N .Ru ∨ LieModel N .PSL 5 2 1 ∨
    IsSporadic N .J2 ∨ LieModel N .PSp 2 2 2

@[expose] def ONan77S5 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.SectionRank.IsKGroupCat Y →
    (∀ A : Subgroup Y, A.Normal → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → A = ⊥) →
    ∀ P : Subgroup Y, (∀ a ∈ P, ∀ b ∈ P, a * b = b * a) → (∀ a ∈ P, a ^ 3 = 1) →
    Nat.card P = 9 →
    (∀ a ∈ P, a ≠ 1 → Nonempty (↥(centralizer ({a} : Set Y)) ≃*
      Multiplicative (ZMod 3) × Equiv.Perm (Fin 5))) →
    ∃ N : Subgroup Y, N.Normal ∧ centralizer (N : Set Y) ≤ N ∧ ONanList ↥N

@[expose] def ONanInspection : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (N : Subgroup Y), N.Normal → centralizer (N : Set Y) ≤ N →
    ONanList ↥N →
    ∀ P : Subgroup Y, (∀ a ∈ P, ∀ b ∈ P, a * b = b * a) → (∀ a ∈ P, a ^ 3 = 1) →
    Nat.card P = 9 → (∀ a ∈ P, a ≠ 1 → Nat.card (centralizer ({a} : Set Y)) = 360) →
    (∃ w : Y, orderOf w = 2 ∧ ∃ H : Subgroup Y, H ≤ centralizer ({w} : Set Y) ∧
      Nonempty (↥H ≃* ↥CFSG.QuasithinUnique.A6Models.pgl29)) →
    IsSporadic Y .HS

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus
