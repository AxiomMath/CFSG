module

public import CFSG.CGT.PushingUpLit.BHS.NaturalDefs
public import CFSG.CGT.PushingUpLit.BHS.Replacement
public import CFSG.RankThree.PartOne.S9.Defs
public import CFSG.Quasithin.Background.A1bBasic
public import CFSG.CGT.PushingUpLit.BHS.SymNatDefs
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne

section SetNormalizer

variable {Γ : Type*} [Group Γ]

@[expose] def setNormalizer (P : Subgroup Γ) (S : Set (Subgroup Γ)) : Subgroup Γ where
  carrier := {g | g ∈ P ∧ ∀ A : Subgroup Γ, A ∈ S ↔ conjSub g A ∈ S}
  one_mem' := ⟨P.one_mem, fun A => by rw [conjSub_one]⟩
  mul_mem' := by
    rintro g h ⟨hgP, hg⟩ ⟨hhP, hh⟩
    refine ⟨P.mul_mem hgP hhP, fun A => ?_⟩
    rw [conjSub_mul, ← hg, ← hh]
  inv_mem' := by
    rintro g ⟨hgP, hg⟩
    refine ⟨P.inv_mem hgP, fun A => ?_⟩
    rw [hg (conjSub g⁻¹ A), ← conjSub_mul, mul_inv_cancel, conjSub_one]

end SetNormalizer

variable {V : Type} [CommGroup V]

structure Hyp41 (P : Subgroup (MulAut V)) (D : Set (Subgroup (MulAut V))) : Prop where
  le : ∀ A ∈ D, A ≤ P
  ne_bot : ∀ A ∈ D, A ≠ ⊥
  elemAb : ∀ A ∈ D, IsElemAbelian2 A
  conj_mem : ∀ A ∈ D, ∀ g ∈ P, conjSub g A ∈ D
  quad : ∀ A ∈ D, IsQuadratic A
  card_eq : ∀ A ∈ D, Nat.card V = Nat.card A * Nat.card (fixV A)
  fixV_eq : ∀ A ∈ D, ∀ a ∈ A, a ≠ 1 → fixV (Subgroup.zpowers a) = fixV A
  card_prod : ∀ A ∈ D, ∀ B ∈ D, B ≠ A → (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) →
    Nat.card V = Nat.card A * Nat.card B * Nat.card (fixV (A ⊔ B))

@[expose] def dInter (D : Set (Subgroup (MulAut V))) (U : Subgroup (MulAut V)) :
    Set (Subgroup (MulAut V)) :=
  {A | A ∈ D ∧ A ≤ U}

@[expose] def dCore (P : Subgroup (MulAut V)) (D : Set (Subgroup (MulAut V)))
    (U : Subgroup (MulAut V)) : Set (Subgroup (MulAut V)) :=
  {A | A ∈ D ∧ ∀ g ∈ P, A ≤ conjSub g U}

structure Hyp42 (P : Subgroup (MulAut V)) (D : Set (Subgroup (MulAut V)))
    (T M : Subgroup (MulAut V)) : Prop extends Hyp41 P D where
  syl : IsSylowOf 2 T P
  le_M : T ≤ M
  M_le : M ≤ P
  ne_core : D ≠ dCore P D M
  normSet_le : setNormalizer P (dInter D T) ≤ M
  cen_le : cenIn P (fixV T) ≤ M

structure Hyp43 (P : Subgroup (MulAut V)) (D : Set (Subgroup (MulAut V)))
    (T M : Subgroup (MulAut V)) : Prop extends Hyp42 P D T M where
  max : ∀ A ∈ D, ∀ X : Subgroup (MulAut V), IsElemAbelian2 X → X ≤ P →
    Nat.card X * Nat.card (fixV X) ≤ Nat.card A * Nat.card (fixV A)

@[expose] def mSet (P M A : Subgroup (MulAut V)) : Set (Subgroup (MulAut V)) :=
  {Y | (∃ g ∈ P, Y = conjSub g M) ∧ A ≤ Y}

@[expose] def lamSet (P : Subgroup (MulAut V)) (D : Set (Subgroup (MulAut V)))
    (M : Subgroup (MulAut V)) : Set (Subgroup (MulAut V)) :=
  {L | L ≤ P ∧ (∃ n : ℕ, 1 ≤ n ∧ IsSLNatSection L ⊤ (fixV L) n) ∧
    (∀ A : Subgroup (MulAut V), A ∈ dInter D L ↔ IsSylowOf 2 A L) ∧
    (∀ A ∈ dInter D L, ∀ B ∈ dInter D L, A ≠ B → mSet P M A ≠ mSet P M B)}

end CFSG.CGT.PushingUpLit.BHS
