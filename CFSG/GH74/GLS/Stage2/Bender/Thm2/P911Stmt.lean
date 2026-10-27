module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.P911

open Subgroup CFSG CFSG.GH74 CFSG.Blueprint CFSG.GH74.GLS.Stage2.Signalizer.Odd87

@[expose] def hbar (Y : Type) [Group Y] (V : Subgroup (MulAut Y)) (z : MulAut Y) :
    Subgroup (MulAut Y) :=
  (MulAut.conj : Y →* MulAut Y).range ⊔ V ⊔ zpowers z

@[expose] def Cfg911 (Y : Type) [Group Y] (p : ℕ) (V : Subgroup (MulAut Y)) (z : MulAut Y) :
    Prop :=
  p.Prime ∧ Odd p ∧ IsElementaryAbelian p ↥V ∧ Nat.card ↥V = p ^ 2 ∧
    z ≠ 1 ∧ z * z = 1 ∧ (∀ v ∈ V, v * z = z * v) ∧
    (∃ O : Subgroup (MulAut Y), O ≤ hbar Y V z ∧ V ≤ O ∧ Odd (Nat.card ↥O) ∧
      (∀ o ∈ O, o * z = z * o) ∧
      ∀ c ∈ hbar Y V z, c * z = z * c → ∀ o ∈ O, c * o * c⁻¹ ∈ O) ∧
    (∀ v ∈ V, v ≠ 1 → layer ↥(fixSub v) = ⊥)

@[expose] def No911 (Y : Type) [Group Y] : Prop :=
  ∀ (p : ℕ) (V : Subgroup (MulAut Y)) (z : MulAut Y), ¬ Cfg911 Y p V z

@[expose] def Core911Fam (F : (Y : Type) → [Group Y] → Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsSimpleGroup Y → (∃ a b : Y, a * b ≠ b * a) →
    F Y → No911 Y

@[expose] def FTwoNL34 (Y : Type) [Group Y] : Prop :=
  LieModel Y .PSL 2 2 3 ∨ LieModel Y .PSL 2 2 4 ∨ LieModel Y .PSU 3 2 2 ∨
    LieModel Y .twistedB2 0 2 3

@[expose] def Core911Alt : Prop := Core911Fam FAlt
@[expose] def Core911Spor : Prop := Core911Fam FSpor
@[expose] def Core911McLy : Prop := Core911Fam FMcLy
@[expose] def Core911Two : Prop := Core911Fam FTwoNL34
@[expose] def Core911L2 : Prop := Core911Fam FL2
@[expose] def Core911L3 : Prop := Core911Fam FL3
@[expose] def Core911U3 : Prop := Core911Fam FU3
@[expose] def Core911Sp4 : Prop := Core911Fam FSp4
@[expose] def Core911G2 : Prop := Core911Fam FG2
@[expose] def Core911D4 : Prop := Core911Fam FD4
@[expose] def Core911L4 : Prop := Core911Fam FL4
@[expose] def Core911U4 : Prop := Core911Fam FU4
@[expose] def Core911L5 : Prop := Core911Fam FL5
@[expose] def Core911U5 : Prop := Core911Fam FU5
@[expose] def Core911Ree : Prop := Core911Fam FRee

theorem no911_of_families (hAlt : Core911Alt) (hSpor : Core911Spor) (hMcLy : Core911McLy)
    (hTwo : Core911Two) (hL2 : Core911L2) (hL3 : Core911L3) (hU3 : Core911U3)
    (hSp4 : Core911Sp4) (hG2 : Core911G2) (hD4 : Core911D4) (hL4 : Core911L4)
    (hU4 : Core911U4) (hL5 : Core911L5) (hU5 : Core911U5) (hRee : Core911Ree)
    (Y : Type) [Group Y] [Finite Y] (hs : IsSimpleGroup Y) (hna : ∃ a b : Y, a * b ≠ b * a)
    (hGH : GHList Y) (hL34 : ¬ LieModel Y .PSL 3 2 2) : No911 Y := by
  rcases ghList_cases hGH with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact hAlt Y hs hna h
  · exact hSpor Y hs hna h
  · exact hMcLy Y hs hna h
  · rcases h with h | h | h | h | h
    · exact hTwo Y hs hna (Or.inl h)
    · exact hTwo Y hs hna (Or.inr (Or.inl h))
    · exact absurd h hL34
    · exact hTwo Y hs hna (Or.inr (Or.inr (Or.inl h)))
    · exact hTwo Y hs hna (Or.inr (Or.inr (Or.inr h)))
  · exact hL2 Y hs hna h
  · exact hL3 Y hs hna h
  · exact hU3 Y hs hna h
  · exact hSp4 Y hs hna h
  · exact hG2 Y hs hna h
  · exact hD4 Y hs hna h
  · exact hL4 Y hs hna h
  · exact hU4 Y hs hna h
  · exact hL5 Y hs hna h
  · exact hU5 Y hs hna h
  · exact hRee Y hs hna h

end CFSG.GH74.GLS.Stage2.Bender.Thm2.P911
