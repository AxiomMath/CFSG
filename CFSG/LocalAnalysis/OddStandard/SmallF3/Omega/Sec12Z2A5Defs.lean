module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Inputs
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Z2A5Hyp (Y : Type) [Group Y] (τ : Y) : Prop :=
  orderOf τ = 2 ∧
    Nonempty (↥(centralizer ({τ} : Set Y)) ≃*
      (Multiplicative (ZMod 2) × ↥(alternatingGroup (Fin 5)))) ∧
    ∀ y : Y, (y ∈ conjClassIn ⊤ τ ∧ y ∈ centralizer ({τ} : Set Y)) ↔
      (∃ x ∈ oTwoRes (centralizer ({τ} : Set Y)), y = τ * x ∧ y * y = 1)

@[expose] def BenderL34Socle (Q : Type) [Group Q] : Prop :=
  ∃ E : Subgroup Q, E.Normal ∧ IsSimpleGroup ↥E ∧ centralizer (E : Set Q) = ⊥ ∧
    derivedSeries Q 2 ≤ E ∧
    (LieModel ↥E .PSL 2 2 4 ∨ LieModel ↥E .PSU 3 2 2 ∨ LieModel ↥E .PSL 3 2 2)

@[expose] def Asc82Z2A5K : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (τ : Y), CFSG.SectionRank.IsKGroupCat Y → Z2A5Hyp Y τ →
    IsO4Plus4 (Y ⧸ oddCore Y) ∨ BenderL34Socle (Y ⧸ oddCore Y)

theorem benderL34_perfect_eq {Q : Type} [Group Q] {E P : Subgroup Q} [E.Normal] [P.Normal]
    (hEs : IsSimpleGroup ↥E) (hd : derivedSeries Q 2 ≤ E) (hP : ⁅P, P⁆ = P) (hP1 : P ≠ ⊥) :
    P = E := by
  have hle : ∀ n, P ≤ derivedSeries Q n := by
    intro n
    induction n with
    | zero => exact le_top
    | succ n ih =>
      rw [derivedSeries_succ, ← hP]
      exact Subgroup.commutator_mono ih ih
  have hPE : P ≤ E := (hle 2).trans hd
  have hn : (P.subgroupOf E).Normal := Subgroup.normal_subgroupOf
  rcases hn.eq_bot_or_eq_top with hb | ht
  · exact absurd ((Subgroup.subgroupOf_eq_bot).1 hb |> fun h => disjoint_self.1
      (h.mono_right hPE)) hP1
  · exact le_antisymm hPE (Subgroup.subgroupOf_eq_top.1 ht)

end CFSG.OddStandard.SmallF3.Omega
