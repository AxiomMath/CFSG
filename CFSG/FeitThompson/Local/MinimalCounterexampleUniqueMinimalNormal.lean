module

public import CFSG.FeitThompson.Definitions.AdmissibleCoprimeActionQuadruple
public import CFSG.FeitThompson.Definitions.ConventionForPLengthAtMostOne
public import CFSG.FeitThompson.Definitions.RawFittingSubgroupConstruction
import CFSG.FeitThompson.Foundations.NormalContainsMinimalNormal
import CFSG.FeitThompson.Foundations.MinimalNormalSolvableElemAbelian
import CFSG.FeitThompson.Local.PLengthOneDisjointKernelQuotients
import CFSG.FeitThompson.Local.MinimalPrimeCentralizerCounterexample
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

universe u

variable {G : Type u} [Group G]

section Minimality

variable {H L : Subgroup G}

theorem normal_of_minimal_normal_le
    (hL : Minimal (fun K : Subgroup G => K.Normal ∧ K ≠ ⊥ ∧ K ≤ H) L) : L.Normal := hL.prop.1

theorem ne_bot_of_minimal_normal_le
    (hL : Minimal (fun K : Subgroup G => K.Normal ∧ K ≠ ⊥ ∧ K ≤ H) L) : L ≠ ⊥ := hL.prop.2.1

theorem le_of_minimal_normal_le
    (hL : Minimal (fun K : Subgroup G => K.Normal ∧ K ≠ ⊥ ∧ K ≤ H) L) : L ≤ H := hL.prop.2.2

theorem forall_normal_lt_eq_bot_of_minimal_normal_le
    (hL : Minimal (fun K : Subgroup G => K.Normal ∧ K ≠ ⊥ ∧ K ≤ H) L) :
    ∀ K : Subgroup G, K.Normal → K < L → K = ⊥ := fun K hKn hKL => by
  by_contra hKb
  exact hKL.ne ((minimal_iff.1 hL).2 ⟨hKn, hKb, hKL.le.trans (le_of_minimal_normal_le hL)⟩
    hKL.le).symm

theorem minimal_normal_le_of_le {H' : Subgroup G}
    (hL : Minimal (fun K : Subgroup G => K.Normal ∧ K ≠ ⊥ ∧ K ≤ H) L) (h : H ≤ H') :
    Minimal (fun K : Subgroup G => K.Normal ∧ K ≠ ⊥ ∧ K ≤ H') L :=
  minimal_iff.2
    ⟨⟨normal_of_minimal_normal_le hL, ne_bot_of_minimal_normal_le hL,
      (le_of_minimal_normal_le hL).trans h⟩,
     fun _ hK hKL => (minimal_iff.1 hL).2
       ⟨hK.1, hK.2.1, hKL.trans (le_of_minimal_normal_le hL)⟩ hKL⟩

theorem inf_eq_bot_of_minimal_normal_le_of_ne {L₁ L₂ : Subgroup G}
    (h₁ : Minimal (fun K : Subgroup G => K.Normal ∧ K ≠ ⊥ ∧ K ≤ H) L₁)
    (h₂ : Minimal (fun K : Subgroup G => K.Normal ∧ K ≠ ⊥ ∧ K ≤ H) L₂) (hne : L₁ ≠ L₂) :
    L₁ ⊓ L₂ = ⊥ := by
  by_contra hb
  have _i1 := normal_of_minimal_normal_le h₁
  have _i2 := normal_of_minimal_normal_le h₂
  have hP : (L₁ ⊓ L₂).Normal ∧ L₁ ⊓ L₂ ≠ ⊥ ∧ L₁ ⊓ L₂ ≤ H :=
    ⟨inferInstance, hb, inf_le_left.trans (le_of_minimal_normal_le h₁)⟩
  exact hne (((minimal_iff.1 h₁).2 hP inf_le_left).trans
    ((minimal_iff.1 h₂).2 hP inf_le_right).symm)

theorem le_map_subtype_fittingRaw_of_minimal_normal_le [Finite G] [Group.IsSolvable G]
    (hL : Minimal (fun K : Subgroup G => K.Normal ∧ K ≠ ⊥ ∧ K ≤ H) L) :
    L ≤ (fittingRaw ↥H).map H.subtype := by
  have _i1 := normal_of_minimal_normal_le hL
  obtain ⟨q, d, hq, -, hcard⟩ :=
    exists_prime_card_eq_pow_of_isSolvable_of_forall_normal_lt_eq_bot
      (ne_bot_of_minimal_normal_le hL) (forall_normal_lt_eq_bot_of_minimal_normal_le hL)
  have hpp : IsPrimePowerOrder (L.subgroupOf H) :=
    isPrimePowerOrder_iff.2
      ⟨q, hq, d, by rw [natCard_subgroupOf_of_le (le_of_minimal_normal_le hL), hcard]⟩
  calc L = L ⊓ H := (inf_eq_left.2 (le_of_minimal_normal_le hL)).symm
    _ = (L.subgroupOf H).map H.subtype := (Subgroup.subgroupOf_map_subtype L H).symm
    _ ≤ (fittingRaw ↥H).map H.subtype :=
        Subgroup.map_mono (le_fittingRaw (_i1.subgroupOf H) hpp)

end Minimality

section Main

variable {p : ℕ} [Fact p.Prime] [Finite G] {H R R0 : Subgroup G}
  (hadm : IsAdmissibleCoprimeActionQuadruple G H R R0)
  (hnot : ¬ HasPLengthLeOne p ↥⁅H, R⁆)
  (hmin : ∀ (Y : Type u) [Group Y] [Finite Y] (J A A0 : Subgroup Y),
    IsAdmissibleCoprimeActionQuadruple Y J A A0 → Nat.card Y < Nat.card G →
    HasPLengthLeOne p ↥⁅J, A⁆)

include hadm hnot hmin

theorem eq_of_minimal_normal_le_of_minimal {L₁ L₂ : Subgroup G}
    (h₁ : Minimal (fun K : Subgroup G => K.Normal ∧ K ≠ ⊥ ∧ K ≤ H) L₁)
    (h₂ : Minimal (fun K : Subgroup G => K.Normal ∧ K ≠ ⊥ ∧ K ≤ H) L₂) : L₁ = L₂ := by
  by_contra hne
  have hinf := inf_eq_bot_of_minimal_normal_le_of_ne h₁ h₂ hne
  have _i1 := normal_of_minimal_normal_le h₁
  have _i2 := normal_of_minimal_normal_le h₂
  have _i3 := _i1.subgroupOf H
  have _i4 := _i2.subgroupOf H
  refine not_hasPLengthLeOne_of_minimal hadm hnot hmin
    (hasPLengthLeOne_of_inf_eq_bot (D₁ := L₁.subgroupOf H) (D₂ := L₂.subgroupOf H) ?_
      (hasPLengthLeOne_quotient_of_minimal hadm hnot hmin (ne_bot_of_minimal_normal_le h₁)
        (le_of_minimal_normal_le h₁))
      (hasPLengthLeOne_quotient_of_minimal hadm hnot hmin (ne_bot_of_minimal_normal_le h₂)
        (le_of_minimal_normal_le h₂)))
  rw [show L₁.subgroupOf H ⊓ L₂.subgroupOf H = (L₁ ⊓ L₂).subgroupOf H from
    (Subgroup.comap_inf _ _ _).symm, hinf, Subgroup.bot_subgroupOf]

theorem existsUnique_minimal_normal_le_of_minimal :
    ∃! L : Subgroup G, Minimal (fun K : Subgroup G => K.Normal ∧ K ≠ ⊥ ∧ K ≤ H) L := by
  obtain ⟨L, hL⟩ :=
    exists_minimal_normal_ne_bot_le hadm.normal (ne_bot_of_minimal hadm hnot hmin)
  exact ⟨L, hL, fun _ hL' => eq_of_minimal_normal_le_of_minimal hadm hnot hmin hL' hL⟩

omit [Fact p.Prime] hnot hmin in
theorem le_map_subtype_fittingRaw_of_minimal_normal {L : Subgroup G}
    (hL : Minimal (fun K : Subgroup G => K.Normal ∧ K ≠ ⊥ ∧ K ≤ H) L) :
    L ≤ (fittingRaw ↥H).map H.subtype :=
  have : Group.IsSolvable G := hadm.isSolvable
  le_map_subtype_fittingRaw_of_minimal_normal_le hL

theorem eq_bot_or_eq_bot_of_inf_eq_bot_of_minimal {V₁ V₂ : Subgroup G} [V₁.Normal] [V₂.Normal]
    (h₁ : V₁ ≤ H) (h₂ : V₂ ≤ H) (hinf : V₁ ⊓ V₂ = ⊥) : V₁ = ⊥ ∨ V₂ = ⊥ := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨L₁, hL₁⟩ := exists_minimal_normal_ne_bot_le (N := V₁) inferInstance hcon.1
  obtain ⟨L₂, hL₂⟩ := exists_minimal_normal_ne_bot_le (N := V₂) inferInstance hcon.2
  have heq := eq_of_minimal_normal_le_of_minimal hadm hnot hmin
    (minimal_normal_le_of_le hL₁ h₁) (minimal_normal_le_of_le hL₂ h₂)
  refine ne_bot_of_minimal_normal_le hL₁ (le_bot_iff.1 ?_)
  rw [← hinf]
  exact le_inf (le_of_minimal_normal_le hL₁) (heq ▸ le_of_minimal_normal_le hL₂)

theorem eq_bot_or_eq_bot_of_sup_eq_fittingRaw_of_minimal {V₁ V₂ : Subgroup G} [V₁.Normal] [V₂.Normal]
    (h₁ : V₁ ≤ (fittingRaw ↥H).map H.subtype) (h₂ : V₂ ≤ (fittingRaw ↥H).map H.subtype)
    (_hsup : V₁ ⊔ V₂ = (fittingRaw ↥H).map H.subtype) (hinf : V₁ ⊓ V₂ = ⊥)
    (_hcomm : ⁅V₁, V₂⁆ = ⊥) : V₁ = ⊥ ∨ V₂ = ⊥ :=
  eq_bot_or_eq_bot_of_inf_eq_bot_of_minimal hadm hnot hmin
    (h₁.trans (Subgroup.map_subtype_le _)) (h₂.trans (Subgroup.map_subtype_le _)) hinf

theorem uniqueMinimalNormalPrimeCentralizerCounterexample :
    (∃! L : Subgroup G, Minimal (fun K : Subgroup G => K.Normal ∧ K ≠ ⊥ ∧ K ≤ H) L) ∧
      (∀ L : Subgroup G, Minimal (fun K : Subgroup G => K.Normal ∧ K ≠ ⊥ ∧ K ≤ H) L →
        L ≤ (fittingRaw ↥H).map H.subtype) ∧
      ∀ (V₁ V₂ : Subgroup G) (_ : V₁.Normal) (_ : V₂.Normal),
        V₁ ≤ (fittingRaw ↥H).map H.subtype → V₂ ≤ (fittingRaw ↥H).map H.subtype →
        V₁ ⊔ V₂ = (fittingRaw ↥H).map H.subtype → V₁ ⊓ V₂ = ⊥ → ⁅V₁, V₂⁆ = ⊥ →
        V₁ = ⊥ ∨ V₂ = ⊥ :=
  ⟨existsUnique_minimal_normal_le_of_minimal hadm hnot hmin,
    fun _ hL => le_map_subtype_fittingRaw_of_minimal_normal hadm hL,
    fun _ _ _ _ h₁ h₂ hsup hinf hcomm =>
      eq_bot_or_eq_bot_of_sup_eq_fittingRaw_of_minimal hadm hnot hmin h₁ h₂ hsup hinf hcomm⟩

end Main

end

end CFSG.FeitThompson

