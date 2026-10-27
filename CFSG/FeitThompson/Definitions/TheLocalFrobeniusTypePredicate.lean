module

public import CFSG.FeitThompson.Local.HallCoreLargestNilpotentNormalHall
public import Mathlib.GroupTheory.SemidirectProduct

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {X : Type*} [Group X] [Finite X] {E : Subgroup X}

structure IsFrobeniusType (X : Type*) [Group X] [Finite X] (E : Subgroup X) : Prop where
  bot_lt_hallCore : ⊥ < hallCore X
  hallCore_lt_top : hallCore X < ⊤
  isComplement' : (hallCore X).IsComplement' E
  exists_abelian_normal : ∃ E₁ ≤ E, (E₁.subgroupOf E).Normal ∧ IsMulCommutative E₁ ∧
    ∀ h ∈ hallCore X, h ≠ 1 → E ⊓ centralizer {h} ≤ E₁
  exists_exponent_eq : ∃ E₀ ≤ E, Monoid.exponent E₀ = Monoid.exponent E ∧
    ∀ e ∈ E₀, e ≠ 1 → hallCore X ⊓ centralizer {e} = ⊥

namespace IsFrobeniusType

theorem hallCore_ne_bot (h : IsFrobeniusType X E) : hallCore X ≠ ⊥ := h.bot_lt_hallCore.ne'

theorem hallCore_ne_top (h : IsFrobeniusType X E) : hallCore X ≠ ⊤ := h.hallCore_lt_top.ne

theorem nontrivial_hallCore (h : IsFrobeniusType X E) : Nontrivial (hallCore X) :=
  (hallCore X).nontrivial_iff_ne_bot.mpr h.hallCore_ne_bot

theorem isCompl (h : IsFrobeniusType X E) : IsCompl (hallCore X) E := h.isComplement'.isCompl

theorem disjoint (h : IsFrobeniusType X E) : Disjoint (hallCore X) E := h.isCompl.disjoint

theorem inf_eq_bot (h : IsFrobeniusType X E) : hallCore X ⊓ E = ⊥ := h.disjoint.eq_bot

theorem sup_eq_top (h : IsFrobeniusType X E) : hallCore X ⊔ E = ⊤ := h.isCompl.sup_eq_top

theorem ne_bot (h : IsFrobeniusType X E) : E ≠ ⊥ := fun hE =>
  h.hallCore_ne_top (Subgroup.isComplement'_bot_right.mp (hE ▸ h.isComplement'))

theorem ne_top (h : IsFrobeniusType X E) : E ≠ ⊤ := fun hE =>
  h.hallCore_ne_bot (Subgroup.isComplement'_top_right.mp (hE ▸ h.isComplement'))

noncomputable def mulEquivSemidirectProduct (h : IsFrobeniusType X E) :
    (hallCore X) ⋊[((hallCore X).normalizerMonoidHom).comp
      (Subgroup.inclusion ((hallCore X).normalizer_eq_top ▸ le_top))] E ≃* X :=
  SemidirectProduct.mulEquivSubgroup h.isComplement'

@[simp]
theorem coe_mulEquivSemidirectProduct (h : IsFrobeniusType X E)
    (x : (hallCore X) ⋊[((hallCore X).normalizerMonoidHom).comp
      (Subgroup.inclusion ((hallCore X).normalizer_eq_top ▸ le_top))] E) :
    h.mulEquivSemidirectProduct x = (x.left : X) * (x.right : X) :=
  SemidirectProduct.mulEquivSubgroup_apply h.isComplement' x

theorem index_hallCore_eq_card (h : IsFrobeniusType X E) : (hallCore X).index = Nat.card E :=
  h.isComplement'.symm.index_eq_card

theorem card_hallCore_mul_card (h : IsFrobeniusType X E) :
    Nat.card (hallCore X) * Nat.card E = Nat.card X := by
  rw [← h.index_hallCore_eq_card, Subgroup.card_mul_index]

theorem coprime_card (h : IsFrobeniusType X E) :
    Nat.Coprime (Nat.card (hallCore X)) (Nat.card E) :=
  h.index_hallCore_eq_card ▸ coprime_natCard_index_hallCore

theorem exists_abelian_le_normalizer (h : IsFrobeniusType X E) :
    ∃ E₁ ≤ E, E ≤ normalizer E₁ ∧ IsMulCommutative E₁ ∧
      ∀ g ∈ hallCore X, g ≠ 1 → E ⊓ centralizer {g} ≤ E₁ := by
  obtain ⟨E₁, hle, hnorm, hcomm, hcent⟩ := h.exists_abelian_normal
  exact ⟨E₁, hle, Subgroup.le_normalizer_of_normal_subgroupOf hle, hcomm, hcent⟩

theorem exists_abelian_centralizer_le (h : IsFrobeniusType X E) {g : X} (hg : g ∈ hallCore X)
    (hg1 : g ≠ 1) : ∃ E₁ ≤ E, IsMulCommutative E₁ ∧ E ⊓ centralizer {g} ≤ E₁ := by
  obtain ⟨E₁, hle, -, hcomm, hcent⟩ := h.exists_abelian_normal
  exact ⟨E₁, hle, hcomm, hcent g hg hg1⟩

theorem exists_ne_one_inf_centralizer_eq_bot (h : IsFrobeniusType X E) :
    ∃ e ∈ E, e ≠ 1 ∧ hallCore X ⊓ centralizer {e} = ⊥ := by
  obtain ⟨E₀, hE₀E, hexp, hcent⟩ := h.exists_exponent_eq
  have hne : E₀ ≠ ⊥ := by
    rintro rfl
    rw [Monoid.exp_eq_one_of_subsingleton] at hexp
    have : Subsingleton E := Monoid.exp_eq_one_iff.mp hexp.symm
    exact h.ne_bot (Subgroup.eq_bot_of_subsingleton E)
  obtain ⟨e, he⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have he1 : (e : X) ≠ 1 := fun hc => he (Subtype.ext hc)
  exact ⟨e, hE₀E e.2, he1, hcent e e.2 he1⟩

end IsFrobeniusType

end

end CFSG.FeitThompson
