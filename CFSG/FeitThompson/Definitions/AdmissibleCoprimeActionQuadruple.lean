module

public import Mathlib.GroupTheory.SpecificGroups.ZGroup

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Pointwise

structure IsAdmissibleCoprimeActionQuadruple (Y : Type*) [Group Y] (J A A0 : Subgroup Y) :
    Prop where
  isSolvable : Group.IsSolvable Y
  odd_card : Odd (Nat.card Y)
  normal : J.Normal
  sup_eq_top : J ⊔ A = ⊤
  inf_eq_bot : J ⊓ A = ⊥
  coprime : (Nat.card J).Coprime (Nat.card A)
  le : A0 ≤ A
  prime_card : (Nat.card A0).Prime
  isZGroup_centralizer : IsZGroup (Subgroup.centralizer (A0 : Set Y) ⊓ J : Subgroup Y)

namespace IsAdmissibleCoprimeActionQuadruple

variable {Y : Type*} [Group Y] {J A A0 : Subgroup Y}
  (h : IsAdmissibleCoprimeActionQuadruple Y J A A0)

include h

theorem finite : Finite Y :=
  Nat.finite_of_card_ne_zero fun h0 => by simpa [h0, Nat.odd_iff] using h.odd_card

theorem coe_mul_coe : (J : Set Y) * (A : Set Y) = Set.univ := by
  have := h.normal
  rw [← Subgroup.normal_mul J A, h.sup_eq_top, Subgroup.coe_top]

theorem disjoint : Disjoint J A :=
  disjoint_iff.mpr h.inf_eq_bot

theorem isComplement' : J.IsComplement' A :=
  Subgroup.isComplement'_of_disjoint_and_mul_eq_univ h.disjoint h.coe_mul_coe

theorem card_mul_card : Nat.card J * Nat.card A = Nat.card Y :=
  h.isComplement'.card_mul_card

theorem odd_card_subgroup (H : Subgroup Y) : Odd (Nat.card H) :=
  h.odd_card.of_dvd_nat H.card_subgroup_dvd_card

theorem isCyclic : IsCyclic A0 :=
  have : Fact (Nat.card A0).Prime := ⟨h.prime_card⟩
  isCyclic_of_prime_card rfl

theorem odd_prime_card : Odd (Nat.card A0) :=
  h.odd_card_subgroup A0

theorem le_centralizer : A0 ≤ Subgroup.centralizer (A0 : Set Y) := by
  rw [Subgroup.le_centralizer_iff_isMulCommutative]
  exact ⟨⟨h.isCyclic.commGroup.mul_comm⟩⟩

theorem isCyclic_sylow_centralizer {p : ℕ} (hp : p.Prime)
    (P : Sylow p (Subgroup.centralizer (A0 : Set Y) ⊓ J : Subgroup Y)) : IsCyclic P :=
  have := h.isZGroup_centralizer
  IsZGroup.isZGroup p hp P

omit h in
theorem mem_centralizer_inf_iff {y : Y} :
    y ∈ (Subgroup.centralizer (A0 : Set Y) ⊓ J : Subgroup Y) ↔
      (∀ a ∈ A0, a * y = y * a) ∧ y ∈ J := by
  simp [Subgroup.mem_centralizer_iff]

end IsAdmissibleCoprimeActionQuadruple

end CFSG.FeitThompson
