module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Facts
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.MulAutSimple
public import CFSG.Adapters.StatedClassicalUnitaryOrders

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open CFSG.Open

theorem isSimpleGroup_of_statedPSU42 {U : Type} [Group U]
    (h : StatedClassicalModel U .PSU 4 2 1) : IsSimpleGroup U :=
  (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity U 4 2 1 h).2

theorem card_of_statedPSU42 {U : Type} [Group U] (h : StatedClassicalModel U .PSU 4 2 1) :
    Nat.card U = 25920 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_four_two h

theorem exists_mul_ne_of_statedPSU42 {U : Type} [Group U]
    (h : StatedClassicalModel U .PSU 4 2 1) : ∃ a b : U, a * b ≠ b * a := by
  by_contra hcomm
  push Not at hcomm
  haveI := isSimpleGroup_of_statedPSU42 h
  haveI : IsMulCommutative U := ⟨⟨hcomm⟩⟩
  have hprime := (Group.is_simple_iff_prime_card (α := U)).1 inferInstance
  rw [card_of_statedPSU42 h] at hprime
  exact absurd hprime (by norm_num)

theorem not_isSolvable_of_statedPSU42 {X : Type} [Group X]
    (h : StatedClassicalModel X .PSU 4 2 1) : ¬ Group.IsSolvable X := by
  intro hsolv
  haveI := isSimpleGroup_of_statedPSU42 h
  obtain ⟨a, b, hab⟩ := exists_mul_ne_of_statedPSU42 h
  exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hsolv a b)

theorem IsU42Two.exists_simple {A : Type} [Group A] (h : IsU42Two A) :
    ∃ (U : Type) (_ : Group U), StatedClassicalModel U .PSU 4 2 1 ∧ IsSimpleGroup U ∧
      (∃ a b : U, a * b ≠ b * a) ∧ Nonempty (A ≃* MulAut U) := by
  obtain ⟨U, _, hU, e⟩ := h
  exact ⟨U, inferInstance, hU, isSimpleGroup_of_statedPSU42 hU,
    exists_mul_ne_of_statedPSU42 hU, e⟩

theorem IsU42Two.not_isSolvable {A : Type} [Group A] (h : IsU42Two A) :
    ¬ Group.IsSolvable A := by
  obtain ⟨U, _, hU, hs, hna, ⟨e⟩⟩ := h.exists_simple
  intro hsolv
  haveI := hs
  exact MulAutSimple.not_isSolvable hna
    (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
