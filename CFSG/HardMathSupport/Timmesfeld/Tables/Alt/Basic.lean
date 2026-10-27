module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.Alt

open Equiv

theorem five_le_of_centerQuotient {L : Type*} [Group L] (hperf : commutator L = ⊤)
    [IsSimpleGroup (L ⧸ Subgroup.center L)] {n : ℕ}
    (e : (L ⧸ Subgroup.center L) ≃* alternatingGroup (Fin n)) : 5 ≤ n := by
  by_contra hn
  push Not at hn
  have hA : Group.IsSolvable (alternatingGroup (Fin n)) :=
    alternatingGroup.isSolvable (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  have hQ : Group.IsSolvable (L ⧸ Subgroup.center L) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  have hZ : Group.IsSolvable (Subgroup.center L) := inferInstance
  have hL : Group.IsSolvable L := by
    refine Group.isSolvable_of_ker_le_range (Subgroup.center L).subtype
      (QuotientGroup.mk' (Subgroup.center L)) ?_
    rw [QuotientGroup.ker_mk', Subgroup.range_subtype]
  have hnt : Nontrivial L := by
    obtain ⟨a, b, hab⟩ := exists_pair_ne (L ⧸ Subgroup.center L)
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨x, y, fun h => hab (by rw [h])⟩
  have := Group.IsSolvable.commutator_lt_top_of_nontrivial L
  rw [hperf] at this
  exact lt_irrefl _ this

end CFSG.HardMathSupport.Timmesfeld.Tables.Alt
