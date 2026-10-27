module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup

theorem card_centralizer_dvd_two_mul_card_centralizer {α : Type*} [Fintype α] [DecidableEq α]
    [Nontrivial α] (σ : alternatingGroup α) :
    Nat.card (centralizer ({(σ : Perm α)} : Set (Perm α))) ∣
      2 * Nat.card (centralizer ({σ} : Set (alternatingGroup α))) := by
  set C := centralizer ({(σ : Perm α)} : Set (Perm α)) with hCdef
  have hmap : (centralizer ({σ} : Set (alternatingGroup α))).map (alternatingGroup α).subtype =
      alternatingGroup α ⊓ C := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hy
      refine Subgroup.mem_inf.mpr ⟨y.2, ?_⟩
      show (y : Perm α) ∈ C
      rw [hCdef, mem_centralizer_singleton_iff]
      exact congrArg Subtype.val hy
    · intro hx
      obtain ⟨hxA, hxC⟩ := Subgroup.mem_inf.mp hx
      refine ⟨⟨x, hxA⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      rw [hCdef, mem_centralizer_singleton_iff] at hxC
      exact Subtype.ext hxC
  have hcard : Nat.card (centralizer ({σ} : Set (alternatingGroup α))) =
      Nat.card (alternatingGroup α ⊓ C : Subgroup (Perm α)) := by
    rw [← hmap, Subgroup.card_map_of_injective (alternatingGroup α).subtype_injective]
  have hrel := (alternatingGroup α).relIndex_mul_card C
  have hdvd : (alternatingGroup α).relIndex C ∣ 2 := by
    have h := (alternatingGroup α).relIndex_dvd_index_of_normal C
    rwa [alternatingGroup.index_eq_two] at h
  rw [hcard, ← hrel]
  exact Nat.mul_dvd_mul_right hdvd _

end CFSG.ComponentClassification.RankTwoAlt
