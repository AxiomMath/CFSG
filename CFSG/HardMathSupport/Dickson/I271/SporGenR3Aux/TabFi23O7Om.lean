module

public import CFSG.RankThree.PartOne.N143.O7
import CFSG.ClassicalInvolution.Orders.Orthogonal

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.RankThree.PartOne.N143.O7 (Om modelEquiv)

private theorem card_zmod_three : Nat.card (ZMod 3) = 3 := by
  rw [Nat.card_eq_fintype_card, ZMod.card]

theorem tabFi23_card_om : Nat.card ↥Om = 4585351680 := by
  have h := CFSG.ClassicalInvolution.card_statedProj_statedOmega_quadOdd_eq_ordBC (K := ZMod 3)
    (p := 3) (f := 1) Nat.prime_three (by norm_num) (by rw [card_zmod_three]; norm_num)
    (n := 3) le_rfl
  rw [Nat.card_congr (modelEquiv card_zmod_three).toEquiv, pow_one] at h
  rw [h]
  decide

theorem tabFi23_isSimpleGroup_om : IsSimpleGroup ↥Om := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadOdd
    (K := ZMod 3) (n := 3) 3 (by norm_num) le_rfl
  exact (modelEquiv card_zmod_three).symm.isSimpleGroup

theorem tabFi23_nonabelian_om : ∃ a b : ↥Om, a * b ≠ b * a := by
  by_contra hc
  push Not at hc
  haveI := tabFi23_isSimpleGroup_om
  letI : CommGroup ↥Om := { (inferInstance : Group ↥Om) with mul_comm := hc }
  have hp := IsSimpleGroup.prime_card (α := ↥Om)
  rw [tabFi23_card_om] at hp
  norm_num at hp

theorem tabFi23_center_om : Subgroup.center ↥Om = ⊥ := by
  haveI := tabFi23_isSimpleGroup_om
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥Om) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := tabFi23_nonabelian_om
    have ha : a ∈ Subgroup.center ↥Om := by rw [h]; trivial
    exact hab (Subgroup.mem_center_iff.1 ha b).symm

theorem tabFi23_isSimpleGroup_of_equiv_om {T : Type*} [Group T] (e : T ≃* ↥Om) :
    IsSimpleGroup T := by
  haveI := tabFi23_isSimpleGroup_om
  exact e.isSimpleGroup

theorem tabFi23_nonabelian_of_equiv_om {T : Type*} [Group T] (e : T ≃* ↥Om) :
    ∃ a b : T, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := tabFi23_nonabelian_om
  refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
  have := congrArg e h
  simpa using this

theorem tabFi23_card_of_equiv_om {T : Type*} [Group T] (e : T ≃* ↥Om) :
    Nat.card T = 4585351680 := by
  rw [Nat.card_congr e.toEquiv, tabFi23_card_om]

end CFSG.HardMathSupport.Dickson.I271
