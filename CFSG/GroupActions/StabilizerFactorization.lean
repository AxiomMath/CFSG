module

public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.QuotientGroup.Defs

public section

namespace CFSG.GroupActions

theorem exists_mul_stabilizer_eq
    {G Ω : Type*} [Group G] [MulAction G Ω]
    (N : Subgroup G) [MulAction.IsPretransitive N Ω] (ω : Ω) (g : G) :
    ∃ (n : N) (h : MulAction.stabilizer G ω), (n : G) * (h : G) = g := by
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq N ω (g • ω)
  refine ⟨n, ⟨(n : G)⁻¹ * g, ?_⟩, by simp⟩
  rw [MulAction.mem_stabilizer_iff, mul_smul]
  have hn' : (n : G) • ω = g • ω := hn
  rw [← hn', inv_smul_smul]

theorem stabilizer_quotient_surjective
    {G Ω : Type*} [Group G] [MulAction G Ω]
    (N : Subgroup G) [N.Normal] [MulAction.IsPretransitive N Ω] (ω : Ω) :
    Function.Surjective
      ((QuotientGroup.mk' N).comp (MulAction.stabilizer G ω).subtype) := by
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨n, h, hnh⟩ := exists_mul_stabilizer_eq N ω g
  refine ⟨h, ?_⟩
  change (h : G ⧸ N) = (g : G ⧸ N)
  rw [← hnh, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr n.property,
    one_mul]

theorem quotient_card_dvd_stabilizer_card
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω]
    (N : Subgroup G) [N.Normal] [MulAction.IsPretransitive N Ω] (ω : Ω) :
    Nat.card (G ⧸ N) ∣ Nat.card (MulAction.stabilizer G ω) :=
  Subgroup.card_dvd_of_surjective (stabilizer_quotient_surjective N ω)

end CFSG.GroupActions
