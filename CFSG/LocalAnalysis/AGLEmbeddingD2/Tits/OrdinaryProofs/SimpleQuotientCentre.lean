module

public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.Tactic.Group

public section

namespace CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs

variable {G : Type*} [Group G]

theorem center_quotient_eq_bot_of_simple {L D : Subgroup G} [(D.subgroupOf L).Normal]
    [IsSimpleGroup (L ⧸ D.subgroupOf L)] (hnab : ¬ IsMulCommutative (L ⧸ D.subgroupOf L))
    (x : L) (hx : ∀ l : L, x * l * x⁻¹ * l⁻¹ ∈ D.subgroupOf L) : x ∈ D.subgroupOf L := by
  have hcen : Subgroup.center (L ⧸ D.subgroupOf L) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (L ⧸ D.subgroupOf L)) with
      h | h
    · exact h
    · exact absurd (Subgroup.center_eq_top_iff.mp h) hnab
  have hmem : (QuotientGroup.mk x : L ⧸ D.subgroupOf L) ∈ Subgroup.center (L ⧸ D.subgroupOf L) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective g
    have key : x * l = (x * l * x⁻¹ * l⁻¹) * (l * x) := by group
    have h1 : (QuotientGroup.mk (x * l) : L ⧸ D.subgroupOf L)
        = QuotientGroup.mk ((x * l * x⁻¹ * l⁻¹) * (l * x)) := congrArg _ key
    have hc : (QuotientGroup.mk (x * l * x⁻¹ * l⁻¹ : L) : L ⧸ D.subgroupOf L) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (hx l)
    rw [QuotientGroup.mk_mul (N := D.subgroupOf L) (x * l * x⁻¹ * l⁻¹ : L), hc, one_mul] at h1
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact h1.symm
  rw [hcen, Subgroup.mem_bot] at hmem
  exact (QuotientGroup.eq_one_iff x).mp hmem

end CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs
