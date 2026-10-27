module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutSetupL1
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.EvenSporadicStandard.M23Std

variable {G : Type} [Group G] {L : Subgroup G} {z : G} {F L1 N : Subgroup G}

namespace OutSetup

variable (S : OutSetup L z F L1 N)

include S

theorem L1_le_of_isSylowOf [Finite G] {P : Subgroup G}
    (hP : IsSylowOf 2 P (normalizer (L1 : Set G))) : L1 ≤ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hP.exists_sylow_eq_subgroupOf
  have hnormal : (L1.subgroupOf (normalizer (L1 : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).2 le_rfl
  have hpg : IsPGroup 2 (L1.subgroupOf (normalizer (L1 : Set G))) := S.isPGroup_L1.comap_subtype
  have hle := IsPGroup.le_sylow_of_normal (N := L1.subgroupOf (normalizer (L1 : Set G))) hpg Q
  intro l hl
  have h1 : (⟨l, Subgroup.le_normalizer hl⟩ : ↥(normalizer (L1 : Set G))) ∈
      L1.subgroupOf (normalizer (L1 : Set G)) := hl
  have h2 := hle h1
  rw [hQ] at h2
  exact h2

end OutSetup

end CFSG.EvenSporadicStandard.M22Std
