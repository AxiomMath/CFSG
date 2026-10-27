module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.NormalPGroupFixed
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ThompsonAmbient

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

open scoped commutatorElement

theorem zj_fixed_subgroup_exists {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (sylow : Sylow prime G)
    (kernel : Subgroup G) [kernel.Normal] (hproper : kernel < thompsonCenterOf (sylow : Subgroup G)) :
    ∃ fixed : Subgroup G, kernel < fixed ∧ fixed ≤ thompsonCenterOf (sylow : Subgroup G) ∧
      (sylow : Subgroup G) ≤ Subgroup.normalizer (fixed : Set G) ∧ IsMulCommutative fixed ∧
        ⁅fixed, (sylow : Subgroup G)⁆ ≤ kernel := by
  let overgroup := (sylow : Subgroup G)
  let normal := thompsonCenterOf overgroup
  have hnormalLe : normal ≤ overgroup := thompsonCenterOf_le overgroup
  have hnormalizes : overgroup ≤ Subgroup.normalizer (normal : Set G) :=
    Subgroup.le_normalizer.trans (thompsonCenterOf_normalized overgroup)
  have : (normal.subgroupOf overgroup).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hnormalLe).mpr hnormalizes
  have : (kernel.subgroupOf overgroup).Normal := inferInstance
  let fixed := normalFixedModulo (normal.subgroupOf overgroup) (kernel.subgroupOf overgroup)
  have hrestrictedProper : kernel.subgroupOf overgroup < normal.subgroupOf overgroup := by
    apply (Subgroup.map_lt_map_iff_of_injective overgroup.subtype_injective).mp
    rw [Subgroup.map_subgroupOf_eq_of_le (hproper.le.trans hnormalLe), Subgroup.map_subgroupOf_eq_of_le hnormalLe]
    exact hproper
  have hstrict := normalFixedModulo_strict prime hprime sylow.isPGroup'
    (normal.subgroupOf overgroup) (kernel.subgroupOf overgroup) hrestrictedProper
  have hambientStrict : kernel < fixed.map overgroup.subtype := by
    have hmapped := (Subgroup.map_lt_map_iff_of_injective overgroup.subtype_injective).mpr hstrict
    rwa [Subgroup.map_subgroupOf_eq_of_le (hproper.le.trans hnormalLe)] at hmapped
  have hfixedLe : fixed.map overgroup.subtype ≤ normal := by
    have hmapped := Subgroup.map_mono (f := overgroup.subtype)
      (show fixed ≤ normal.subgroupOf overgroup from inf_le_left)
    rwa [Subgroup.map_subgroupOf_eq_of_le hnormalLe] at hmapped
  have hfixedNormalized : overgroup ≤ Subgroup.normalizer (fixed.map overgroup.subtype : Set G) := by
    apply Subgroup.le_normalizer_iff.mpr
    intro conjugator hconjugator element helement
    obtain ⟨representative, hrepresentative, rfl⟩ := helement
    have hnormalFixed : fixed.Normal := normalFixedModulo_normal _ _
    exact Subgroup.mem_map.mpr ⟨(⟨conjugator, hconjugator⟩ : overgroup) * representative *
      (⟨conjugator, hconjugator⟩ : overgroup)⁻¹,
        hnormalFixed.conj_mem representative hrepresentative ⟨conjugator, hconjugator⟩, rfl⟩
  refine ⟨fixed.map overgroup.subtype, hambientStrict, hfixedLe, hfixedNormalized, ?_, ?_⟩
  · exact IsMulCommutative.of_setLike_mul_comm (fun first hfirst second hsecond =>
      congrArg (fun value : normal => (value : G))
        (isMulCommutative_iff.mp (thompsonCenterOf_commutative overgroup)
          ⟨first, hfixedLe hfirst⟩ ⟨second, hfixedLe hsecond⟩))
  · apply Subgroup.commutator_le.mpr
    intro first hfirst second hsecond
    obtain ⟨representative, hrepresentative, rfl⟩ := hfirst
    exact normalFixedModulo_commutator_le_kernel (normal.subgroupOf overgroup) (kernel.subgroupOf overgroup)
      (Subgroup.commutator_mem_commutator hrepresentative (Subgroup.mem_top (⟨second, hsecond⟩ : overgroup)))

end CFSG.RankThreeEvenClassification.Helpers
