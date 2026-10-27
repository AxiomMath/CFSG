module

public import Mathlib.GroupTheory.Nilpotent

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex

universe v

variable {G : Type v} [Group G] [Finite G]

theorem supplied_sylow_ambient_of_entire_normalizer_le
    {p : ℕ} [Fact p.Prime] (Y : Subgroup G) (S : Sylow p Y)
    (hnormalizer : Subgroup.normalizer
      (((S : Subgroup Y).map Y.subtype : Subgroup G) : Set G) ≤ Y) :
    ∃ Q : Sylow p G, (Q : Subgroup G) = (S : Subgroup Y).map Y.subtype := by
  let A : Subgroup G := (S : Subgroup Y).map Y.subtype
  have hA : IsPGroup p A := S.isPGroup'.map Y.subtype
  obtain ⟨Q, hAQ⟩ := hA.exists_le_sylow
  let R : Subgroup (Q : Subgroup G) := A.subgroupOf (Q : Subgroup G)
  let V : Subgroup G := (Subgroup.normalizer (R : Set (Q : Subgroup G))).map
    (Q : Subgroup G).subtype
  have hRmap : R.map (Q : Subgroup G).subtype = A :=
    Subgroup.map_subgroupOf_eq_of_le hAQ
  have hVnormalizer : V ≤ Subgroup.normalizer (A : Set G) := by
    have hmap := Subgroup.le_normalizer_map (H := R) (Q : Subgroup G).subtype
    rw [hRmap] at hmap
    exact hmap
  have hVY : V ≤ Y := hVnormalizer.trans hnormalizer
  have hAV : A ≤ V := by
    rw [← hRmap]
    exact Subgroup.map_mono (Subgroup.le_normalizer (H := R))
  have hVp : IsPGroup p V :=
    (Q.isPGroup'.to_subgroup (Subgroup.normalizer (R : Set (Q : Subgroup G)))).map
      (Q : Subgroup G).subtype
  have hSmax : V.subgroupOf Y = (S : Subgroup Y) :=
    S.is_maximal' hVp.comap_subtype (Subgroup.map_le_iff_le_comap.mp hAV)
  have hVA : V = A := by
    have hmap := congrArg (fun K : Subgroup Y => K.map Y.subtype) hSmax
    rw [Subgroup.map_subgroupOf_eq_of_le hVY] at hmap
    exact hmap
  have hself : Subgroup.normalizer (R : Set (Q : Subgroup G)) = R := by
    apply Subgroup.map_injective (f := (Q : Subgroup G).subtype) Subtype.coe_injective
    exact hVA.trans hRmap.symm
  let : Group.IsNilpotent (Q : Subgroup G) := Q.isPGroup'.isNilpotent
  have hRtop : R = ⊤ := normalizerCondition_iff_only_full_group_self_normalizing.mp
    (Group.normalizerCondition_of_isNilpotent (G := (Q : Subgroup G))) R hself
  have hAQeq : A = (Q : Subgroup G) := by
    rw [← hRmap, hRtop, Subgroup.map_top, Subgroup.range_subtype]
  exact ⟨Q, hAQeq.symm⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
