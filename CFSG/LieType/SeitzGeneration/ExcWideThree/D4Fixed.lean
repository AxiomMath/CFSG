module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4OutTorus
public import CFSG.LieType.Chevalley.EvenCanonicalFieldCentralizer
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.Defs

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.CTP
  CFSG.LieType.SeitzGeneration.ExcOuterLeOne

section Fixed

variable {K : Type} [Field K] [Finite K]


theorem entrywiseFixedGroup_D4_eq_fixedFieldImage (σ : K ≃+* K) (hσ3 : σ ^ 3 = 1) :
    entrywiseFixedGroup Tag.D4 σ = fixedFieldImage Tag.D4 σ :=
  CFSG.GH74.GLS.Stage2.Bender.Thm1.entrywiseFixedGroup_D4_eq_fixedFieldImage_of_cube σ
    (fun c => congrArg (fun φ : K ≃+* K => φ c) hσ3)

theorem fixedSubgroup_entrywiseAdjointAut_D4 (σ : K ≃+* K) (hσ3 : σ ^ 3 = 1) :
    fixedSubgroup (entrywiseAdjointAut Tag.D4 σ) =
      (fixedFieldImage Tag.D4 σ).subgroupOf (adjointGroup Tag.D4 K) := by
  ext x
  rw [mem_fixedSubgroup, Subgroup.mem_subgroupOf,
    ← entrywiseFixedGroup_D4_eq_fixedFieldImage σ hσ3, mem_entrywiseFixedGroup]
  constructor
  · intro h
    refine ⟨x.2, ?_⟩
    have := congrArg Subtype.val h
    rwa [coe_entrywiseAdjointAut] at this
  · rintro ⟨-, h⟩
    refine Subtype.ext ?_
    rw [coe_entrywiseAdjointAut]
    exact h

noncomputable def fixedD4Equiv (σ : K ≃+* K) (hσ3 : σ ^ 3 = 1) :
    ↥(fixedSubgroup (entrywiseAdjointAut Tag.D4 σ)) ≃* adjointGroup Tag.D4 (fixSubfield σ) :=
  (MulEquiv.subgroupCongr (fixedSubgroup_entrywiseAdjointAut_D4 σ hσ3)).trans
    ((Subgroup.subgroupOfEquivOfLe (fun _ hj => (mem_entrywiseFixedGroup.1
      ((Chevalley_coordinate_field_fixed_normal_subgroup Tag.D4 K σ).2.2.2.1 hj)).1)).trans
      (fixedFieldImageEquiv (τ := Tag.D4) σ).symm)

theorem card_subfieldGroup_D4 (σ : K ≃+* K) (hσ3 : σ ^ 3 = 1) :
    Nat.card (subfieldGroup Tag.D4 σ) = Nat.card (adjointGroup Tag.D4 (fixSubfield σ)) :=
  Nat.card_congr (fixedD4Equiv σ hσ3).toEquiv

theorem eq_one_of_central_fixed_D4 (σ : K ≃+* K) (hσ3 : σ ^ 3 = 1) {x : adjointGroup Tag.D4 K}
    (hx : x ∈ fixedSubgroup (entrywiseAdjointAut Tag.D4 σ))
    (hc : ∀ y ∈ fixedSubgroup (entrywiseAdjointAut Tag.D4 σ), x * y = y * x) : x = 1 := by
  have hz : fixedD4Equiv σ hσ3 ⟨x, hx⟩ ∈
      Subgroup.center (adjointGroup Tag.D4 (fixSubfield σ)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, hy⟩ : ∃ y : ↥(fixedSubgroup (entrywiseAdjointAut Tag.D4 σ)),
        fixedD4Equiv σ hσ3 y = g := ⟨(fixedD4Equiv σ hσ3).symm g, by simp⟩
    rw [← hy, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc y y.2).symm
  rw [center_adjointGroup_eq_bot, Subgroup.mem_bot] at hz
  have h1 : (⟨x, hx⟩ : ↥(fixedSubgroup (entrywiseAdjointAut Tag.D4 σ))) = 1 :=
    (fixedD4Equiv σ hσ3).injective (by rw [hz, map_one])
  exact congrArg Subtype.val h1

end Fixed

end CFSG.LieType.SeitzGeneration.ExcWideThree
