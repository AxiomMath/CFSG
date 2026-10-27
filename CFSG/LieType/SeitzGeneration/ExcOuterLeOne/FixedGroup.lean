module

public import CFSG.LieType.Chevalley.EvenCanonicalFieldCentralizer
public import CFSG.LieType.Chevalley.EvenF4AutomorphismNormalForm
public import CFSG.RankThree.PartOne.SEITZ2.Common
public import CFSG.RankThree.SteinbergR3ESmallReeCosetDescent
public import CFSG.RankThree.PartOne.CTP.SeitzMaxAbstract
public import CFSG.RankThree.PartOne.CTP.StrongPClassification

open CFSG.RankThree.PartOne.CTP
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

public section

namespace CFSG.LieType.SeitzGeneration.ExcOuterLeOne


section Fixed

variable {τ : Tag} {K : Type} [Field K] [Finite K]

theorem fixedSubgroup_entrywiseAdjointAut_of_eq (σ : K ≃+* K)
    (hΓJ : entrywiseFixedGroup τ σ = fixedFieldImage τ σ) :
    fixedSubgroup (entrywiseAdjointAut τ σ) = (fixedFieldImage τ σ).subgroupOf (adjointGroup τ K) := by
  ext x
  rw [mem_fixedSubgroup, Subgroup.mem_subgroupOf, ← hΓJ, mem_entrywiseFixedGroup]
  constructor
  · intro h
    refine ⟨x.2, ?_⟩
    have := congrArg Subtype.val h
    rwa [coe_entrywiseAdjointAut] at this
  · rintro ⟨-, h⟩
    refine Subtype.ext ?_
    rw [coe_entrywiseAdjointAut]
    exact h

noncomputable def fixedEquivOfEq (σ : K ≃+* K) (hΓJ : entrywiseFixedGroup τ σ = fixedFieldImage τ σ) :
    ↥(fixedSubgroup (entrywiseAdjointAut τ σ)) ≃* adjointGroup τ (fixSubfield σ) :=
  (MulEquiv.subgroupCongr (fixedSubgroup_entrywiseAdjointAut_of_eq σ hΓJ)).trans
    ((Subgroup.subgroupOfEquivOfLe (fixedFieldImage_le.trans inf_le_left)).trans
      (fixedFieldImageEquiv (τ := τ) σ).symm)

theorem eq_one_of_central_fixed_of_eq (σ : K ≃+* K)
    (hΓJ : entrywiseFixedGroup τ σ = fixedFieldImage τ σ) {x : adjointGroup τ K}
    (hx : x ∈ fixedSubgroup (entrywiseAdjointAut τ σ))
    (hc : ∀ y ∈ fixedSubgroup (entrywiseAdjointAut τ σ), x * y = y * x) : x = 1 := by
  have hz : fixedEquivOfEq σ hΓJ ⟨x, hx⟩ ∈ Subgroup.center (adjointGroup τ (fixSubfield σ)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, hy⟩ : ∃ y : ↥(fixedSubgroup (entrywiseAdjointAut τ σ)),
        fixedEquivOfEq σ hΓJ y = g := ⟨(fixedEquivOfEq σ hΓJ).symm g, by simp⟩
    rw [← hy, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc y y.2).symm
  rw [center_adjointGroup_eq_bot, Subgroup.mem_bot] at hz
  have h1 : (⟨x, hx⟩ : ↥(fixedSubgroup (entrywiseAdjointAut τ σ))) = 1 :=
    (fixedEquivOfEq σ hΓJ).injective (by rw [hz, map_one])
  exact congrArg Subtype.val h1

end Fixed

section F4

variable {K : Type} [Field K] [Finite K]

theorem isCyclic_outer_F4 : IsCyclic (Outer (adjointGroup Tag.F4 K)) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  by_cases h2 : ringChar K = 2
  · have hK2 : Nat.card K = 2 ^ (n : ℕ) := by rw [hK, h2]
    have : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := by
      have : CharP K 2 := by rw [← h2]; exact ringChar.charP K
      exact this
    obtain ⟨-, -, ⟨Θ, -, hsurj, hker⟩, -⟩ := even_F4_exact_automorphism_normal_form n.pos K hK2
    exact CFSG.RankThree.PartOne.SEITZ2.isCyclic_outer_of_hom Θ hsurj hker
  · have : IsCyclic (K ≃+* K) := CFSG.RankThree.PartOne.CTP.isCyclic_ringEquiv_of_card hℓ n.pos hK
    obtain ⟨-, Θ, -, hsurj, hker, -⟩ := odd_F4_and_nonexceptional_G2_automorphism_normal_form
      hℓ h2 n.pos K hK .F4 (Or.inl rfl)
    exact CFSG.RankThree.PartOne.SEITZ2.isCyclic_outer_of_hom Θ hsurj hker

end F4

theorem entrywiseFixedGroup_F4_eq {K : Type} [Field K] [Finite K] (σ : K ≃+* K) :
    entrywiseFixedGroup Tag.F4 σ = fixedFieldImage Tag.F4 σ :=
  CFSG.RankThree.entrywiseFixedGroup_eq_fixedFieldImage_of_det_one (by rw [Matrix.det_transpose, det_cartan_F4]) σ

theorem entrywiseFixedGroup_E8_eq {K : Type} [Field K] [Finite K] (σ : K ≃+* K) :
    entrywiseFixedGroup Tag.E8 σ = fixedFieldImage Tag.E8 σ :=
  CFSG.RankThree.entrywiseFixedGroup_eq_fixedFieldImage_of_det_one (by rw [Matrix.det_transpose, det_cartan_E8]) σ

end CFSG.LieType.SeitzGeneration.ExcOuterLeOne
