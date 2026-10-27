module

public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.OutFixed
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.ExcCommon

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement


theorem UpD42Pumpup.isD42_fixSubfield_of_entrywise {τ : Tag} {K : Type} [Field K] [Finite K]
    (σ : K ≃+* K) (hs : IsSimpleGroup ↥(adjointGroup τ (fixSubfield σ)))
    (hnab : ∃ a b : ↥(adjointGroup τ (fixSubfield σ)), a * b ≠ b * a)
    (h : UpD42Pumpup ↥(adjointGroup τ K) (entrywiseAdjointAut τ σ)) :
    IsCatalogLieIso ↥(adjointGroup τ (fixSubfield σ)) IsD42Index := by
  obtain ⟨-, hinj, -, hJΓ, -, -, hquot⟩ :=
    Chevalley_coordinate_field_fixed_normal_subgroup τ K σ
  have hJC : fixedFieldImage τ σ ≤ adjointGroup τ K := fun x hx => (hJΓ hx).1
  let J : Subgroup ↥(adjointGroup τ K) := (fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)
  let eJ : ↥(adjointGroup τ (fixSubfield σ)) ≃* ↥(fixedFieldImage τ σ) :=
    (adjointGroup τ (fixSubfield σ)).equivMapOfInjective _ hinj
  let e : ↥J ≃* ↥(adjointGroup τ (fixSubfield σ)) :=
    (Subgroup.subgroupOfEquivOfLe hJC).trans eJ.symm
  haveI := hs
  haveI : IsSimpleGroup ↥J := e.isSimpleGroup
  have hJfix : J ≤ fixSubgroup (entrywiseAdjointAut τ σ) := by
    rw [I923.fixSubgroup_entrywiseAdjointAut]
    intro x hx
    exact Subgroup.mem_subgroupOf.2 (hJΓ (Subgroup.mem_subgroupOf.1 hx))
  have hcomm : ⁅fixSubgroup (entrywiseAdjointAut τ σ), fixSubgroup (entrywiseAdjointAut τ σ)⁆ ≤
      J := by
    rw [I923.fixSubgroup_entrywiseAdjointAut]
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    let N : Subgroup ↥(entrywiseFixedGroup τ σ) :=
      (fixedFieldImage τ σ).subgroupOf (entrywiseFixedGroup τ σ)
    have hcN : ∀ x y : ↥(entrywiseFixedGroup τ σ), ⁅x, y⁆ ∈ N := by
      intro x y
      have h : (QuotientGroup.mk' N) ⁅x, y⁆ = 1 := by
        rw [map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.2 (hquot _ _)
      exact (QuotientGroup.eq_one_iff _).1 h
    have h1 := hcN ⟨(a : ModGL τ K), Subgroup.mem_subgroupOf.1 ha⟩
      ⟨(b : ModGL τ K), Subgroup.mem_subgroupOf.1 hb⟩
    rw [Subgroup.mem_subgroupOf] at h1 ⊢
    simpa [commutatorElement_def] using h1
  have hnabJ : ∃ a b : ↥J, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by simpa using h))⟩
  exact IsCatalogLieIso.of_mulEquiv e
    (isD42Type_of_upD42Pumpup_of_simple_normal_comm h J hJfix hcomm inferInstance hnabJ)


theorem UpD42Pumpup.false_of_entrywise {τ : Tag} {K : Type} [Field K] [Finite K]
    (σ : K ≃+* K) {t : StatedLieTag} (ht : t ≠ .POmegaPlus) {n d : ℕ}
    (hX : LieModel ↥(adjointGroup τ (fixSubfield σ)) t n 2 d)
    (hs : IsSimpleGroup ↥(adjointGroup τ (fixSubfield σ)))
    (hnab : ∃ a b : ↥(adjointGroup τ (fixSubfield σ)), a * b ≠ b * a)
    (h : UpD42Pumpup ↥(adjointGroup τ K) (entrywiseAdjointAut τ σ)) : False :=
  ht (CFSG.SeitzReduction.OmegaPilot.lieModel_POmega_two_unique (Or.inl rfl)
    (lieModel_of_isD42 (h.isD42_fixSubfield_of_entrywise σ hs hnab)) hX).1

end CFSG.HardMathSupport.Dickson.Sec6

end
