module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieOutBase
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.ExcCommon
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedTrialityOddRotAlg

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.Yardstones.Md0ec50421ce4
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.UniquenessMaximal
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.HardMathSupport.Lang.E6Descent
  CFSG.RankThree.Chevalley CFSG.RankThree.LocalRank CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Dickson.Sec6.I923
open CFSG.LocalAnalysis.GLTheoremA.I1431C2 (catalogIs_of_mulEquiv)
open scoped commutatorElement

variable {T : TauCeti.CFSGIndex → Prop}

section Entrywise


theorem typeLayer_entrywise {τ : Tag} {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (hs : IsSimpleGroup ↥(adjointGroup τ (fixSubfield σ)))
    (hnab : ∃ a b : ↥(adjointGroup τ (fixSubfield σ)), a * b ≠ b * a) {G : Prop}
    (hG : catalogIs ↥(adjointGroup τ (fixSubfield σ)) T → G) :
    TypeLayer T (entrywiseAdjointAut τ σ) G := by
  obtain ⟨-, hinj, -, hJΓ, -, hJnorm, hquot⟩ :=
    Chevalley_coordinate_field_fixed_normal_subgroup τ K σ
  have hJC : fixedFieldImage τ σ ≤ adjointGroup τ K := fun x hx => (hJΓ hx).1
  let S : Subgroup ↥(adjointGroup τ K) := (fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)
  let eJ : ↥(adjointGroup τ (fixSubfield σ)) ≃* ↥(fixedFieldImage τ σ) :=
    (adjointGroup τ (fixSubfield σ)).equivMapOfInjective _ hinj
  let e : ↥S ≃* ↥(adjointGroup τ (fixSubfield σ)) :=
    (Subgroup.subgroupOfEquivOfLe hJC).trans eJ.symm
  haveI : IsSimpleGroup ↥S := e.isSimpleGroup
  refine typeLayer_of_simple_normal_comm _ S ?_ ?_ inferInstance ?_ fun h =>
    hG (catalogIs_of_mulEquiv e h)
  · rw [fixSubgroup_entrywiseAdjointAut]
    intro x hx
    exact Subgroup.mem_subgroupOf.2 (hJΓ (Subgroup.mem_subgroupOf.1 hx))
  · rw [fixSubgroup_entrywiseAdjointAut]
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
  · obtain ⟨a, b, hab⟩ := hnab
    exact ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by simpa using h))⟩

end Entrywise

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end

