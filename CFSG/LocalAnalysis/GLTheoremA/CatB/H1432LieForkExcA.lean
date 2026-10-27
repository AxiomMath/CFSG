module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432LieForkDefs
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.ExcCommon
import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432LieForkBase
import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.G2
import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.F4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Dickson.Sec6.I923
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open scoped commutatorElement

section Entrywise


theorem outerSubThree_entrywise {t : StatedLieTag} {n f : ℕ} {τ : Tag} {K : Type} [Field K]
    [Finite K] (σ : K ≃+* K) (hs : IsSimpleGroup ↥(adjointGroup τ (fixSubfield σ)))
    (hX : OuterLayerThree t n f ↥(adjointGroup τ (fixSubfield σ))) :
    OuterSubThree t n f (fixSubgroup (entrywiseAdjointAut τ σ)) := by
  haveI : Finite ↥(fixSubfield σ) := Subtype.finite
  obtain ⟨-, hinj, -, hJΓ, -⟩ := Chevalley_coordinate_field_fixed_normal_subgroup τ K σ
  have hJC : fixedFieldImage τ σ ≤ adjointGroup τ K := fun x hx => (hJΓ hx).1
  have e : ↥((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)) ≃*
      ↥(adjointGroup τ (fixSubfield σ)) := (Subgroup.subgroupOfEquivOfLe hJC).trans
    ((adjointGroup τ (fixSubfield σ)).equivMapOfInjective _ hinj).symm
  haveI : Nontrivial ↥(adjointGroup τ (fixSubfield σ)) := hs.toNontrivial
  have hZ : Subgroup.center ↥(adjointGroup τ ↥(fixSubfield σ)) = ⊥ := center_adjointGroup_eq_bot
  obtain ⟨u, v, huv⟩ := exists_noncomm_of_center_bot hZ
  rw [fixSubgroup_entrywiseAdjointAut]
  refine outerSubThree_of_simple_normal_comm (fun x hx => ?_) ?_ e.isSimpleGroup
    ⟨e.symm u, e.symm v, fun h => huv (e.symm.injective (by simpa using h))⟩
    (outerLayerThree_congr e.symm hX)
  · exact Subgroup.mem_subgroupOf.2 (hJΓ (Subgroup.mem_subgroupOf.1 hx))
  · refine Subgroup.commutator_le.2 fun a ha b hb => Subgroup.mem_subgroupOf.2 ?_
    have h := commutator_entrywiseFixedGroup_le σ (Subgroup.commutator_mem_commutator
      (Subgroup.mem_subgroupOf.1 ha) (Subgroup.mem_subgroupOf.1 hb))
    simpa [commutatorElement_def] using h

theorem outerSubThree_entrywise_of_model {t : StatedLieTag} {n d : ℕ} {τ : Tag} {K : Type}
    [Field K] [Finite K] (σ : K ≃+* K) (ht : t ≠ .trialityD4)
    (hX : CFSG.Blueprint.LieModel ↥(adjointGroup τ (fixSubfield σ)) t n 3 d)
    (hs : IsSimpleGroup ↥(adjointGroup τ (fixSubfield σ))) :
    OuterSubThree t n (3 * d) (fixSubgroup (entrywiseAdjointAut τ σ)) :=
  outerSubThree_entrywise σ hs (outerLayerThree_of_field ht rfl hX)

theorem outerSubThree_of_untwisted {t : StatedLieTag} {n f : ℕ} {τ : Tag} {P : Type} [Group P]
    [Finite P] (hU : UntwistedChevalleyModel P τ (3 ^ f)) {ψ : MulAut P} (hψ3 : ψ ^ 3 = 1)
    (hψ : ψ ∉ inner P)
    (h : ∀ (F : Type) [Field F] [Finite F], Nat.card F = 3 ^ f →
      ∀ β : MulAut ↥(adjointGroup τ F), β ^ 3 = 1 → β ∉ inner ↥(adjointGroup τ F) →
        OuterSubThree t n f (fixSubgroup β)) :
    OuterSubThree t n f (fixSubgroup ψ) := by
  obtain ⟨F, _, _, hF, ⟨θ⟩⟩ := exists_equiv_adjointGroup_of_untwisted hU
  exact outerSubThree_congr θ (h F hF _ (by rw [← map_pow, hψ3, map_one])
    fun hin => hψ ((congr_mem_inner_iff_of_equiv θ ψ).mp hin))

end Entrywise

section G2


theorem lieOuterThreeAt_g2 : LieOuterThreeAt FamG2 := by
  intro P _ _ t n f hadm hF hm ψ hψ3 hψ
  obtain rfl := hF
  obtain rfl : n = 0 := hadm.2.2.1
  have hf : 1 ≤ f := hadm.2.1
  have hU : UntwistedChevalleyModel P .G2 (3 ^ f) := (hm.chevalleyExceptionalModel (by decide)).2
  refine outerSubThree_of_untwisted hU hψ3 hψ fun F _ _ hFcard β hβ3 hβinn => ?_
  obtain ⟨d, T, δ, rfl, -, hTc, hδ⟩ :=
    G2_descent Nat.prime_three hf hadm.2.2.2 F hFcard β hβ3 hβinn
  refine outerSubThree_of_conj δ β ?_
  rw [hδ]
  haveI : Finite ↥(fixSubfield T) := Subtype.finite
  have hM : ChevalleyExceptionalModel ↥(adjointGroup Tag.G2 ↥(fixSubfield T)) .G2 3 d :=
    ⟨⟨Nat.prime_three, by omega, rfl, Nat.le_self_pow (by omega) 3⟩, untwisted_adjointGroup hTc⟩
  exact outerSubThree_entrywise_of_model T (by decide) (Or.inr (Or.inl ⟨rfl, by decide, hM⟩))
    (CFSG.LieType.Simplicity.fam_g2_simplicity _ 3 d hM).2

end G2

section F4


theorem lieOuterThreeAt_f4 : LieOuterThreeAt FamF4 := by
  intro P _ _ t n f hadm hF hm ψ hψ3 hψ
  obtain rfl := hF
  obtain rfl : n = 0 := hadm.2.2
  have hf : 1 ≤ f := hadm.2.1
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hU : UntwistedChevalleyModel P .F4 (3 ^ f) := (hm.chevalleyExceptionalModel (by decide)).2
  refine outerSubThree_of_untwisted hU hψ3 hψ fun F _ _ hFcard β hβ3 hβinn => ?_
  obtain ⟨d, T, δ, rfl, -, hTc, hδ⟩ := F4_descent hf F hFcard β hβ3 hβinn
  refine outerSubThree_of_conj δ β ?_
  rw [hδ]
  haveI : Finite ↥(fixSubfield T) := Subtype.finite
  have hM : ChevalleyExceptionalModel ↥(adjointGroup Tag.F4 ↥(fixSubfield T)) .F4 3 d :=
    ⟨⟨Nat.prime_three, by omega, rfl⟩, untwisted_adjointGroup hTc⟩
  exact outerSubThree_entrywise_of_model T (by decide) (Or.inr (Or.inl ⟨rfl, by decide, hM⟩))
    (CFSG.LieType.Simplicity.fam_f4_simplicity _ 3 d hM).2

end F4

end CFSG.LocalAnalysis.GLTheoremA.H1420

end
