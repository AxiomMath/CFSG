module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofTwE6Descent
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofTwE6Frame
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6GraphMain
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddOmegaField

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Chevalley CFSG.ComponentClassification.CatLeaf
open CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionRepresentation in
theorem oddLieCentralQuotient_of_omegaPlus_involution {J : Type} [Group J] {n p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .POmegaPlus n p f)
    (hm : Blueprint.LieModel J .POmegaPlus n p f) {α : MulAut J} (hα : orderOf α = 2)
    {Kc : Subgroup (fixedSubgroup α)} (hKc : IsComponent Kc) : OddLieCentralQuotient p Kc := by
  have hC : StatedClassicalModel J .POmegaPlus n p f :=
    EvenOrthSelector.statedModel_of_lieModel (by decide) hm
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hC
  have hrep := odd_orthogonal_involution_semilinear_representation .POmegaPlus
    (Or.inr (Or.inl rfl)) (EvenOrthSelector.statedModel_of_lieModel (by decide) hm) K hK e
  refine oddLieCentralQuotient_of_semilinearRepresentation hrep (coordinatePlusWitnessEquiv K e)
    (fun g hσ2 hord L hL => ?_) α hα hKc
  by_cases hσ : g.val.right = 1
  · exact oddOmegaPlusLinearInput_holds n K p f hp hp2 hK hadm g hσ hord L hL
  · exact oddOmegaPlusFieldInput_holds n K p f hp hp2 hK hadm g hσ2 hσ hord L hL

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]

theorem e6_twisted_zero_orbitGroup_oddLieCentralQuotient
    (D : OrthogonalSemilinearFixedRootDatum .E6 p k) (hχ : D.χ = signMaskChar .E6 0)
    (hθ : ∀ γ, D.θ (toReal γ) =
      toReal (thetaMap (ToralSign.wordElt .E6 []) TwistTag.E6.perm γ))
    (J' : Set.range D.classOrbit) (hq : IsQuasisimple (D.withOrbit J').orbitGroup) :
    OddLieCentralQuotient p (D.withOrbit J').orbitGroup := by
  have hp : p.Prime := Fact.out
  have hadm : StatedLieAdmissible .E6 0 p (D.e * 2) := ⟨hp, by have := D.one_le_e; omega, rfl⟩
  have hΔ : simpleUnion (D.withOrbit J').χ = Set.range e6SimpleRoot := by
    change simpleUnion D.χ = _
    rw [hχ]
    exact simpleUnion_e6_zero
  rcases simpleRootsJ_eq_empty_or_eq (D.withOrbit J') hΔ (fun i => e6_simple_inter_zero hχ i)
    with h0 | hJS
  · exact absurd (orbitGroup_eq_bot_of_simpleRootsJ_eq_empty _ h0)
      ((Subgroup.nontrivial_iff_ne_bot _).1 (CFSG.LocalCores.isQuasisimple_nontrivial hq))
  · exact e6_twisted_orbitGroup_oddLieCentralQuotient D (Or.inl rfl) hχ hθ J' hq hJS ⟨0, rfl⟩
      fun K₂ _ _ hK₂ _ hα _ hL => oddLieCentralQuotient_of_E6_involution oddE6GraphInput_holds
        hp D.odd hadm (lieModel_pairSpan_e6Simple hp D.odd hK₂) hα hL

theorem e6_twisted_twenty_orbitGroup_oddLieCentralQuotient
    (D : OrthogonalSemilinearFixedRootDatum .E6 p k) (hχ : D.χ = signMaskChar .E6 20)
    (hθ : ∀ γ, D.θ (toReal γ) =
      toReal (thetaMap (ToralSign.wordElt .E6 []) TwistTag.E6.perm γ))
    (J' : Set.range D.classOrbit) (hq : IsQuasisimple (D.withOrbit J').orbitGroup) :
    OddLieCentralQuotient p (D.withOrbit J').orbitGroup := by
  have hp : p.Prime := Fact.out
  have hadm : StatedLieAdmissible .POmegaPlus 5 p (D.e * 2) :=
    ⟨hp, by have := D.one_le_e; omega, by norm_num⟩
  have hΔ : simpleUnion (D.withOrbit J').χ = Set.range e6D5TwRoot := by
    change simpleUnion D.χ = _
    rw [hχ]
    exact simpleUnion_e6_twenty
  rcases simpleRootsJ_eq_empty_or_eq (D.withOrbit J') hΔ (fun i => e6_simple_inter_twenty hχ i)
    with h0 | hJS
  · exact absurd (orbitGroup_eq_bot_of_simpleRootsJ_eq_empty _ h0)
      ((Subgroup.nontrivial_iff_ne_bot _).1 (CFSG.LocalCores.isQuasisimple_nontrivial hq))
  · exact e6_twisted_orbitGroup_oddLieCentralQuotient D (Or.inr (Or.inl rfl)) hχ hθ J' hq hJS
      ⟨3, rfl⟩ fun K₂ _ _ hK₂ _ hα _ hL => oddLieCentralQuotient_of_omegaPlus_involution hp D.odd
        hadm (lieModel_pairSpan_e6D5Tw hp D.odd hK₂) hα hL

theorem e6_two_theta_orbitGroup_oddLieCentralQuotient
    (D : OrthogonalSemilinearFixedRootDatum .E6 p k)
    (hθ : ∀ γ, D.θ (toReal γ) =
      toReal (thetaMap (ToralSign.wordElt .E6 []) TwistTag.E6.perm γ))
    (J' : Set.range D.classOrbit) (hq : IsQuasisimple (D.withOrbit J').orbitGroup)
    (hJS : (D.withOrbit J').simpleRootsJ = {hiE6}) :
    OddLieCentralQuotient p (D.withOrbit J').orbitGroup := by
  have hfix : ∀ β ∈ (D.withOrbit J').simpleRootsJ,
      (D.withOrbit J').θ (toReal β) = toReal β := by
    intro β hβ
    rw [hJS, Set.mem_singleton_iff] at hβ
    subst hβ
    change D.θ _ = _
    rw [hθ, thetaMap_e6_hiE6]
  have horb := orbitGroup_eq_map_pairSpan (D.withOrbit J') hfix
  rw [hJS] at horb
  have hK : Nat.card (frobeniusFixedField k p D.e) = p ^ D.e :=
    card_frobeniusFixedField D.one_le_e
  have : Finite (frobeniusFixedField k p D.e) :=
    Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  let e : (D.withOrbit J').orbitGroup ≃* pairSpan .E6 (frobeniusFixedField k p D.e) {hiE6} :=
    (MulEquiv.subgroupCongr horb).trans
      ((Subgroup.equivMapOfInjective _ _ (baseChangeGL_injective _)).symm)
  exact oddLieCentralQuotient_of_mulEquiv e
    (oddLieCentralQuotient_pairSpan_hiE6 (Fact.out : p.Prime) D.odd hK
      (LocalCores.isQuasisimple_of_mulEquiv e hq))

theorem e6_twisted_two_orbitGroup_oddLieCentralQuotient
    (D : OrthogonalSemilinearFixedRootDatum .E6 p k) (hχ : D.χ = signMaskChar .E6 2)
    (hθ : ∀ γ, D.θ (toReal γ) =
      toReal (thetaMap (ToralSign.wordElt .E6 []) TwistTag.E6.perm γ))
    (J' : Set.range D.classOrbit) (hq : IsQuasisimple (D.withOrbit J').orbitGroup) :
    OddLieCentralQuotient p (D.withOrbit J').orbitGroup := by
  have hp : p.Prime := Fact.out
  have hadm : StatedLieAdmissible .PSL 6 p (D.e * 2) :=
    ⟨hp, by have := D.one_le_e; omega, by norm_num, by simp, by simp⟩
  rcases e6_two_simpleRootsJ D hχ hθ J' with h0 | hA | hT
  · exact absurd (orbitGroup_eq_bot_of_simpleRootsJ_eq_empty _ h0)
      ((Subgroup.nontrivial_iff_ne_bot _).1 (CFSG.LocalCores.isQuasisimple_nontrivial hq))
  · exact e6_twisted_orbitGroup_oddLieCentralQuotient D (Or.inr (Or.inr rfl)) hχ hθ J' hq hA
      ⟨0, rfl⟩ fun K₂ _ _ hK₂ _ hα _ hL => oddLieCentralQuotient_of_psl_involution hp D.odd hadm
        (lieModel_pairSpan_e6A5 hp D.odd hK₂) hα hL
  · exact e6_two_theta_orbitGroup_oddLieCentralQuotient D hθ J' hq hT

end CFSG.ComponentClassification.CatLeafProof
