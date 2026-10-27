module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2FamTwE6Orbit
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2FamTwE6Out
public import CFSG.LocalAnalysis.SteinbergCEOddResidualTwistedE6Inner
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofSLFormUniform

public noncomputable section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG
  CFSG.ComponentClassification.CatLeafProof
  CFSG.ComponentClassification
open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.ToralSign CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf

section


theorem cl24_twE6Inner_holds :
    ∀ (J : Type) [Group J] (p f : ℕ), p.Prime → p ≠ 2 → StatedLieAdmissible .twistedE6 0 p f →
      Blueprint.LieModel J .twistedE6 0 p f → ∀ α : MulAut J, orderOf α = 2 →
        α ∈ (MulAut.conj : J →* MulAut J).range →
        ∀ L : Subgroup (fixedSubgroup α), IsComponent L →
          Cl24Q p (fun f' => f' = f ∨ f' = 2 * f ∨ f' = 4 * f) L := by
  intro J _ p f hp hp2 hadm hm α hα hαi L hL
  have hf : 1 ≤ f := hadm.2.1
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨F, _, _, σ, hF, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card TwistTag.E6 hp hf
    (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hm).2
  have hF2 : Nat.card F = (p ^ f) ^ 2 := hF
  have : CharP F p := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp
    (show 1 ≤ f * 2 by omega) (by rw [hF2, ← pow_mul])
  have : CharP (AlgebraicClosure F) p :=
    charP_of_injective_algebraMap (algebraMap F (AlgebraicClosure F)).injective p
  have hk := isAlgebraic_zmod_of_isAlgClosure p F (AlgebraicClosure F)
  have hα' : orderOf (MulAut.congr e α) = 2 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective α).trans hα
  have hα'2 : MulAut.congr e α ^ 2 = 1 := by
    rw [← hα']
    exact pow_orderOf_eq_one _
  have hα'i : MulAut.congr e α ∈ twistedE6Inn F σ := by
    obtain ⟨g, hg⟩ := hαi
    exact ⟨e g, by rw [← hg, mulAut_congr_conj_twistedE6]⟩
  obtain ⟨x, hxR, hx2, ⟨eA⟩⟩ :=
    LocalAnalysis.SteinbergCE.exists_mulEquiv_twisted_E6_inner_fixed hp2 hf hF2 σ hσ hα'2 hα'i
  obtain ⟨-, h6, -⟩ := rational_toral_sign_diagram_arithmetic
  obtain ⟨-, n6, -⟩ :=
    rational_toral_twist_semilinear_pinning_normalization (k := AlgebraicClosure F) p hp2 f hf
  obtain ⟨-, r6, -⟩ :=
    rational_inner_involution_finite_toral_twist_reduction p (AlgebraicClosure F) hp2 f hf
  set R := fixedPointsIn (adjointGroup TwistTag.E6.tag (AlgebraicClosure F))
    (frobTwistGL TwistTag.E6.tag (AlgebraicClosure F) p f
      (diagramMap TwistTag.E6 (AlgebraicClosure F))) with hR
  set N := ⁅R, R⁆ ⊓ Subgroup.centralizer {x} with hN
  have hRfin : Finite R := finite_fixedPointsIn_frobTwistGL p hf (by decide)
    (units_map_entrywiseHom_diagramMap (t := TwistTag.E6)
      (iterateFrobenius (AlgebraicClosure F) p f))
    (diagramMap_pow_order TwistTag.E6 (AlgebraicClosure F))
  have hNR : N ≤ R := fun y hy => Subgroup.commutator_le_self _ hy.1
  have hNfin : Finite N := Finite.of_injective _ (Subgroup.inclusion_injective hNR)
  let Ψ : fixedSubgroup α ≃* N := (fixedSubgroupCongrEquiv e α).trans eA
  set S' : Subgroup N := L.map Ψ.toMonoidHom with hS'
  have hS'c : IsComponent S' := LocalCores.isComponent_map_mulEquiv Ψ hL
  have hMN : S'.map N.subtype ≤ N := Subgroup.map_subtype_le _
  have hsub : (S'.map N.subtype).subgroupOf N = S' :=
    Subgroup.comap_map_eq_self_of_injective N.subtype_injective S'
  have hS'N : Assembly.IsComponentOf (S'.map N.subtype) N :=
    (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hMN).2
      (by rw [hsub]; exact hS'c)
  obtain ⟨Dd, ⟨mr, hmr, l, hl, hDχ, hDθ⟩, hDe, hXfin, hall⟩ :=
    exists_datum_uniform_of_twistReduction p hp2 hk hf
      (Or.inr (Or.inl rfl)) TwistTag.E6.cartan_perm symmetrizedCartan_perm_E6 h6.theta
      (fun l _ hγ => wordWeylMatrix_mul_diagramMap_conj_pinnedX TwistTag.E6 l hγ)
      (diagramMap_mem_normalizer TwistTag.E6) (map_conj_diagramMap TwistTag.E6 _ (Or.inl rfl))
      n6 (r6 x hxR hx2) (S'.map N.subtype) hMN
      (@ExcSelector.isPComponent_two_subgroupOf _ _ _ _ hNfin hS'N)
  obtain ⟨J₀, hJ₀X, hJ₀c, ⟨eL⟩⟩ := hall (S'.map N.subtype) hMN
    (@ExcSelector.isPComponent_two_subgroupOf _ _ _ _ hNfin hS'N)
  obtain ⟨J', hJ', hq⟩ := ExcSelector.exists_eq_orbitGroupC_of_isPComponent' Dd hXfin hJ₀X hJ₀c
  let eLJ : L ≃* (Dd.withOrbit J').orbitGroup :=
    ((L.equivMapOfInjective _ Ψ.injective).trans
      ((S'.equivMapOfInjective _ N.subtype_injective).trans
        (eL.trans (MulEquiv.subgroupCongr hJ')))).trans
      (Subgroup.subgroupOfEquivOfLe (Dd.withOrbit J').orbitGroup_le_adjointGroup)
  refine cl24_of_mulEquiv eLJ ?_
  simp only [e6SignDiagramReps, List.mem_cons, List.mem_nil_iff, or_false] at hmr
  rcases hmr with rfl | rfl | rfl
  · simp only [e6OmegaWords0, List.mem_cons, List.mem_nil_iff, or_false] at hl
    subst hl
    exact cl24_e6_twisted_zero Dd hDχ hDθ J' hq
  · simp only [e6OmegaWords20, List.mem_cons, List.mem_nil_iff, or_false] at hl
    subst hl
    exact cl24_e6_twisted_twenty Dd hDχ hDθ J' hq
  · simp only [e6OmegaWords2, List.mem_cons, List.mem_nil_iff, or_false] at hl
    subst hl
    exact cl24_e6_twisted_two Dd hDχ hDθ J' hq

theorem cl24_family_twistedE6 : Cl24OddFamily .twistedE6 := by
  intro J _ n p f hp hp2 hadm hm α hα Kc hKc
  obtain rfl : n = 0 := hadm.2.2
  refine Or.inl ?_
  by_cases hi : α ∈ (MulAut.conj : J →* MulAut J).range
  · exact (cl24_twE6Inner_holds J p f hp hp2 hadm hm α hα hi Kc hKc).mono fun f' h => by
      unfold Cl24FieldRel; omega
  · exact (cl24_twE6Outer_holds J p f hp hp2 hadm hm α hα hi Kc hKc).mono fun f' h => by
      unfold Cl24FieldRel; omega

end

end CFSG.OddStandard.SmallF3.HypA2Leaves
