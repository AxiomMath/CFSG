module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2FamE6Graph
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6TwistedOuter

public noncomputable section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG
  CFSG.ComponentClassification.CatLeafProof
  CFSG.ComponentClassification
open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.SteinbergCE
  CFSG.LocalAnalysis.SteinbergCE.E6GraphCoset CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification.CatLeaf
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section


theorem cl24_twE6Outer_holds
    :
    ∀ (J : Type) [Group J] (p f : ℕ), p.Prime → p ≠ 2 → StatedLieAdmissible .twistedE6 0 p f →
      Blueprint.LieModel J .twistedE6 0 p f → ∀ α : MulAut J, orderOf α = 2 →
        α ∉ (MulAut.conj : J →* MulAut J).range →
        ∀ L : Subgroup (fixedSubgroup α), IsComponent L → Cl24Q p (fun f' => f' = f) L := by
  intro J _ p f hp hp2 hadm hm α hα hαo L hL
  have hf : 1 ≤ f := hadm.2.1
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨F, _, _, σ, hF, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card TwistTag.E6 hp hf
    (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hm).2
  have hF2 : Nat.card F = (p ^ f) ^ 2 := hF
  have : CharP F p := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp
    (show 1 ≤ f * 2 by omega) (by rw [hF2, ← pow_mul])
  have : CharP (AlgebraicClosure F) p :=
    charP_of_injective_algebraMap (algebraMap F (AlgebraicClosure F)).injective p
  have halg := isAlgebraic_zmod_of_isAlgClosure p F (AlgebraicClosure F)
  have hα' : orderOf (MulAut.congr e α) = 2 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective α).trans hα
  have hα'2 : MulAut.congr e α ^ 2 = 1 := by
    rw [← hα']
    exact pow_orderOf_eq_one _
  have hα'o : MulAut.congr e α ∉ twistedE6Inn F σ := by
    rintro ⟨c, hc⟩
    refine hαo ⟨e.symm c, (MulAut.congr e).injective ?_⟩
    rw [mulAut_congr_conj_twistedE6, MulEquiv.apply_symm_apply]
    exact hc
  obtain ⟨x, hxR, hx2, ⟨Φ⟩⟩ :=
    exists_mulEquiv_twisted_E6_outer_fixed hp2 hf F hF2 σ hσ _ hα'2 hα'o
  let Ψ := (fixedSubgroupCongrEquiv e α).trans Φ
  exact cl24_of_mulEquiv (L.equivMapOfInjective Ψ.toMonoidHom Ψ.injective)
    (cl24_oddLieCentralQuotient_of_isComponent_graphCosetFixed p hp2 hf _ halg 1
      (Or.inr rfl) hxR hx2
      (LocalCores.isComponent_map_mulEquiv Ψ hL))

end

end CFSG.OddStandard.SmallF3.HypA2Leaves
