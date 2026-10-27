module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL34Z2c
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL34Z2b

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42

namespace EndB

theorem exists_pi_of_lieModel {E : Type} [Group E]
    (hY : Blueprint.LieModel (E ⧸ center E) .PSL 3 2 2) :
    ∃ π : E →* PSL3Four.S, Function.Surjective π ∧ π.ker = center E := by
  obtain ⟨θ⟩ := CatFactsSmall.nonempty_equiv_psl34_of_lieModel hY
  refine ⟨θ.toMonoidHom.comp (QuotientGroup.mk' (center E)), fun y => ?_, ?_⟩
  · obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (center E) (θ.symm y)
    refine ⟨x, ?_⟩
    rw [MonoidHom.comp_apply, hx, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
  · ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem isSimpleGroup_of_center_eq_bot {E : Type*} [Group E] (hq : IsQuasisimple E)
    (hZ : center E = ⊥) : IsSimpleGroup E := by
  have := hq.2.1
  let e : E ⧸ center E ≃* E := (QuotientGroup.quotientMulEquivOfEq hZ).trans
    QuotientGroup.quotientBot
  have : Nontrivial E := e.symm.toEquiv.nontrivial
  exact IsSimpleGroup.isSimpleGroup_of_surjective e.toMonoidHom e.surjective

theorem harris414_L34
    (hFC : AutPSL2FieldCentralizerInput)
    (hKC : AutPSL2CentralizerInput) (hI : AutPSL2InvolutionInput) (hKF : AutPSL2FusionInput)
    (hUC : GrSLit.L34UnitaryCentralizerFact) (hFF : L34FieldSylowFusionFact)
    (hCF : L34CyclicFourCenterFact) : Harris414L34Case := by
  intro X _ _ _ hnab hK hcat t L p f S w z V i j hhyp hL34
  obtain ⟨hs, h412, h47, hq, hns, hout⟩ := hhyp
  obtain ⟨hY, -⟩ := hL34
  obtain ⟨π, hπs, hker⟩ := exists_pi_of_lieModel hY
  have hL : LLayer hs π := ⟨h412, h47, hq, hout, hπs, hker⟩
  have hZ : center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ≠ ⊥ :=
    fun h => hns (isSimpleGroup_of_center_eq_bot hq h)
  rcases hL.center_cases hZ with h2 | ⟨h4, hZc, hQc⟩ | ⟨h4, hQZ⟩
  · by_cases hQ : pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) =
        zpowers (betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))
    · exact hL.false_of_Z2a hnab hFC hKC hI hKF hUC hFF hZ h2 hQ
    · exact hL.false_of_Z2b hFC hKC hI hKF hUC hZ h2 hQ
  · exact hL.false_of_Z4 hnab hFC hKC hI hKF hCF hZ h4 hZc hQc
  · by_cases hQc : IsCyclic ↥(pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
    · have hZc : IsCyclic ↥(center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) := by
        let e : ↥(center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) ≃*
            ↥(pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) :=
          ((center _).equivMapOfInjective _ (subtype_injective _)).trans
            (MulEquiv.subgroupCongr hQZ)
        exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
      exact hL.false_of_Z4 hnab hFC hKC hI hKF hCF hZ h4 hZc hQc
    · exact hL.false_of_E4 hFC hKC hI hKF hUC hZ h4 hQZ hQc

end EndB

end CFSG.ComponentClassification.HarrisLit
