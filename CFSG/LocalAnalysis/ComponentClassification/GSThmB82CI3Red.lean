module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CI3Sub
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3FGSolCI

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open scoped MatrixGroups

namespace Eight2

variable {X : Type} [Group X] [Finite X]

namespace Three

theorem false_of_sl23 (hCI : GSLit.ClassicalInvolutionInput)
    (hUc : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) [IsSimpleGroup X]
    (hnonab : ∃ u v : X, u * v ≠ v * u)
    (hunb : ∃ w : X, orderOf w = 2 ∧ oddCore (centralizer ({w} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X) {a z : X} {J N : Subgroup X} (ha : orderOf a = 2)
    (hJt : IsSec8JType (↥J ⧸ pPrimeCore 2 ↥J) 3 1) (hJa : J ≤ centralizer ({a} : Set X))
    (hCJ : centralizer ({a} : Set X) ≤ normalizer (J : Set X)) (hzJ : z ∈ J) (hzz : z * z = 1)
    (hz1 : z ≠ 1)
    (hNs : Open.IsSubnormal N (centralizer ({a} : Set X) ⊓ centralizer ({z} : Set X)))
    (haN : a ∈ N) (eN : ↥N ⧸ pPrimeCore 2 ↥N ≃* SL(2, ZMod 3)) : False := by
  have hAs := isSubnormal_sup hJt hJa hCJ hzJ hzz hz1 hNs eN
  have hAC := le_of_open hAs
  have hNJ : N ≤ normalizer (J : Set X) := (le_of_open hNs).trans (inf_le_left.trans hCJ)
  obtain ⟨eA⟩ := nonempty_quotient_sup_equiv hNJ
  let eF : Open.genFittingFStar X ≃* X :=
    (MulEquiv.subgroupCongr (StandardRecognition.genFittingFStar_eq_top_of_isSimpleGroup
      hnonab)).trans Subgroup.topEquiv
  have : IsSimpleGroup (Open.genFittingFStar X) := eF.isSimpleGroup
  have hFnonab : ∃ u v : Open.genFittingFStar X, u * v ≠ v * u := by
    obtain ⟨u, v, huv⟩ := hnonab
    refine ⟨eF.symm u, eF.symm v, fun h => huv (eF.symm.injective ?_)⟩
    rw [map_mul, map_mul]
    exact h
  have hout := HarrisLit.T1.F3FG.oddLieType_or_m11_of_slTwoThree_fstar hCI hFnonab ha hAC
    (isSubnormal_of_open hAs) (mem_sup_left haN) (eA.trans eN)
  have hcatF : Blueprint.Catalog (Open.genFittingFStar X) := by
    rcases hout with ⟨t, m, q, f, -, -, -, hm⟩ | h
    · exact Blueprint.lieModel_catalog _ t m q f hm
    · exact .inr (.inr (.inr (.inr ⟨.M11, h⟩)))
  obtain ⟨-, -, -, -, htop⟩ := SmallLocal.simple_generalized_fitting_self_local X hnonab
  let e : GeneralizedFitting.subgroup X ≃* X := (MulEquiv.subgroupCongr htop).trans topEquiv
  have hs : IsSimpleGroup (GeneralizedFitting.subgroup X) := e.isSimpleGroup
  have hn : ∃ u v : GeneralizedFitting.subgroup X, u * v ≠ v * u := by
    obtain ⟨u, v, huv⟩ := hnonab
    refine ⟨e.symm u, e.symm v, fun h => huv (e.symm.injective ?_)⟩
    rw [map_mul, map_mul]
    exact h
  exact hU (hUc X hs hn (SectionRank.catalog_of_mulEquiv (e.trans eF.symm) hcatF) hunb)

end Three

theorem false_of_sl23_conj (hCI : GSLit.ClassicalInvolutionInput)
    (hUc : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) [IsSimpleGroup X]
    (hnonab : ∃ u v : X, u * v ≠ v * u)
    (hunb : ∃ w : X, orderOf w = 2 ∧ oddCore (centralizer ({w} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X) {a z b δ g : X} {J : Subgroup X} (ha : orderOf a = 2)
    (hJt : IsSec8JType (↥J ⧸ pPrimeCore 2 ↥J) 3 1) (hJa : J ≤ centralizer ({a} : Set X))
    (hCJ : centralizer ({a} : Set X) ≤ normalizer (J : Set X)) (hzJ : z ∈ J) (hzz : z * z = 1)
    (hz1 : z ≠ 1) (hga : g⁻¹ * a * g = δ) (hgz : g⁻¹ * z * g = b) {N : Subgroup X}
    (hNX : N ≤ centralizer ({b} : Set X) ⊓ centralizer ({δ} : Set X))
    (hNs : (N.subgroupOf (centralizer ({b} : Set X) ⊓ centralizer ({δ} : Set X))).IsSubnormal)
    (hδN : δ ∈ N) (eN : ↥N ⧸ pPrimeCore 2 ↥N ≃* SL(2, ZMod 3)) : False := by
  set φ : X ≃* X := MulAut.conj g with hφ
  have hφa : φ δ = a := by
    rw [hφ, MulAut.conj_apply, ← hga]
    group
  have hφb : φ b = z := by
    rw [hφ, MulAut.conj_apply, ← hgz]
    group
  have hCmap : (centralizer ({b} : Set X) ⊓ centralizer ({δ} : Set X)).map φ.toMonoidHom =
      centralizer ({a} : Set X) ⊓ centralizer ({z} : Set X) := by
    rw [Subgroup.map_inf _ _ _ φ.injective, CatFactsSp4.map_centralizer_singleton,
      CatFactsSp4.map_centralizer_singleton, hφa, hφb, inf_comm]
  have hN' : Open.IsSubnormal (N.map φ.toMonoidHom)
      (centralizer ({a} : Set X) ⊓ centralizer ({z} : Set X)) := by
    have h1 := Three.open_map φ.toMonoidHom (Three.open_of_isSubnormal hNX hNs)
    rwa [hCmap] at h1
  have haN' : a ∈ N.map φ.toMonoidHom := by
    rw [← hφa]
    exact mem_map_of_mem _ hδN
  let e₀ : ↥(N.map φ.toMonoidHom) ≃* ↥N :=
    (N.equivMapOfInjective φ.toMonoidHom φ.injective).symm
  exact Three.false_of_sl23 hCI hUc hnonab hunb hU ha hJt hJa hCJ hzJ hzz hz1 hN' haN'
    ((UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 e₀).trans eN)

end Eight2

end CFSG.ComponentClassification.GSThmB
