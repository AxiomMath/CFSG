module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalKGroup

public section

namespace CFSG.ComponentClassification.CatalogueU

open CFSG.Assembly CFSG.Blueprint Subgroup

theorem catalog_generalizedFitting_of_kProper {X : Type} [Group X]
    (hK : KProper Catalog X) [IsSimpleGroup (GeneralizedFitting.subgroup X)]
    (hnonab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a)
    (hproper : GeneralizedFitting.subgroup X ≠ ⊤) : Catalog (GeneralizedFitting.subgroup X) :=
  UnbalancingLocal.catalog_of_kProper_of_surjective (fun e h => SectionRank.catalog_of_mulEquiv e h)
    hK _ hproper hnonab (MonoidHom.id _) Function.surjective_id

theorem kProper_unbalanced_U_failure_is_simple_of_catalogU
    (hU : CatalogAlmostSimpleUnbalancedOutcome) {X : Type} [Group X] [Finite X]
    (hK : KProper Catalog X) (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnonab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a)
    (hz : ∃ z : X, orderOf z = 2 ∧ CFSG.oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hfail : ¬ OutcomeLocal.UOutcome X) :
    GeneralizedFitting.subgroup X = ⊤ ∧ IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a := by
  have htop : GeneralizedFitting.subgroup X = ⊤ := by
    by_contra hproper
    exact hfail (hU X hsimple hnonab (catalog_generalizedFitting_of_kProper hK hnonab hproper) hz)
  let e : X ≃* GeneralizedFitting.subgroup X :=
    Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop.symm)
  refine ⟨htop, e.isSimpleGroup, ?_⟩
  obtain ⟨a, b, hab⟩ := hnonab
  exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩

end CFSG.ComponentClassification.CatalogueU
