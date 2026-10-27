module

public import CFSG.LocalAnalysis.ComponentClassification.KProperRelativeBShell
import CFSG.LocalAnalysis.ComponentClassification.SmallLocalSimpleFitting
import CFSG.ClassicalInvolution.OrderForm
import CFSG.Milestones.CT_catalog_nonabelian_type_partition
public import CFSG.Fischer.Classification.Recognition.PSU6

public section

namespace CFSG.ComponentClassification.CTUSimple

theorem outcome_of_uOutcome {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hU : OutcomeLocal.UOutcome G) :
    (Blueprint.OddLieType G ∨
      ∃ n : ℕ, 7 ≤ n ∧ n % 4 = 3 ∧ Nonempty (G ≃* alternatingGroup (Fin n))) ∧
      Blueprint.Catalog G := by
  have htop : GeneralizedFitting.subgroup G = ⊤ :=
    (SmallLocal.simple_generalized_fitting_self_local G hnonab).2.2.2.2
  let e : GeneralizedFitting.subgroup G ≃* G :=
    (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
  have hout : Blueprint.OddLieType G ∨
      ∃ n : ℕ, 7 ≤ n ∧ n % 4 = 3 ∧ Nonempty (G ≃* alternatingGroup (Fin n)) := by
    rcases hU with h | ⟨n, hodd, h7, ⟨eA⟩, h1⟩ | ⟨-, hlt⟩
    · exact .inl ((ClassicalInvolution.oddLieType_congr e).1 h)
    · have hn1 : n % 4 ≠ 1 := fun h4 => (h1 h4).ne htop
      obtain ⟨k, rfl⟩ := hodd
      exact .inr ⟨2 * k + 1, h7, by omega, ⟨e.symm.trans eA⟩⟩
    · exact absurd htop hlt.ne
  refine ⟨hout, Milestones.ct_catalog_nonabelian_type_partition_converse G ?_⟩
  rcases hout with h | ⟨n, h7, -, hA⟩
  · exact .inr (.inl h)
  · exact .inl ⟨n, by omega, hA⟩

theorem ctu_kproper_simple_unbalanced_recognition_models_of_inputs
    (hU : KProperRelativeB.RelativeU Blueprint.Catalog)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (z : G) (hz : orderOf z = 2)
    (hunbal : CFSG.oddCore (Subgroup.centralizer ({z} : Set G)) ≠ ⊥) :
    (CFSG.Blueprint.OddLieType G ∨
      ∃ n : ℕ, 7 ≤ n ∧ n % 4 = 3 ∧ Nonempty (G ≃* alternatingGroup (Fin n))) ∧
      CFSG.Blueprint.Catalog G := by
  have htop : GeneralizedFitting.subgroup G = ⊤ :=
    (SmallLocal.simple_generalized_fitting_self_local G hnonab).2.2.2.2
  let e : GeneralizedFitting.subgroup G ≃* G :=
    (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
  have hsimple : IsSimpleGroup (GeneralizedFitting.subgroup G) := e.isSimpleGroup
  have hnonabF : ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := id hnonab
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  exact outcome_of_uOutcome hnonab (hU G hK hsimple hnonabF ⟨z, hz, hunbal⟩)

theorem ctu_kproper_simple_unbalanced_recognition_of_inputs
    (hU : KProperRelativeB.RelativeU Blueprint.Catalog)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (z : G) (hz : orderOf z = 2)
    (hunbal : CFSG.oddCore (Subgroup.centralizer ({z} : Set G)) ≠ ⊥) :
    CFSG.Blueprint.OddLieType G ∨
      ∃ n : ℕ, 7 ≤ n ∧ n % 4 = 3 ∧ Nonempty (G ≃* alternatingGroup (Fin n)) :=
  (ctu_kproper_simple_unbalanced_recognition_models_of_inputs hU G hnonab hK z hz hunbal).1

end CFSG.ComponentClassification.CTUSimple
