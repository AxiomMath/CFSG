module

public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting

public section

open CFSG.Open

namespace CFSG.ComponentClassification.SimpleStructure

theorem radical_free (G : Type*) [Group G] [IsSimpleGroup G]
    (hnonab : ∃ left right : G, left * right ≠ right * left) : SolvableRadical.Free G := by
  let : Group.IsPerfect G := ⟨Helpers.commutator_eq_top G hnonab⟩
  intro candidate hnormal hsolvable
  rcases hnormal.eq_bot_or_eq_top with hbot | htop
  · exact hbot
  · let : Group.IsSolvable candidate := hsolvable
    let equivalence := (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
    have hsolvableG : Group.IsSolvable G := Group.isSolvable_of_surjective
      (f := equivalence.toMonoidHom) equivalence.surjective
    exact (Group.IsPerfect.not_isSolvable G hsolvableG).elim

theorem quasisimple (G : Type*) [Group G] [IsSimpleGroup G]
    (hnonab : ∃ left right : G, left * right ≠ right * left) : IsQuasisimple G := by
  let : Group.IsPerfect G := ⟨Helpers.commutator_eq_top G hnonab⟩
  exact Quasisimple.simple_of_perfect G

theorem fitting_eq_bot (G : Type*) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ left right : G, left * right ≠ right * left) : Fitting.subgroup G = ⊥ :=
  radical_free G hnonab _ (Fitting.normal G) (Fitting.solvable G)

theorem layer_eq_top (G : Type*) [Group G] [IsSimpleGroup G]
    (hnonab : ∃ left right : G, left * right ≠ right * left) : Layer.subgroup G = ⊤ := by
  apply top_unique
  apply Layer.component_le
  exact ⟨le_rfl, .refl ⊤, Components.quasisimple_of_equiv Subgroup.topEquiv (quasisimple G hnonab)⟩

theorem generalizedFitting_eq_top (G : Type*) [Group G] [IsSimpleGroup G]
    (hnonab : ∃ left right : G, left * right ≠ right * left) : GeneralizedFitting.subgroup G = ⊤ := by
  change Fitting.subgroup G ⊔ Layer.subgroup G = ⊤
  rw [layer_eq_top G hnonab, sup_top_eq]

theorem proper_simple_section_order {G : Type*} [Group G] [Finite G]
    (hK : IsKProperByOrder G) (candidate : Subgroup G) [IsSimpleGroup candidate]
    [Group.IsPerfect candidate] (hproper : candidate ≠ ⊤) : Nat.card candidate ∈ knownSimpleOrders := by
  have hnonab : ∃ left right : candidate, left * right ≠ right * left := by
    have hnoncomm := Group.IsPerfect.not_isMulCommutative candidate
    simpa only [isMulCommutative_iff, not_forall] using hnoncomm
  exact Helpers.simple_quotient_order_of_surjective G hK candidate hproper candidate hnonab
    (MonoidHom.id candidate) Function.surjective_id

theorem known_order_of_proper_generalizedFitting {G : Type*} [Group G] [Finite G]
    (hK : IsKProperByOrder G) [IsSimpleGroup (GeneralizedFitting.subgroup G)]
    [Group.IsPerfect (GeneralizedFitting.subgroup G)] (hproper : GeneralizedFitting.subgroup G ≠ ⊤) :
    Nat.card (GeneralizedFitting.subgroup G) ∈ knownSimpleOrders :=
  proper_simple_section_order hK _ hproper

end CFSG.ComponentClassification.SimpleStructure
