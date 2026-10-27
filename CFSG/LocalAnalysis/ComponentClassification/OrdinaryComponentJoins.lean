module

public import CFSG.LocalAnalysis.ComponentClassification.LocalComponents

public section

open CFSG.Open

namespace CFSG.ComponentClassification.OrdinaryComponentJoins

theorem exists_le_of_le_sSup {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (hcomponent : IsComponentOf component ⊤)
    (subgroups : Set (Subgroup G)) (hsubnormal : ∀ subgroup ∈ subgroups, IsSubnormal subgroup ⊤)
    (hle : component ≤ sSup subgroups) : ∃ subgroup ∈ subgroups, component ≤ subgroup := by
  classical
  by_contra hnone
  have hcentralizes : sSup subgroups ≤ Subgroup.centralizer (component : Set G) := by
    apply sSup_le
    intro subgroup hmem
    have hnotLe : ¬ component ≤ subgroup := fun hcontained => hnone ⟨subgroup, hmem, hcontained⟩
    have hcommutes := (LocalComponents.subnormal_contains_or_commutes component subgroup
      hcomponent (hsubnormal subgroup hmem)).resolve_left hnotLe
    rw [Subgroup.commutator_comm] at hcommutes
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommutes
  have hcommutes : ⁅component, component⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hle.trans hcentralizes)
  let : Group.IsPerfect component := ⟨hcomponent.2.2.1⟩
  have hbot : component = ⊥ := by rwa [Subgroup.commutator_eq_self] at hcommutes
  exact (component.nontrivial_iff_ne_bot.mp (Quasisimple.nontrivial hcomponent.2.2)) hbot

theorem le_left_or_right {G : Type*} [Group G] [Finite G]
    (component left right : Subgroup G) (hcomponent : IsComponentOf component ⊤)
    (hleft : IsSubnormal left ⊤) (hright : IsSubnormal right ⊤) (hle : component ≤ left ⊔ right) :
    component ≤ left ∨ component ≤ right := by
  obtain ⟨containing, hmem, hcontained⟩ := exists_le_of_le_sSup component hcomponent {left, right}
    (by intro subgroup hsubgroup; rcases hsubgroup with rfl | rfl <;> assumption)
    (by simpa only [sSup_pair] using hle)
  rcases hmem with rfl | rfl
  · exact Or.inl hcontained
  · exact Or.inr hcontained

end CFSG.ComponentClassification.OrdinaryComponentJoins
