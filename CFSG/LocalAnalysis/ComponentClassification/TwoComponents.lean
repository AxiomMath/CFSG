module

public import Mathlib
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import CFSG.Open.Defs
public import CFSG.Open.OrderForm
public import CFSG.LocalAnalysis.ComponentClassification.Helpers
public import CFSG.LocalAnalysis.ComponentClassification.OddCore
public import CFSG.LocalAnalysis.ComponentClassification.Components
public import CFSG.LocalAnalysis.ComponentClassification.Quasisimple
public import CFSG.LocalAnalysis.ComponentClassification.LocalComponents
public import CFSG.LocalAnalysis.ComponentClassification.Layer

public section

open CFSG.Open

namespace CFSG.ComponentClassification.TwoComponents

@[expose] def IsTwoComponent {G : Type*} [Group G] (subgroup : Subgroup G) : Prop :=
  IsSubnormal subgroup ⊤ ∧
    IsComponentOf (subgroup.map (QuotientGroup.mk' (componentClassificationOddCore G))) ⊤ ∧
    ∀ smaller : Subgroup G, smaller ≤ subgroup → IsSubnormal smaller ⊤ →
      smaller.map (QuotientGroup.mk' (componentClassificationOddCore G)) =
        subgroup.map (QuotientGroup.mk' (componentClassificationOddCore G)) →
      smaller = subgroup

theorem exists_lift {G : Type*} [Group G] [Finite G]
    (component : Subgroup (G ⧸ componentClassificationOddCore G))
    (hcomponent : IsComponentOf component ⊤) :
    ∃ lift : Subgroup G, IsTwoComponent lift ∧
      lift.map (QuotientGroup.mk' (componentClassificationOddCore G)) = component := by
  obtain ⟨lift, hsubnormal, hmap, _, _, hminimal⟩ :=
    Components.perfect_lift_of_component component hcomponent
  refine ⟨lift, ⟨hsubnormal, ?_, ?_⟩, hmap⟩
  · rw [hmap]
    exact hcomponent
  · intro smaller hle hchain hsmallerMap
    rw [hmap] at hsmallerMap
    exact hminimal smaller hle hchain hsmallerMap

theorem perfect {G : Type*} [Group G] {subgroup : Subgroup G}
    (hcomponent : IsTwoComponent subgroup) : commutator subgroup = ⊤ := by
  let quotient := QuotientGroup.mk' (componentClassificationOddCore G)
  let image := subgroup.map quotient
  let : Group.IsPerfect image := ⟨hcomponent.2.1.2.2.1⟩
  have hderivedNormal : (⁅subgroup, subgroup⁆.subgroupOf subgroup).Normal := by
    have hnormal :=
      (inferInstance : (⁅subgroup, subgroup⁆.subgroupOf (subgroup ⊔ subgroup)).Normal)
    have hsup : subgroup ⊔ subgroup = subgroup :=
      le_antisymm (sup_le le_rfl le_rfl) le_sup_left
    rw [hsup] at hnormal
    exact hnormal
  have hderivedChain : IsSubnormal ⁅subgroup, subgroup⁆ ⊤ :=
    IsSubnormal.step (Subgroup.commutator_le_self subgroup) hderivedNormal hcomponent.1
  have hderivedMap : ⁅subgroup, subgroup⁆.map quotient = subgroup.map quotient := by
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_eq_self
  have hderived : ⁅subgroup, subgroup⁆ = subgroup :=
    hcomponent.2.2 _ (Subgroup.commutator_le_self subgroup) hderivedChain hderivedMap
  let : Group.IsPerfect subgroup := Subgroup.isPerfect_iff.mpr hderived
  exact Group.IsPerfect.commutator_eq_top

theorem quasisimple_quotient {G : Type*} [Group G] [Finite G]
    {subgroup : Subgroup G} (hcomponent : IsTwoComponent subgroup) :
    IsQuasisimple (subgroup ⧸ componentClassificationOddCore subgroup) :=
  (Components.quotient_component_iff subgroup hcomponent.1).mp hcomponent.2.1

theorem nontrivial {G : Type*} [Group G] [Finite G] {subgroup : Subgroup G}
    (hcomponent : IsTwoComponent subgroup) : Nontrivial subgroup := by
  have hquasisimple := quasisimple_quotient hcomponent
  let : Nontrivial (subgroup ⧸ componentClassificationOddCore subgroup) :=
    Quasisimple.nontrivial hquasisimple
  exact (QuotientGroup.mk'_surjective (componentClassificationOddCore subgroup)).nontrivial

theorem ordinary_of_corefree {G : Type*} [Group G] [Finite G]
    (hcorefree : componentClassificationOddCore G = ⊥) {subgroup : Subgroup G}
    (hcomponent : IsTwoComponent subgroup) : IsComponentOf subgroup ⊤ := by
  have hsubgroupCore := OddCore.subnormal_corefree hcorefree subgroup hcomponent.1
  let quotient := QuotientGroup.mk' (componentClassificationOddCore subgroup)
  have hkernel : quotient.ker = ⊥ := by
    rw [QuotientGroup.ker_mk', hsubgroupCore]
  have equivalence : subgroup ≃* (subgroup ⧸ componentClassificationOddCore subgroup) :=
    MulEquiv.ofBijective quotient
      ⟨(MonoidHom.ker_eq_bot_iff quotient).mp hkernel, QuotientGroup.mk'_surjective _⟩
  exact ⟨le_top, hcomponent.1,
    Components.quasisimple_of_equiv equivalence (quasisimple_quotient hcomponent)⟩

@[expose] noncomputable def badSubgroup (G : Type*) [Group G] : Subgroup G :=
  sSup {subgroup : Subgroup G | IsTwoComponent subgroup ∧ ¬ IsQuasisimple subgroup}

theorem badSubgroup_eq_bot_of_corefree {G : Type*} [Group G] [Finite G]
    (hcorefree : componentClassificationOddCore G = ⊥) : badSubgroup G = ⊥ := by
  apply le_antisymm _ bot_le
  apply sSup_le
  intro subgroup hbad
  exact (hbad.2 (ordinary_of_corefree hcorefree hbad.1).2.2).elim

theorem ordinary_of_badSubgroup_eq_bot {G : Type*} [Group G] [Finite G]
    (hbad : badSubgroup G = ⊥) {subgroup : Subgroup G} (hcomponent : IsTwoComponent subgroup) :
    IsComponentOf subgroup ⊤ := by
  classical
  refine ⟨le_top, hcomponent.1, ?_⟩
  by_contra hnotQuasisimple
  have hle : subgroup ≤ badSubgroup G := le_sSup ⟨hcomponent, hnotQuasisimple⟩
  rw [hbad] at hle
  have hbot : subgroup = ⊥ := le_antisymm hle bot_le
  let : Nontrivial subgroup := nontrivial hcomponent
  exact (subgroup.nontrivial_iff_ne_bot.mp inferInstance) hbot

end CFSG.ComponentClassification.TwoComponents
