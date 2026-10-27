module

public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeInheritance
import CFSG.GroupTheory.PCore.Transport

public section

namespace CFSG

variable {G : Type*} [Group G]

theorem isComponent_iff_open (L : Subgroup G) :
    IsComponent L ↔ Open.IsComponentOf L ⊤ := by
  constructor
  · rintro ⟨⟨hperfect, hsimple, _⟩, hsubnormal⟩
    exact ⟨le_top, ComponentClassification.Components.chain_of_mathlib_subnormal hsubnormal,
      hperfect.commutator_eq_top, hsimple⟩
  · rintro ⟨_, hsubnormal, hperfect, hsimple⟩
    have hquasisimple : Open.IsQuasisimple L := ⟨hperfect, hsimple⟩
    exact ⟨⟨⟨hperfect⟩, hsimple,
        ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian L hquasisimple⟩,
      ComponentClassification.Components.mathlib_subnormal_of_chain hsubnormal
        Subgroup.IsSubnormal.top⟩

theorem layer_eq_componentClassification (G : Type*) [Group G] :
    layer G = ComponentClassification.Layer.subgroup G :=
  WholeGroup.layerOf_congr isComponent_iff_open

theorem generalizedFitting_eq_componentClassification (G : Type*) [Group G] :
    generalizedFitting G = ComponentClassification.GeneralizedFitting.subgroup G := by
  rw [generalizedFitting, ComponentClassification.GeneralizedFitting.subgroup,
    layer_eq_componentClassification]
  rfl

theorem centralizer_generalizedFitting_le (G : Type*) [Group G] [Finite G] :
    Subgroup.centralizer (generalizedFitting G : Set G) ≤ generalizedFitting G := by
  rw [generalizedFitting_eq_componentClassification]
  exact ComponentClassification.GeneralizedFitting.centralizer_le G

theorem isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot
    (G : Type*) [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (hcore : pPrimeCore p G = ⊥) (hlayer : layer G = ⊥) : IsCharacteristicP p G := by
  have hgeneralized : generalizedFitting G = pCore p G := by
    rw [generalizedFitting, hlayer, sup_bot_eq, Fitting_eq_pcore G p hcore]
  change Subgroup.centralizer (pCore p G : Set G) ≤ pCore p G
  rw [← hgeneralized]
  exact centralizer_generalizedFitting_le G

theorem pCore_eq_open (G : Type*) [Group G] (p : ℕ) :
    pCore p G = Open.pCore p G := (Open.pCore_eq_pCore p G).symm

theorem pPrimeCore_eq_bot_of_isCharacteristicP
    (G : Type*) [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (hchar : IsCharacteristicP p G) : pPrimeCore p G = ⊥ := by
  have hopen : Subgroup.centralizer (Open.pCore p G : Set G) ≤ Open.pCore p G := by
    exact (show Subgroup.centralizer (pCore p G : Set G) ≤ pCore p G from hchar)
  exact RankThreeCoreUniqueness.Helpers.self_centralizing_pCore_primeComplementCore_eq_bot
    p Fact.out hopen

theorem layer_eq_bot_of_isCharacteristicP
    (G : Type*) [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (hchar : IsCharacteristicP p G) : layer G = ⊥ := by
  let : (pCore p G).Normal := pCore_normal (p := p)
  let : Group.IsNilpotent (pCore p G) := (pCore_isPGroup (p := p)).isNilpotent
  let : Group.IsSolvable (pCore p G) := inferInstance
  have hsubnormal : Open.IsSubnormal (pCore p G) ⊤ :=
    ComponentClassification.Components.chain_of_mathlib_subnormal
      (inferInstance : (pCore p G).Normal).isSubnormal
  have hcommutes := ComponentClassification.Layer.commutes_with_solvable_subnormal
    (pCore p G) hsubnormal
  have hbound : ComponentClassification.Layer.subgroup G ≤ pCore p G :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommutes).trans hchar
  let : Group.IsSolvable (ComponentClassification.Layer.subgroup G) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hbound)
  let : Group.IsPerfect (ComponentClassification.Layer.subgroup G) :=
    ComponentClassification.Layer.perfect G
  let : Subsingleton (ComponentClassification.Layer.subgroup G) :=
    ComponentClassification.SolvableKernelContainment.perfect_solvable_subsingleton
  rw [layer_eq_componentClassification]
  exact Subgroup.eq_bot_of_subsingleton _

theorem isCharacteristicP_iff_generalizedFitting_eq_pCore
    (G : Type*) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] :
    IsCharacteristicP p G ↔ generalizedFitting G = pCore p G := by
  constructor
  · intro hchar
    rw [generalizedFitting, layer_eq_bot_of_isCharacteristicP G p hchar, sup_bot_eq,
      Fitting_eq_pcore G p (pPrimeCore_eq_bot_of_isCharacteristicP G p hchar)]
  · intro heq
    change Subgroup.centralizer (pCore p G : Set G) ≤ pCore p G
    rw [← heq]
    exact centralizer_generalizedFitting_le G

end CFSG
