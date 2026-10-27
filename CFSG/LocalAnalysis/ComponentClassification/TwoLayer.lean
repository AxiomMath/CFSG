module

public import CFSG.LocalAnalysis.ComponentClassification.BadComponents
public import CFSG.LocalAnalysis.ComponentClassification.BadComponentDetection
public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct

public section

open CFSG.Open

namespace CFSG.ComponentClassification.TwoLayer

@[expose] noncomputable def subgroup (G : Type*) [Group G] : Subgroup G :=
  sSup {component : Subgroup G | TwoComponents.IsTwoComponent component}

noncomputable def goodSubgroup (G : Type*) [Group G] : Subgroup G :=
  sSup {component : Subgroup G |
    TwoComponents.IsTwoComponent component ∧ IsQuasisimple component}

theorem good_le_layer (G : Type*) [Group G] : goodSubgroup G ≤ Layer.subgroup G := by
  apply sSup_le
  intro component hgood
  exact Layer.component_le ⟨le_top, hgood.1.1, hgood.2⟩

theorem good_bad_commute (G : Type*) [Group G] [Finite G] :
    ⁅goodSubgroup G, TwoComponents.badSubgroup G⁆ = ⊥ := by
  apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
  apply sSup_le
  intro component hgood
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (BadComponentDetection.commutes_with_bad_of_quasisimple component hgood.1 hgood.2)

theorem good_sup_bad (G : Type*) [Group G] :
    goodSubgroup G ⊔ TwoComponents.badSubgroup G = subgroup G := by
  classical
  apply le_antisymm
  · apply sup_le
    · apply sSup_le
      intro component hgood
      exact le_sSup hgood.1
    · apply sSup_le
      intro component hbad
      exact le_sSup hbad.1
  · apply sSup_le
    intro component hcomponent
    by_cases hquasisimple : IsQuasisimple component
    · have hle : component ≤ goodSubgroup G := le_sSup ⟨hcomponent, hquasisimple⟩
      exact hle.trans le_sup_left
    · have hle : component ≤ TwoComponents.badSubgroup G := le_sSup ⟨hcomponent, hquasisimple⟩
      exact hle.trans le_sup_right

theorem good_equiv_invariant {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (equivalence : G ≃* H) :
    (goodSubgroup G).map equivalence.toMonoidHom = goodSubgroup H := by
  apply le_antisymm
  · apply Subgroup.map_le_iff_le_comap.mpr
    apply sSup_le
    intro component hgood
    apply Subgroup.map_le_iff_le_comap.mp
    apply le_sSup
    exact ⟨(TwoComponentTransport.equiv_iff equivalence component).mpr hgood.1,
      Components.quasisimple_of_equiv
        (component.equivMapOfInjective equivalence.toMonoidHom equivalence.injective).symm hgood.2⟩
  · apply sSup_le
    intro component hgood
    let preimage := component.map equivalence.symm.toMonoidHom
    have hpreimage : TwoComponents.IsTwoComponent preimage :=
      (TwoComponentTransport.equiv_iff equivalence.symm component).mpr hgood.1
    have hpreimageQuasisimple : IsQuasisimple preimage := Components.quasisimple_of_equiv
      (component.equivMapOfInjective equivalence.symm.toMonoidHom equivalence.symm.injective).symm
        hgood.2
    have hle : preimage ≤ goodSubgroup G := le_sSup ⟨hpreimage, hpreimageQuasisimple⟩
    intro element hmem
    have hinverse : equivalence.symm element ∈ goodSubgroup G :=
      hle (Subgroup.mem_map_of_mem equivalence.symm.toMonoidHom hmem)
    exact ⟨equivalence.symm element, hinverse, equivalence.apply_symm_apply element⟩

theorem good_characteristic (G : Type*) [Group G] [Finite G] :
    (goodSubgroup G).Characteristic := by
  apply Subgroup.characteristic_iff_map_eq.mpr
  intro automorphism
  exact good_equiv_invariant automorphism

theorem local_component_in_layer_or_bad {G : Type*} [Group G] [Finite G]
    (element : G) (component : Subgroup (Subgroup.centralizer ({element} : Set G)))
    (hcomponent : TwoComponents.IsTwoComponent component)
    (hle : component.map (Subgroup.centralizer ({element} : Set G)).subtype ≤ subgroup G) :
    component.map (Subgroup.centralizer ({element} : Set G)).subtype ≤ Layer.subgroup G ∨
      component.map (Subgroup.centralizer ({element} : Set G)).subtype ≤
        TwoComponents.badSubgroup G := by
  let centralizer := Subgroup.centralizer ({element} : Set G)
  let good := goodSubgroup G
  let bad := TwoComponents.badSubgroup G
  let ambientComponent := component.map centralizer.subtype
  let : good.Characteristic := good_characteristic G
  let : bad.Characteristic := BadComponents.characteristic G
  have hgoodInvariant : good.map (MulAut.conj element).toMonoidHom = good :=
    (Subgroup.characteristic_iff_map_eq.mp inferInstance) (MulAut.conj element)
  have hbadInvariant : bad.map (MulAut.conj element).toMonoidHom = bad :=
    (Subgroup.characteristic_iff_map_eq.mp inferInstance) (MulAut.conj element)
  have hfixed : FixedCommutingProduct.fixedSubgroup (MulAut.conj element) = centralizer := by
    ext member
    change element * member * element⁻¹ = member ↔
      member ∈ Subgroup.centralizer ({element} : Set G)
    constructor
    · intro heq
      apply Subgroup.mem_centralizer_iff.mpr
      intro singleton hsingleton
      rw [Set.mem_singleton_iff.mp hsingleton]
      calc
        element * member = (element * member * element⁻¹) * element := by group
        _ = member * element := by rw [heq]
    · intro hmem
      have hcommutes := Subgroup.mem_centralizer_iff.mp hmem element (Set.mem_singleton element)
      rw [hcommutes]
      group
  have hderived := FixedCommutingProduct.derived_fixed good bad (good_bad_commute G)
    (MulAut.conj element) hgoodInvariant hbadInvariant
  rw [hfixed, good_sup_bad] at hderived
  let : Group.IsPerfect component := ⟨TwoComponents.perfect hcomponent⟩
  let : Group.IsPerfect ambientComponent := Group.IsPerfect.map centralizer.subtype
  have hcomponentFixed : ambientComponent ≤ subgroup G ⊓ centralizer :=
    le_inf hle (Subgroup.map_subtype_le component)
  have hcomponentProduct : ambientComponent ≤
      (good ⊓ centralizer) ⊔ (bad ⊓ centralizer) := by
    calc
      ambientComponent = ⁅ambientComponent, ambientComponent⁆ := Subgroup.commutator_eq_self.symm
      _ ≤ ⁅subgroup G ⊓ centralizer, subgroup G ⊓ centralizer⁆ :=
        Subgroup.commutator_mono hcomponentFixed hcomponentFixed
      _ ≤ (good ⊓ centralizer) ⊔ (bad ⊓ centralizer) := hderived
  let localGood := good.subgroupOf centralizer
  let localBad := bad.subgroupOf centralizer
  have hlocalProduct : component ≤ localGood ⊔ localBad := by
    have hmap : component.map centralizer.subtype ≤
        (localGood ⊔ localBad).map centralizer.subtype := by
      rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype]
      exact hcomponentProduct
    have hcomap := Subgroup.map_le_iff_le_comap.mp hmap
    rwa [Subgroup.comap_map_eq_self_of_injective centralizer.subtype_injective] at hcomap
  have hlocalGoodChain : IsSubnormal localGood ⊤ := Components.chain_of_mathlib_subnormal
    (Subgroup.IsSubnormal.step localGood ⊤ le_top Subgroup.IsSubnormal.top inferInstance)
  have hlocalBadChain : IsSubnormal localBad ⊤ := Components.chain_of_mathlib_subnormal
    (Subgroup.IsSubnormal.step localBad ⊤ le_top Subgroup.IsSubnormal.top inferInstance)
  have hpairJoin : sSup ({localGood, localBad} : Set (Subgroup centralizer)) =
      localGood ⊔ localBad := by simp
  have hpairSubnormal : ∀ localSubgroup ∈ ({localGood, localBad} : Set (Subgroup centralizer)),
      IsSubnormal localSubgroup ⊤ := by
    intro localSubgroup hmem
    rcases Set.mem_insert_iff.mp hmem with rfl | hmem
    · exact hlocalGoodChain
    · rw [Set.mem_singleton_iff.mp hmem]
      exact hlocalBadChain
  obtain ⟨containing, hcontaining, hcontained⟩ := TwoComponentJoins.exists_le_of_le_sSup component
    hcomponent ({localGood, localBad} : Set (Subgroup centralizer)) hpairSubnormal
      (by rwa [hpairJoin])
  rcases Set.mem_insert_iff.mp hcontaining with rfl | hcontaining
  · left
    exact (Subgroup.map_le_iff_le_comap.mpr hcontained).trans (good_le_layer G)
  · right
    rw [Set.mem_singleton_iff.mp hcontaining] at hcontained
    exact Subgroup.map_le_iff_le_comap.mpr hcontained

end CFSG.ComponentClassification.TwoLayer
