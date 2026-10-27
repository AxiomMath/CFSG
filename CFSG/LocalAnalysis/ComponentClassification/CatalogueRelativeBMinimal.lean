module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueRelativeBInduction
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBRadical
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBDerived
public import CFSG.LocalAnalysis.ComponentClassification.ProperComponentInputs
public import CFSG.Milestones.OO_odd_order_solvable
public import CFSG.LocalAnalysis.ComponentInitial.KProperPumpUpStatement
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalKGroup

public section

namespace CFSG.ComponentClassification.CatalogueRelativeB

open CFSG.Assembly

@[expose] def CatalogueSchreier : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X],
    (∃ a b : X, a * b ≠ b * a) → InCatalog X →
      Group.IsSolvable (OuterAutomorphisms.Outer X)

open LocalAnalysis.ComponentInitial (SchreierFor)

variable {C : GroupProp}

theorem proper_component_in_catalogue {G : Type} [Group G] [Finite G]
    (hC : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y → C Y → C X)
    (hK : KProper C G) (hfree : SolvableRadical.Free G)
    (component : Subgroup G) (hcomponent : CFSG.Open.IsComponentOf component ⊤)
    (hproper : component ≠ ⊤) : C component := by
  let : IsSimpleGroup component := RadicalFreeLayer.component_simple hfree component hcomponent
  let : Group.IsPerfect component := ⟨hcomponent.2.2.1⟩
  have hnonab : ∃ a b : component, a * b ≠ b * a := by
    have hnoncomm := Group.IsPerfect.not_isMulCommutative component
    simpa only [isMulCommutative_iff, not_forall] using hnoncomm
  exact UnbalancingLocal.catalog_of_kProper_of_surjective hC hK component hproper hnonab
    (MonoidHom.id component) Function.surjective_id

theorem proper_component_outer {G : Type} [Group G] [Finite G]
    (hC : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y → C Y → C X)
    (hK : KProper C G) (hfree : SolvableRadical.Free G)
    (hschreier : SchreierFor C) (component : Subgroup G)
    (hcomponent : CFSG.Open.IsComponentOf component ⊤) (hproper : component ≠ ⊤) :
    Group.IsSolvable (OuterAutomorphisms.Outer component) := by
  let : IsSimpleGroup component := RadicalFreeLayer.component_simple hfree component hcomponent
  let : Group.IsPerfect component := ⟨hcomponent.2.2.1⟩
  have hnonab : ∃ a b : component, a * b ≠ b * a := by
    have hnoncomm := Group.IsPerfect.not_isMulCommutative component
    simpa only [isMulCommutative_iff, not_forall] using hnoncomm
  exact hschreier component hnonab (proper_component_in_catalogue hC hK hfree component
    hcomponent hproper)

theorem proper_quotient_component_outer {G : Type} [Group G] [Finite G]
    (hC : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y → C Y → C X)
    (hK : KProper C G) (hschreier : SchreierFor C)
    (component : Subgroup (G ⧸ CFSG.Open.componentClassificationOddCore G))
    (hcomponent : CFSG.Open.IsComponentOf component ⊤) (hproper : component ≠ ⊤) :
    Group.IsSolvable (OuterAutomorphisms.Outer (component ⧸ Subgroup.center component)) := by
  let simple := component ⧸ Subgroup.center component
  let : IsSimpleGroup simple := hcomponent.2.2.2
  have hnonab := Helpers.quasisimple_central_quotient_nonabelian component hcomponent.2.2
  have hcatalogue : C simple :=
    UnbalancingLocal.catalog_of_kProper_of_surjective hC
      (CatalogueKProperOver.kProper_quotient hC hK _) component hproper hnonab
      (QuotientGroup.mk' (Subgroup.center component)) (QuotientGroup.mk'_surjective _)
  exact hschreier simple hnonab hcatalogue

theorem radical_free {G : Type} [Group G] [Finite G]
    (hC : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y → C Y → C X)
    (hK : KProper C G) (ih : InductionHypothesis C G)
    (hfailure : ¬ CentralTwoBInclusion.Property G) (hschreier : SchreierFor C) :
    SolvableRadical.Free G := by
  let : Group.IsSolvable (CFSG.Open.componentClassificationOddCore G) :=
    CFSG.Milestones.odd_order_solvable (OddCore.odd_card G)
  apply MinimalBRadical.no_solvable_normal_of_proper_outer _
    (proper_subgroup_B hC hK ih) hfailure (proper_quotient_component_outer hC hK hschreier)
  intro N hnormal hlt
  let : N.Normal := hnormal
  exact smaller_quotient_B hC hK ih N hlt

theorem layer_derived_simple {G : Type} [Group G] [Finite G]
    (hC : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y → C Y → C X)
    (hK : KProper C G) (hfree : SolvableRadical.Free G)
    (hschreier : SchreierFor C) (z : G) (hz : orderOf z = 2)
    (localComponent : Subgroup (Subgroup.centralizer ({z} : Set G)))
    (hlocal : TwoComponents.IsTwoComponent localComponent)
    (hnotQuasisimple : ¬ CFSG.Open.IsQuasisimple localComponent)
    (hcover : Subgroup.normalClosure
      (localComponent.map (Subgroup.centralizer ({z} : Set G)).subtype : Set G) ⊔
        Subgroup.zpowers z = ⊤) :
    Layer.subgroup G = commutator G ∧ IsSimpleGroup (commutator G) := by
  apply ReducedSemisimpleSimplicity.layer_derived_simple_of_proper_component_inputs
    hfree z hz _ _ localComponent hlocal hnotQuasisimple hcover
  · intro component hcomponent _
    exact ProperComponentInputs.even_of_odd_order_solvable
      (fun _ hodd => CFSG.Milestones.odd_order_solvable hodd) component hcomponent
  · intro component hcomponent hproper
    let : Group.IsSolvable (OuterAutomorphisms.Outer component) :=
      proper_component_outer hC hK hfree hschreier component hcomponent hproper
    have hcenter := RadicalFreeLayer.component_center_eq_bot hfree component hcomponent
    let projection := QuotientGroup.mk' (Subgroup.center component)
    have hkernel : projection.ker = ⊥ := by rw [QuotientGroup.ker_mk', hcenter]
    let equivalence := MulEquiv.ofBijective projection
      ⟨(MonoidHom.ker_eq_bot_iff projection).mp hkernel, QuotientGroup.mk'_surjective _⟩
    exact OuterAutomorphisms.solvable_of_equiv equivalence

theorem simple_unbalanced_section {G : Type} [Group G] [Finite G]
    (hC : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y → C Y → C X)
    (hK : KProper C G) (ih : InductionHypothesis C G)
    (hfailure : ¬ CentralTwoBInclusion.Property G) (hschreier : SchreierFor C) :
    IsSimpleGroup (commutator G) ∧ Group.IsPerfect (commutator G) ∧
      GeneralizedFitting.subgroup G = commutator G ∧ (commutator G).index ≤ 2 ∧
      ∃ z : G, orderOf z = 2 ∧ commutator G ⊔ Subgroup.zpowers z = ⊤ ∧
        ¬ (TwoComponents.badSubgroup (Subgroup.centralizer ({z} : Set G))).map
          (Subgroup.centralizer ({z} : Set G)).subtype ≤ TwoComponents.badSubgroup G ∧
        CFSG.Open.componentClassificationOddCore (Subgroup.centralizer ({z} : Set G)) ≠ ⊥ := by
  have hfree := radical_free hC hK ih hfailure hschreier
  have hsmaller : ∀ (N : Subgroup G) (_ : N.Normal),
      Nat.card (G ⧸ N) < Nat.card G → CentralTwoBInclusion.Property (G ⧸ N) := by
    intro N hnormal hlt
    let : N.Normal := hnormal
    exact smaller_quotient_B hC hK ih N hlt
  obtain ⟨z, hz, localComponent, hlocal, hnotQuasi, hnotContained,
    hclosure, hperfect, _, hindex, hcover⟩ :=
    MinimalBDerived.involution_component_reduction hsmaller (proper_subgroup_B hC hK ih) hfailure
  have hclosureCover : Subgroup.normalClosure
      (localComponent.map (Subgroup.centralizer ({z} : Set G)).subtype : Set G) ⊔
        Subgroup.zpowers z = ⊤ := by rwa [hclosure]
  obtain ⟨hlayer, hsimple⟩ :=
    layer_derived_simple hC hK hfree hschreier z hz localComponent hlocal hnotQuasi hclosureCover
  have hfitting : Fitting.subgroup G = ⊥ := hfree _ (Fitting.normal G) (Fitting.solvable G)
  have hgeneralized : GeneralizedFitting.subgroup G = commutator G := by
    change Fitting.subgroup G ⊔ Layer.subgroup G = commutator G
    rw [hfitting, bot_sup_eq, hlayer]
  have hbad : localComponent ≤ TwoComponents.badSubgroup (Subgroup.centralizer ({z} : Set G)) :=
    le_sSup ⟨hlocal, hnotQuasi⟩
  have hbadFailure : ¬ (TwoComponents.badSubgroup (Subgroup.centralizer ({z} : Set G))).map
      (Subgroup.centralizer ({z} : Set G)).subtype ≤ TwoComponents.badSubgroup G := by
    intro hcontained
    exact hnotContained ((Subgroup.map_mono hbad).trans hcontained)
  have hlocalCore :
      CFSG.Open.componentClassificationOddCore (Subgroup.centralizer ({z} : Set G)) ≠ ⊥ := by
    intro hbot
    exact hnotQuasi (TwoComponents.ordinary_of_corefree hbot hlocal).2.2
  exact ⟨hsimple, hperfect, hgeneralized, hindex, z, hz, hcover, hbadFailure, hlocalCore⟩

end CFSG.ComponentClassification.CatalogueRelativeB
