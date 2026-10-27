module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBasic

public section

namespace CFSG.QuasithinUnique.Setup.Family

open CFSG.Quasithin CFSG.SectionRank CFSG.Blueprint CFSG.Assembly.LowTwoRank

structure ActorLayer (V : Type) [CommGroup V] [Finite V] (H T M : Subgroup (MulAut V)) : Prop where
  offenders_nonempty : ∃ A : Subgroup (MulAut V), IsBestOffender H A
  J_normal : ((bestJ H).subgroupOf H).Normal
  eq_J_sup_T : H = bestJ H ⊔ T
  eq_K_sup_T : H = oddOrderSubgroup H ⊔ T
  K_le_J : oddOrderSubgroup H ≤ bestJ H
  offender_centralizes_rad : ∀ A : Subgroup (MulAut V), IsBestOffender H A →
    A ≤ Subgroup.centralizer (radIn H : Set (MulAut V))
  offender_normalizes_components : ∀ A : Subgroup (MulAut V), IsBestOffender H A →
    ∀ L : Subgroup (MulAut V), IsComp L H → A ≤ Subgroup.normalizer (L : Set (MulAut V))
  core_eq_rad : coreIn H M = radIn H
  rad_eq_fitting : radIn H = fittingIn H
  fitting_eq_center : fittingIn H = centerIn (oddOrderSubgroup H)
  rad_odd : Odd (Nat.card (radIn H))
  K_eq_layer : oddOrderSubgroup H = layerIn H
  layer_eq_genFitting : layerIn H = genFittingIn H
  exists_component : ∃ L : Subgroup (MulAut V), IsComp L H
  components_generate : (⨆ (L : Subgroup (MulAut V)) (_ : IsComp L H), L) = oddOrderSubgroup H
  components_commute : ∀ L L' : Subgroup (MulAut V), IsComp L H → IsComp L' H → L ≠ L' →
    ∀ x ∈ L, ∀ y ∈ L', x * y = y * x
  components_normal : ∀ L : Subgroup (MulAut V), IsComp L H →
    (L.subgroupOf (oddOrderSubgroup H)).Normal
  components_transitive : ∀ L L' : Subgroup (MulAut V), IsComp L H → IsComp L' H →
    ∃ t ∈ T, L' = L.map (MulAut.conj t).toMonoidHom
  component_commutator : ∀ L : Subgroup (MulAut V), IsComp L H →
    ∃ A : Subgroup (MulAut V), IsBestOffender H A ∧ ⁅L, A⁆ = L

@[expose] def ActorLayerProp : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (H T M E : Subgroup (MulAut V)),
    FFHyp V H T M E → ¬ Group.IsSolvable H → ActorLayer V H T M

@[expose] def NoSporadicComponentProp : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (H T M E : Subgroup (MulAut V)),
    FFHyp V H T M E → ¬ Group.IsSolvable H → CFSG.IsStronglyQuasithin H →
    ∀ L : Subgroup (MulAut V), IsComp L H → ¬ NativeSporadic.SporadicRep (CQ L)

@[expose] def NoSuzukiComponentProp : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (H T M E : Subgroup (MulAut V)),
    FFHyp V H T M E → ∀ L : Subgroup (MulAut V), IsComp L H → ∀ f : ℕ, ¬ SuzukiModel (CQ L) 2 f

@[expose] def NoAlt78BinaryLinearProp : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (H T M E : Subgroup (MulAut V)),
    FFHyp V H T M E → ¬ Group.IsSolvable H → ∀ L : Subgroup (MulAut V), IsComp L H →
      (∀ n : ℕ, (n = 7 ∨ n = 8) → ¬ Nonempty (CQ L ≃* alternatingGroup (Fin n))) ∧
      (∀ n : ℕ, 3 ≤ n → ¬ Nonempty (CQ L ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)))

@[expose] def OddClassicalSmallProp : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (H T M E : Subgroup (MulAut V)),
    FFHyp V H T M E → ¬ Group.IsSolvable H → IsSQTKCat H →
    ∀ L : Subgroup (MulAut V), IsComp L H → ∀ p : ℕ, p.Prime → p ≠ 2 →
      ∀ (t : StatedLieTag) (n f : ℕ), StatedClassicalModel (CQ L) t n p f → SmallOddTuple t n p f

@[expose] def FamilyRestrictionProp : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (H T M E : Subgroup (MulAut V)),
    FFHyp V H T M E → ¬ Group.IsSolvable H → IsSQTKCat H → NoEvenSL2Component H →
    ∀ L : Subgroup (MulAut V), IsComp L H →
      ResidualFamily (CQ L) ∧
      (Nat.card (Subgroup.center ↥L) = 1 ∨ Nat.card (Subgroup.center ↥L) = 3) ∧
      CFSG.IsStronglyQuasithin (CQ L)


@[expose] def IsConjAction {G : Type} [Group G] (H L : Subgroup G)
    (α : ↥H →* MulAut (CQ L)) : Prop :=
  ∀ (h : ↥H) (l l' : ↥L), (l' : G) = (h : G) * l * (h : G)⁻¹ →
    α h (QuotientGroup.mk l) = QuotientGroup.mk l'

structure ResidualStructure (V : Type) [CommGroup V] [Finite V] (H T M L : Subgroup (MulAut V)) :
    Prop where
  isComp : IsComp L H
  unique : ∀ L' : Subgroup (MulAut V), IsComp L' H → L' = L
  normal : (L.subgroupOf H).Normal
  K_eq : oddOrderSubgroup H = L
  layer_eq : L = layerIn H
  genFitting_eq : layerIn H = genFittingIn H
  H_eq : H = L ⊔ T
  quotient_two : IsPGroup 2 (↥H ⧸ L.subgroupOf H)
  centralizer_eq : H ⊓ Subgroup.centralizer (L : Set (MulAut V)) = radIn H
  rad_eq_fitting : radIn H = fittingIn H
  fitting_eq_center : fittingIn H = centerIn L
  center_card : Nat.card (centerIn L) = 1 ∨ Nat.card (centerIn L) = 3
  action : ∃ α : ↥H →* MulAut (CQ L), IsConjAction H L α ∧
    α.ker = (centerIn L).subgroupOf H ∧
    (MulAut.conj : CQ L →* MulAut (CQ L)).range ≤ α.range ∧
    (∀ N : Subgroup (MulAut (CQ L)), N ≤ α.range → (N.subgroupOf α.range).Normal → IsPGroup 2 N →
      N = ⊥) ∧
    Function.Injective (α.comp (T.subgroupOf H).subtype) ∧
    IsSylowTwoOf ((T.subgroupOf H).map α) α.range ∧
    ¬ (((T.subgroupOf H).map α).subgroupOf α.range).Normal ∧
    (T.subgroupOf H).map α ≤ (M.subgroupOf H).map α ∧ (M.subgroupOf H).map α < α.range ∧
    ∀ X : Subgroup (MulAut (CQ L)), (T.subgroupOf H).map α ≤ X → X < α.range →
      X ≤ (M.subgroupOf H).map α

@[expose] def OneQuasisimpleResidualProp : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (H T M E : Subgroup (MulAut V)),
    FFHyp V H T M E → ¬ Group.IsSolvable H → IsSQTKCat H → NoEvenSL2Component H →
    ∃ L : Subgroup (MulAut V), ResidualStructure V H T M L

@[expose] def OddRankLeOne (S : Type) [Group S] : Prop :=
  ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.pRank r S ≤ 1

@[expose] def OddRankOneOddClassicalProp : Prop :=
  ∀ (S : Type) [Group S] [Finite S], OddRankLeOne S → ∀ p : ℕ, p.Prime → p ≠ 2 →
    ∀ (t : StatedLieTag) (n f : ℕ), StatedClassicalModel S t n p f →
      t = .PSL ∧ n = 2 ∧ f = 1 ∧ 5 ≤ p

@[expose] def OddRankOneEvenClassicalProp : Prop :=
  ∀ (S : Type) [Group S] [Finite S], OddRankLeOne S → ∀ (t : StatedLieTag) (n f : ℕ),
    StatedClassicalModel S t n 2 f → (t = .PSL ∧ n = 2 ∧ 2 ≤ f) ∨ (t = .PSL ∧ n = 3 ∧ f = 1)

@[expose] def OddRankOneChevalleyProp : Prop :=
  ∀ (S : Type) [Group S] [Finite S], OddRankLeOne S → ∀ (t : StatedLieTag) (p f : ℕ),
    t ∈ chevalleyExceptionalTags → ChevalleyExceptionalModel S t p f →
      t = .trialityD4 ∧ p = 2 ∧ f = 1

@[expose] def OddRankOneReeTitsProp : Prop :=
  ∀ (S : Type) [Group S] [Finite S], OddRankLeOne S → ∀ (t : StatedLieTag) (p f : ℕ),
    t ∈ reeTitsTags → ¬ ReeTitsModel S t p f

@[expose] def TrialityTwoHasRankTwoProp : Prop :=
  ∀ (S : Type) [Group S] [Finite S], ChevalleyExceptionalModel S .trialityD4 2 1 →
    2 ≤ CFSG.pRank 3 S

@[expose] def ComponentOddRankTwoNormalProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H L : Subgroup G), IsSQTKCat H → IsComp L H →
    ∀ p : ℕ, p.Prime → p ≠ 2 → 2 ≤ CFSG.pRank p (CQ L) → (L.subgroupOf H).Normal

end CFSG.QuasithinUnique.Setup.Family
