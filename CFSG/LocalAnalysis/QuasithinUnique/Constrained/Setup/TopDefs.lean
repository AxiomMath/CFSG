module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyStatements

public section

namespace CFSG.QuasithinUnique.Setup.Top

open CFSG.Quasithin CFSG.SectionRank CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.Family CFSG.QuasithinUnique.Setup.Lift
open scoped Pointwise

variable {G : Type} [Group G]

abbrev reducedModule (S P : Subgroup G) : Subgroup G :=
  conjClosure (omegaOneCenterOf S) P

structure PrePacket (S P : Subgroup G) (r : ℕ) (L : Fin r → Subgroup G) : Prop where
  pow_two : ∃ k : ℕ, r = 2 ^ k
  injective : Function.Injective L
  le_odd : ∀ i, L i ≤ oddOrderSubgroup P
  permuted : ∀ s ∈ S, ∀ i, ∃ j, (L i).map (MulAut.conj s).toMonoidHom = L j
  transitive : ∀ i j, ∃ s ∈ S, (L i).map (MulAut.conj s).toMonoidHom = L j
  chi0 : ∀ i, IsChi0Block P (L i)
  commute : ∀ i j, i ≠ j → ⁅L i, L j⁆ = ⊥
  odd_eq : oddOrderSubgroup P = ⨆ i, L i
  central : ∀ i, L i ⊓ (⨆ j, ⨆ (_ : j ≠ i), L j) ≤ centerIn (L i)
  perfect : ∀ i, ⁅L i, thompsonJ S⁆ = L i
  gen : ∀ i, P = L i ⊔ S
  u_le : ∀ i, blockU (L i) ≤ reducedModule S P

structure BlockPacket (S P : Subgroup G) (r : ℕ) (L : Fin r → Subgroup G) : Prop
    extends PrePacket S P r L where
  one_le : 1 ≤ r
  le_two : r ≤ 2
  escape : ∀ i, ¬ L i ≤ uniqueMaxOver S P
  prod_eq : (P : Set G) =
    (uniqueMaxOver S P : Set G) * (List.ofFn fun i => (L i : Set G)).prod

structure SolvableRefinement (r : ℕ) (L : Fin r → Subgroup G) : Prop where
  alt4 : ∀ i, Nonempty (↥(L i) ≃* alternatingGroup (Fin 4))
  type : ∀ i, IsAltType (L i) 3
  direct : ∀ i, L i ⊓ (⨆ j, ⨆ (_ : j ≠ i), L j) = ⊥

@[expose] def EvenSL2Refinement (S P : Subgroup G) (n r : ℕ) (L : Fin r → Subgroup G) : Prop :=
  (autOn (thompsonJ S) (reducedModule S P) ≤ autOn (oddOrderSubgroup P) (reducedModule S P) →
    ∀ i, IsLin2Type (L i) n) ∧
  (¬ autOn (thompsonJ S) (reducedModule S P) ≤ autOn (oddOrderSubgroup P) (reducedModule S P) →
    n = 2 ∧ ∀ i, IsAltType (L i) 5)

@[expose] def HasEvenSL2Component {A : Type} [Group A] (H : Subgroup A) : Prop :=
  ∃ (D : Subgroup A) (n : ℕ) (F : Type) (_ : Field F), IsComp D H ∧ 2 ≤ n ∧ Nat.card F = 2 ^ n ∧
    Nonempty (CQ D ≃* Matrix.SpecialLinearGroup (Fin 2) F)

structure OneQuasisimpleData [Finite G] (S P : Subgroup G)
    (hV : CFSG.Open.IsElemAbelian 2 (reducedModule S P))
    (hP : P ≤ Subgroup.normalizer (reducedModule S P : Set G))
    (L : Subgroup (MulAut (reducedModule S P))) : Prop where
  residual : @ResidualStructure (reducedModule S P) (commGroupOfElemAbelian hV) inferInstance
    (autOn P (reducedModule S P)) (autOn S (reducedModule S P))
    (autOn (uniqueMaxOver S P) (reducedModule S P)) L
  composite_kernel : ∀ α : ↥(autOn P (reducedModule S P)) →* MulAut (CQ L),
    IsConjAction (autOn P (reducedModule S P)) L α → ∀ p : P,
      (α ⟨rho (reducedModule S P) P hP p, (mem_autOn_self_iff hP).2 ⟨p, rfl⟩⟩ = 1 ↔
        rho (reducedModule S P) P hP p ∈ centerIn L)
  restriction : ∃ φ : ↥(oddOrderSubgroup P) →* ↥L, Function.Surjective φ ∧
    φ.ker = (P ⊓ Subgroup.centralizer (reducedModule S P : Set G)).subgroupOf
      (oddOrderSubgroup P) ∧
    ∀ n : ↥(oddOrderSubgroup P),
      (φ n : MulAut (reducedModule S P)) =
        rho (reducedModule S P) P hP ⟨n, oddOrderSubgroup_le P n.2⟩

structure ActorData [Finite G] (S P : Subgroup G) (hV : CFSG.Open.IsElemAbelian 2 (reducedModule S P)) :
    Prop where
  sqtk : IsSQTKCat (autOn P (reducedModule S P))
  exists_offender : ∃ E : Subgroup (MulAut (reducedModule S P)),
    @FFHyp (reducedModule S P) (commGroupOfElemAbelian hV) inferInstance
      (autOn P (reducedModule S P)) (autOn S (reducedModule S P))
      (autOn (uniqueMaxOver S P) (reducedModule S P)) E

@[expose] def SolvableA3Family : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S P : Subgroup G), PushUpObstruction S P →
    Group.IsSolvable (autOn P (reducedModule S P)) →
    ∃ (r : ℕ) (K : Fin r → Subgroup G), PrePacket S P r K ∧
      (∀ i, Nonempty (↥(K i) ≃* alternatingGroup (Fin 4))) ∧
      (∀ i, K i ⊓ (⨆ j, ⨆ (_ : j ≠ i), K j) = ⊥)

@[expose] def NonsolvableActionSQT : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S P : Subgroup G), PushUpObstruction S P →
    ¬ Group.IsSolvable (autOn P (reducedModule S P)) →
    CFSG.IsStronglyQuasithin (autOn P (reducedModule S P))

@[expose] def NoAlt6Component : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (H T M E : Subgroup (MulAut V)),
    FFHyp V H T M E → ¬ Group.IsSolvable H → IsSQTKCat H →
    ∀ L : Subgroup (MulAut V), IsComp L H → ¬ Nonempty (CQ L ≃* alternatingGroup (Fin 6))

@[expose] def NoPSU33Component : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (H T M E : Subgroup (MulAut V)),
    FFHyp V H T M E → ¬ Group.IsSolvable H → IsSQTKCat H →
    ∀ L : Subgroup (MulAut V), IsComp L H → ¬ StatedClassicalModel (CQ L) .PSU 3 3 1

@[expose] def NoEvenUnitaryThreeComponent : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (H T M E : Subgroup (MulAut V)),
    FFHyp V H T M E → ¬ Group.IsSolvable H → IsSQTKCat H →
    ∀ L : Subgroup (MulAut V), IsComp L H → ∀ f : ℕ, 2 ≤ f →
      ¬ StatedClassicalModel (CQ L) .PSU 3 2 f

@[expose] def NoTrialityOrLargeReeComponent : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (H T M E : Subgroup (MulAut V)),
    FFHyp V H T M E → ¬ Group.IsSolvable H → IsSQTKCat H →
    ∀ L : Subgroup (MulAut V), IsComp L H →
      (∀ f : ℕ, 1 ≤ f → ¬ ChevalleyExceptionalModel (CQ L) .trialityD4 2 f) ∧
      (∀ f : ℕ, Odd f → 3 ≤ f → ¬ ReeTitsModel (CQ L) .twistedF4 2 f)

@[expose] def NoG2OrTitsComponent : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (H T M E : Subgroup (MulAut V)),
    FFHyp V H T M E → ¬ Group.IsSolvable H → IsSQTKCat H →
    ∀ L : Subgroup (MulAut V), IsComp L H →
      (∀ f : ℕ, 2 ≤ f → ¬ ChevalleyExceptionalModel (CQ L) .G2 2 f) ∧
      ¬ ReeTitsModel (CQ L) .Tits 2 1

@[expose] def NoPSL3Component : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (H T M E : Subgroup (MulAut V)),
    FFHyp V H T M E → ¬ Group.IsSolvable H → IsSQTKCat H →
    ∀ L : Subgroup (MulAut V), IsComp L H → ∀ f : ℕ, 2 ≤ f →
      ¬ StatedClassicalModel (CQ L) .PSL 3 2 f

@[expose] def NoPSp4Component : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (H T M E : Subgroup (MulAut V)),
    FFHyp V H T M E → ¬ Group.IsSolvable H → IsSQTKCat H →
    ∀ L : Subgroup (MulAut V), IsComp L H → ∀ f : ℕ, 2 ≤ f →
      ¬ StatedClassicalModel (CQ L) .PSp 2 2 f

end CFSG.QuasithinUnique.Setup.Top
