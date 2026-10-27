module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitWeakCorr

public section

namespace CFSG.ComponentClassification.FooteMarked

open CFSG Subgroup
open CFSG.ComponentClassification.FooteLit
open CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.UnbalancedGS

variable {G : Type*} [Group G]

@[expose] noncomputable def fixedShadow (M U : Subgroup G) : Subgroup G :=
  (CFSG.perfectResidual ↥(M ⊓ centralizer (U : Set G))).map
    (M ⊓ centralizer (U : Set G)).subtype

@[expose] noncomputable def fixedShadowAt (M : Subgroup G) (u : G) : Subgroup G :=
  (CFSG.perfectResidual ↥(M ⊓ centralizer ({u} : Set G))).map
    (M ⊓ centralizer ({u} : Set G)).subtype

theorem fixedShadow_zpowers (M : Subgroup G) (u : G) :
    fixedShadow M (zpowers u) = fixedShadowAt M u := by
  rw [fixedShadow, fixedShadowAt, centralizer_zpowers_eq]

theorem fixedShadow_le (M U : Subgroup G) : fixedShadow M U ≤ M :=
  (map_subtype_le _).trans inf_le_left

theorem fixedShadowAt_le (M : Subgroup G) (u : G) : fixedShadowAt M u ≤ M :=
  (map_subtype_le _).trans inf_le_left

@[expose] noncomputable def Marked (S : Set (Subgroup G)) (T : Type*) [Group T]
    (M : Subgroup G) : Prop :=
  Group.IsPerfect M ∧ Nonempty (M ⧸ pPrimeCore 2 M ≃* T) ∧
    ∃ a : G, orderOf a = 2 ∧ a ∈ UnbalancedLayer.coreActionKernel M ∧
      ∃ Sa : Subgroup G, Sa ∈ S ∧
        fixedShadowAt M a ⊔ FooteLit.oddCoreOfCentralizer a =
          Sa ⊔ FooteLit.oddCoreOfCentralizer a

@[expose] def IsomorphicFamily (S : Set (Subgroup G)) (T : Type*) [Group T] : Prop :=
  (∀ J ∈ S, ∃ a : G, FooteLit.IsTwoComponentAt a J) ∧
  (∀ J ∈ S, Nonempty (J ⧸ pPrimeCore 2 J ≃* T)) ∧
  (∀ J ∈ S, ∀ g : G, conjugate J g ∈ S) ∧
  ∀ (a b : G) (J : Subgroup G), J ∈ S → ∀ K : Subgroup G,
    GrSLit.GSWeakCorr a J b K →
      K ∈ S ∧ conjugate K a = K ∧
        UnbalancedGS.gsFixedLayer J b ⊔ FooteLit.oddCoreIn K = K

@[expose] def MarkedST (S : Set (Subgroup G)) (T : Type*) [Group T] : Prop :=
  ∀ M : Subgroup G, Marked S T M → ∀ U : Subgroup G,
    IsPGroup 2 U → U ≤ UnbalancedLayer.coreActionKernel M → U ≠ ⊥ →
      ∃ L : Subgroup G,
        FooteLit.IsTwoComponentIn L (centralizer (U : Set G)) ∧ Marked S T L ∧
          FooteLit.conjClosure (fixedShadow M U)
            (FooteLit.twoLayerIn (centralizer (U : Set G))) = L ∧
          fixedShadow M U ⊔ FooteLit.oddCoreIn L = L

@[expose] noncomputable def ambientCanonicalLift (X : Subgroup G)
    (A : Subgroup (X ⧸ pPrimeCore 2 X)) : Subgroup G :=
  (CatalogueBPrimeJoin.canonicalPrimeLift 2 A).map X.subtype

theorem ambientCanonicalLift_subgroupOf (X : Subgroup G)
    (A : Subgroup (X ⧸ pPrimeCore 2 X)) :
    (ambientCanonicalLift X A).subgroupOf X = CatalogueBPrimeJoin.canonicalPrimeLift 2 A := by
  rw [ambientCanonicalLift]
  apply Subgroup.map_injective X.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le
    (map_subtype_le (CatalogueBPrimeJoin.canonicalPrimeLift 2 A))]

theorem ambientCanonicalLift_le (X : Subgroup G) (A : Subgroup (X ⧸ pPrimeCore 2 X)) :
    ambientCanonicalLift X A ≤ X :=
  map_subtype_le _

theorem ambientCanonicalLift_isTwoComponentIn {X : Subgroup G} [Finite X]
    {A : Subgroup (X ⧸ pPrimeCore 2 X)} (hA : IsComponent A) :
    FooteLit.IsTwoComponentIn (ambientCanonicalLift X A) X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨ambientCanonicalLift_le X A, ?_⟩
  rw [ambientCanonicalLift_subgroupOf]
  exact (CatalogueBPrimeJoin.canonicalPrimeLift_isPComponent 2 A hA).1

theorem ambientCanonicalLift_map_quotient {X : Subgroup G} [Finite X]
    {A : Subgroup (X ⧸ pPrimeCore 2 X)} (hA : IsComponent A) :
    ((ambientCanonicalLift X A).subgroupOf X).map
        (QuotientGroup.mk' (pPrimeCore 2 X)) = A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [ambientCanonicalLift_subgroupOf]
  exact (CatalogueBPrimeJoin.canonicalPrimeLift_isPComponent 2 A hA).2

@[expose] noncomputable def canonicalPerfectLift {G : Type} [Group G] (X : Subgroup G)
    (A : Subgroup (X ⧸ pPrimeCore 2 X)) : Subgroup G :=
  ((CFSG.perfectResidual ↥(A.comap (QuotientGroup.mk' (pPrimeCore 2 X)))).map
    (A.comap (QuotientGroup.mk' (pPrimeCore 2 X))).subtype).map X.subtype

@[expose] def markedComponents (S : Set (Subgroup G)) (T : Type*) [Group T]
    (X : Subgroup G) : Set (Subgroup G) :=
  {K | FooteLit.IsTwoComponentIn K X ∧ Marked S T K}

@[expose] noncomputable def markedLayer (S : Set (Subgroup G)) (T : Type*) [Group T]
    (X : Subgroup G) : Subgroup G :=
  sSup (markedComponents S T X)

@[expose] noncomputable def markedCount (S : Set (Subgroup G)) (T : Type*) [Group T]
    (X : Subgroup G) : ℕ :=
  (markedComponents S T X).ncard

@[expose] def base (X : Subgroup G) : Subgroup G :=
  FooteLit.oddTwoCoreIn X ⊔ FooteLit.twoLayerIn X

@[expose] noncomputable def wholeKernel (S : Set (Subgroup G)) (T : Type*) [Group T]
    (X : Subgroup G) : Subgroup G :=
  X ⊓ UnbalancedLayer.coreActionKernel (markedLayer S T X)

@[expose] noncomputable def baseKernel (S : Set (Subgroup G)) (T : Type*) [Group T]
    (X : Subgroup G) : Subgroup G :=
  base X ⊓ UnbalancedLayer.coreActionKernel (markedLayer S T X)

@[expose] noncomputable def Balanced (S : Set (Subgroup G)) (T : Type*) [Group T]
    (X : Subgroup G) : Prop :=
  2 ≤ markedCount S T X ∧
    (3 ≤ markedCount S T X ∨ Even (Nat.card (baseKernel S T X)))

theorem markedComponents_subset (S : Set (Subgroup G)) (T : Type*) [Group T]
    (X : Subgroup G) : markedComponents S T X ⊆ {K | FooteLit.IsTwoComponentIn K X} :=
  fun _ hK => hK.1

theorem markedLayer_le (S : Set (Subgroup G)) (T : Type*) [Group T] (X : Subgroup G) :
    markedLayer S T X ≤ X := by
  refine sSup_le ?_
  rintro K ⟨hKX, -⟩
  exact hKX.1

theorem base_le (X : Subgroup G) : base X ≤ X := by
  simp only [base, FooteLit.oddTwoCoreIn, FooteLit.twoLayerIn]
  exact sup_le (map_subtype_le _) (map_subtype_le _)

theorem baseKernel_le (S : Set (Subgroup G)) (T : Type*) [Group T] (X : Subgroup G) :
    baseKernel S T X ≤ X :=
  inf_le_left.trans (base_le X)

section Finite

variable [Finite G]

@[expose] noncomputable def IsMarkedChoice (S : Set (Subgroup G)) (T : Type*) [Group T]
    (N : Subgroup G) : Prop :=
  Balanced S T N ∧
    (∀ X : Subgroup G, Balanced S T X → markedCount S T X ≤ markedCount S T N) ∧
    (∀ X : Subgroup G, Balanced S T X → markedCount S T X = markedCount S T N →
      CFSG.Open.twoRank ↥(wholeKernel S T X) ≤
        CFSG.Open.twoRank ↥(wholeKernel S T N)) ∧
    ∀ X : Subgroup G, Balanced S T X → markedCount S T X = markedCount S T N →
      CFSG.Open.twoRank ↥(wholeKernel S T X) =
          CFSG.Open.twoRank ↥(wholeKernel S T N) →
        2 ^ (Nat.card (wholeKernel S T X)).factorization 2 ≤
          2 ^ (Nat.card (wholeKernel S T N)).factorization 2

theorem IsMarkedChoice.balanced {S : Set (Subgroup G)} {T : Type*} [Group T]
    {N : Subgroup G} (hN : IsMarkedChoice S T N) : Balanced S T N :=
  hN.1

theorem IsMarkedChoice.markedCount_le {S : Set (Subgroup G)} {T : Type*} [Group T]
    {N : Subgroup G} (hN : IsMarkedChoice S T N) {X : Subgroup G} (hX : Balanced S T X) :
    markedCount S T X ≤ markedCount S T N :=
  hN.2.1 X hX

end Finite

end CFSG.ComponentClassification.FooteMarked
