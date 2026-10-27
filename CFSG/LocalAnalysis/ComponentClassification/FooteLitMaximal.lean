module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCases
import CFSG.Foundations.GilmanSolomonGrammarChains
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

variable {G : Type*} [Group G]

@[expose] def oddCoreOfCentralizer (t : G) : Subgroup G :=
  (pPrimeCore 2 (centralizer ({t} : Set G))).map (centralizer ({t} : Set G)).subtype

@[expose] def footeFixed (L : Subgroup G) (t : G) : Subgroup G :=
  closure {g : G | g ∈ (L ⊓ centralizer ({t} : Set G)) ⊔ oddCoreOfCentralizer t ∧
    ∃ k : ℕ, orderOf g = 2 ^ k}

@[expose] def twoLayerOf (b : G) : Subgroup G :=
  (pLayer ↥(centralizer ({b} : Set G)) 2).map (centralizer ({b} : Set G)).subtype

@[expose] def conjClosure (Y E : Subgroup G) : Subgroup G :=
  closure (⋃ e ∈ (E : Set G), (conjugate Y e : Set G))

@[expose] def IsTwoComponentAt (a : G) (L : Subgroup G) : Prop :=
  orderOf a = 2 ∧ L ≤ centralizer ({a} : Set G) ∧
    IsPComponent 2 (L.subgroupOf (centralizer ({a} : Set G)))

@[expose] def FooteStep (L K : Subgroup G) : Prop :=
  ∃ a b : G, IsTwoComponentAt a L ∧ IsTwoComponentAt b K ∧ a * b = b * a ∧ a ≠ b ∧
    b ∈ coreActionKernel L ∧
    conjClosure (footeFixed L b) (twoLayerOf b) = K ⊔ conjugate K a

@[expose] def FooteReach (L M : Subgroup G) : Prop :=
  Relation.ReflTransGen FooteStep L M

@[expose] def FooteMaximal (L : Subgroup G) : Prop :=
  gs_grammar% GSGrammar.MaximalComponent (fun L => ∃ a : G, IsTwoComponentAt a L) FooteReach
    (fun H => Open.fusionZStar H) L

@[expose] def FooteMaximalInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X →
    ∀ x : X, orderOf x = 2 → ∀ L : Subgroup X, L ≤ centralizer ({x} : Set X) →
    IsPComponent 2 (L.subgroupOf (centralizer ({x} : Set X))) → FooteMaximal L →
    FooteType L →
    Blueprint.OddLieType X ∨ CFSG.pRank 2 ↥(coreActionKernel L) = 1 ∨ FooteExceptional X L

theorem FooteStep.source {L K : Subgroup G} (h : FooteStep L K) : ∃ a : G, IsTwoComponentAt a L :=
  let ⟨a, _, ha, _⟩ := h
  ⟨a, ha⟩

theorem FooteStep.target {L K : Subgroup G} (h : FooteStep L K) : ∃ b : G, IsTwoComponentAt b K :=
  let ⟨_, b, _, hb, _⟩ := h
  ⟨b, hb⟩

theorem FooteReach.trans {L M N : Subgroup G} (h₁ : FooteReach L M) (h₂ : FooteReach M N) :
    FooteReach L N :=
  Relation.ReflTransGen.trans h₁ h₂

theorem FooteReach.target {L M : Subgroup G} (hL : ∃ a : G, IsTwoComponentAt a L)
    (h : FooteReach L M) : ∃ b : G, IsTwoComponentAt b M := by
  rcases Relation.ReflTransGen.cases_tail h with rfl | ⟨K, -, hKM⟩
  · exact hL
  · exact hKM.target

theorem FooteMaximal.of_reach {L M : Subgroup G} (hL : FooteMaximal L) (h : FooteReach L M) :
    FooteMaximal M :=
  GSGrammar.MaximalComponent.of_rel (vertex := fun L => ∃ a : G, IsTwoComponentAt a L)
    (reach := FooteReach) (zstar := fun H => Open.fusionZStar H) hL
    (fun _ _ _ => FooteReach.trans) h (h.target hL.1)

theorem FooteMaximal.equiv_of_reach {L M : Subgroup G} (hL : FooteMaximal L)
    (h : FooteReach L M) : Nonempty (L ⧸ Open.fusionZStar L ≃* M ⧸ Open.fusionZStar M) :=
  hL.2 M h

end CFSG.ComponentClassification.FooteLit
