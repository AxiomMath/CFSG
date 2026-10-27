module

public import CFSG.ClassicalInvolution.MilestoneAssemblyCore
public import CFSG.ClassicalInvolution.MainReduction
public import CFSG.ClassicalInvolution.Generic.StepPerfect
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Induction
public import CFSG.ClassicalInvolution.OrderForm
public import CFSG.ClassicalInvolution.Orders.OddLieType
public import CFSG.ClassicalInvolution.SolvableCase.M12

public section

namespace CFSG.ClassicalInvolution.MilestoneAssembly

open CFSG.Open CFSG.ClassicalInvolution.Hat2A7

theorem cit2A7Case_of_inductive2A7 (h : CITInductive2A7) : Generic.CIT2A7Case := by
  intro F _ _ _ hnab z hz K hzK hK hw _
  obtain ⟨L, hL⟩ := exists_isClassical2A7_of_witness hz hzK hK hw
  exact (false_of_inductive2A7 h hnab hL).elim

theorem cit2A7Case_of_inputs (GS : GoldschmidtMilestone) (TW : TwinExclusion)
    (LOC : LocalOddCentralStep2A7) (red : StepReduction2A7) : Generic.CIT2A7Case :=
  cit2A7Case_of_inductive2A7 (citInductive2A7_of_step
    (red (coreStep2A7_of_inputs (goldschmidtStronglyClosedExponent_of_milestone GS) TW LOC)))

theorem partOneSolvable_of_inputs (hB : NormalOddByQuaternion) (hn : PartOneSolvableNonTight) :
    PartOneSolvable :=
  partOneSolvable_of_tight_of_nonTight
    (partOneSolvableTight_of_normalOddByQuaternion hB m12NoSolvableTightClassical) hn

theorem citSimplePerfect_of_open
    (hMFZ : ∀ (p : ℕ) [Fact p.Prime], RouteD.Gaps.FundNoncentral p)
    (hcore : ∀ (p f : ℕ) [Fact p.Prime], CoreOpen p f)
    (hexc : ∀ (p f : ℕ) [Fact p.Prime], ModelFacts.ClassicalMembersFundamentalExc p f)
    (GS : GoldschmidtMilestone) (TW : TwinExclusion) (LOC : LocalOddCentralStep2A7)
    (red : StepReduction2A7) : CITSimplePerfect :=
  Generic.citSimplePerfect_of_cases
    (Generic.citSimplePerfectSL2_of_citInductiveU
      (fun p f _ => citInductiveU_of_open (hMFZ p) (hcore p f) (hexc p f))
      ModelFacts.modelClauseZero)
    (cit2A7Case_of_inputs GS TW LOC red)

structure MilestoneInputs : Prop where
  mfz : ∀ (p : ℕ) [Fact p.Prime], RouteD.Gaps.FundNoncentral p
  core : ∀ (p f : ℕ) [Fact p.Prime], CoreOpen p f
  exc : ∀ (p f : ℕ) [Fact p.Prime], ModelFacts.ClassicalMembersFundamentalExc p f
  goldschmidt : GoldschmidtMilestone
  twin : TwinExclusion
  localOddCentral2A7 : LocalOddCentralStep2A7
  stepReduction2A7 : StepReduction2A7
  nonTight : PartOneSolvableNonTight
  normalOddByQuaternion : NormalOddByQuaternion

theorem models_of_named_inputs
    (hMFZ : ∀ (p : ℕ) [Fact p.Prime], RouteD.Gaps.FundNoncentral p)
    (hcore : ∀ (p f : ℕ) [Fact p.Prime], CoreOpen p f)
    (hexc : ∀ (p f : ℕ) [Fact p.Prime], ModelFacts.ClassicalMembersFundamentalExc p f)
    (GS : GoldschmidtMilestone) (TW : TwinExclusion) (LOC : LocalOddCentralStep2A7)
    (red : StepReduction2A7) (hNT : PartOneSolvableNonTight) (hB : NormalOddByQuaternion)
    (G : Type) [Group G] [Finite G]
    [IsSimpleGroup (genFittingFStar G)]
    (hFnonab : ∃ a b : genFittingFStar G, a * b ≠ b * a)
    (z : G) (hz : orderOf z = 2)
    (J : Subgroup G) (hzJ : z ∈ J) (hJ : IsSubnormal J (Subgroup.centralizer ({z} : Set G)))
    (S : Sylow 2 J)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    (classicalInvolutionWitness J → CFSG.Blueprint.OddLieType (genFittingFStar G) ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic (genFittingFStar G) .M11) ∧
    (classicalInvolutionTightlyEmbedded J → CFSG.Blueprint.OddLieType (genFittingFStar G) ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic (genFittingFStar G) .M11 ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic (genFittingFStar G) .M12) :=
  models_of_citSimplePerfect (citSimplePerfect_of_open hMFZ hcore hexc GS TW LOC red)
    (partOneSolvable_of_inputs hB hNT) hB G hFnonab z hz J hzJ hJ S hS

theorem order_of_named_inputs
    (hMFZ : ∀ (p : ℕ) [Fact p.Prime], RouteD.Gaps.FundNoncentral p)
    (hcore : ∀ (p f : ℕ) [Fact p.Prime], CoreOpen p f)
    (hexc : ∀ (p f : ℕ) [Fact p.Prime], ModelFacts.ClassicalMembersFundamentalExc p f)
    (GS : GoldschmidtMilestone) (TW : TwinExclusion) (LOC : LocalOddCentralStep2A7)
    (red : StepReduction2A7) (hNT : PartOneSolvableNonTight) (hB : NormalOddByQuaternion)
    (G : Type) [Group G] [Finite G]
    (F : Subgroup G) [F.Normal] [IsSimpleGroup F]
    (hFnonab : ∃ a b : F, a * b ≠ b * a)
    (hFstar : Subgroup.centralizer (F : Set G) = ⊥)
    (z : G) (hz : orderOf z = 2)
    (J : Subgroup G) (hzJ : z ∈ J) (hJ : IsSubnormal J (Subgroup.centralizer ({z} : Set G)))
    (S : Sylow 2 J)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    (classicalInvolutionWitness J →
      (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ Nat.card F ∈ lieOrdersChar p) ∨ Nonempty (F ≃* M11)) ∧
    (classicalInvolutionTightlyEmbedded J →
      (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ Nat.card F ∈ lieOrdersChar p) ∨ Nonempty (F ≃* M11) ∨
        Nonempty (F ≃* classicalInvolutionM12)) :=
  orderForm_of_modelsForm (fun _ _ h => card_mem_lieOrdersChar_of_oddLieType h)
    (fun G _ _ _ hFnonab z hz J hzJ hJ S hS =>
      models_of_named_inputs hMFZ hcore hexc GS TW LOC red hNT hB G hFnonab z hz J hzJ hJ S hS)
    G F hFnonab hFstar z hz J hzJ hJ S hS

theorem MilestoneInputs.models (h : MilestoneInputs)
    (G : Type) [Group G] [Finite G]
    [IsSimpleGroup (genFittingFStar G)]
    (hFnonab : ∃ a b : genFittingFStar G, a * b ≠ b * a)
    (z : G) (hz : orderOf z = 2)
    (J : Subgroup G) (hzJ : z ∈ J) (hJ : IsSubnormal J (Subgroup.centralizer ({z} : Set G)))
    (S : Sylow 2 J)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    (classicalInvolutionWitness J → CFSG.Blueprint.OddLieType (genFittingFStar G) ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic (genFittingFStar G) .M11) ∧
    (classicalInvolutionTightlyEmbedded J → CFSG.Blueprint.OddLieType (genFittingFStar G) ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic (genFittingFStar G) .M11 ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic (genFittingFStar G) .M12) :=
  models_of_named_inputs h.mfz h.core h.exc h.goldschmidt h.twin h.localOddCentral2A7
    h.stepReduction2A7 h.nonTight h.normalOddByQuaternion G hFnonab z hz J hzJ hJ S hS

theorem MilestoneInputs.order (h : MilestoneInputs)
    (G : Type) [Group G] [Finite G]
    (F : Subgroup G) [F.Normal] [IsSimpleGroup F]
    (hFnonab : ∃ a b : F, a * b ≠ b * a)
    (hFstar : Subgroup.centralizer (F : Set G) = ⊥)
    (z : G) (hz : orderOf z = 2)
    (J : Subgroup G) (hzJ : z ∈ J) (hJ : IsSubnormal J (Subgroup.centralizer ({z} : Set G)))
    (S : Sylow 2 J)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    (classicalInvolutionWitness J →
      (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ Nat.card F ∈ lieOrdersChar p) ∨ Nonempty (F ≃* M11)) ∧
    (classicalInvolutionTightlyEmbedded J →
      (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ Nat.card F ∈ lieOrdersChar p) ∨ Nonempty (F ≃* M11) ∨
        Nonempty (F ≃* classicalInvolutionM12)) :=
  order_of_named_inputs h.mfz h.core h.exc h.goldschmidt h.twin h.localOddCentral2A7
    h.stepReduction2A7 h.nonTight h.normalOddByQuaternion G F hFnonab hFstar z hz J hzJ hJ S hS

end CFSG.ClassicalInvolution.MilestoneAssembly
