module

public import CFSG.LocalAnalysis.GLTheoremA.S4S.Inputs
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3Bridge
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open

@[expose] def GWLBalanceClause3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], lBalanceIsKGroup X → ∀ p : ℕ, p.Prime →
    ∀ P : Subgroup X, IsPGroup p P →
      lBalancePrimeCore p (⊤ : Subgroup X) = ⊥ →
      ∀ a ∈ lBalancePLayer p (Subgroup.normalizer (P : Set X)),
        ∀ b ∈ lBalancePrimeCore p (Subgroup.normalizer (P : Set X)), a * b = b * a

theorem input14_5Print_of_gw (h : GWLBalanceClause3) : Input14_5Print := by
  intro X _ _ hK p hp _ hcore P _ hP
  have hcore' : lBalancePrimeCore p (⊤ : Subgroup X) = ⊥ :=
    (CFSG.ComponentClassification.LBalance.primeCore_top (G := X) p).trans hcore
  have hO : GLAPPrimeCoreOf p (Subgroup.normalizer (P : Set X)) =
      lBalancePrimeCore p (Subgroup.normalizer (P : Set X)) :=
    (CFSG.ComponentClassification.LBalance.primeCore_eq_map p
      (Subgroup.normalizer (P : Set X))).symm
  have hcomm := h X hK p hp P hP hcore'
  rw [CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPLayer_eq, hO,
    Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  exact (hcomm a ha b hb).symm

end CFSG.LocalAnalysis.GLTheoremA
