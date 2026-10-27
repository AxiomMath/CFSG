module

public import CFSG.LieType.Steinberg.CentralExt.SUOddClosed
public import CFSG.LieType.Steinberg.CentralExt.GriessClassical
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication

public section

open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier

namespace CFSG.LieType.Steinberg.CentralExt.GriessClassical

variable {X : Type} [Group X] {n p f : ℕ}

theorem exceptionalOrders_PSU_odd (ho : ¬ Even n) : exceptionalOrders .PSU n p f = (1, 1) := by
  have h4 : n ≠ 4 := by
    rintro rfl
    exact ho (by decide)
  have h6 : n ≠ 6 := by
    rintro rfl
    exact ho (by decide)
  unfold exceptionalOrders
  split <;> simp_all

theorem psu_odd_row
    (h : StatedClassicalModel X .PSU n p f) (ho : ¬ Even n) :
    commutator X = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier X ≃* generic .PSU n p f × exceptional .PSU n p f) := by
  obtain ⟨⟨hp, hf, hn, hq⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := CFSG.LieType.Steinberg.charP_of_card_eq_sq_pow hp hK
  refine of_mulEquiv e (of_mulEquiv_target ?_ (SUOdd.psu_odd_hopfMultiplier hK hf hn ho hq))
  exact (padOne _).trans (toGenEx (t := .PSU) (n := n) (p := p) (f := f)
    (a₁ := Nat.gcd n (p ^ f + 1)) (a₂ := 1) (b₁ := 1) (b₂ := 1) (by simp [genericOrders])
    (exceptionalOrders_PSU_odd ho))
