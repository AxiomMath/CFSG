module

public import CFSG.HardMathSupport.Timmesfeld.Proving.OmegaCentreZMod2
public import CFSG.HardMathSupport.Timmesfeld.Proving.OmegaEmbed
public import CFSG.ClassicalGroups.Orthogonal.Restrict
public import CFSG.ClassicalGroups.Orthogonal.Simple
public import CFSG.LieType.Universal.Spin.Forms
public import CFSG.Open.StatedDefs
public import CFSG.LocalAnalysis.GLTheoremB.UniqDefs
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCentralizer
public import CFSG.LieType.Universal.SpinOmega.Kernel
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.HardMathSupport.Timmesfeld.Proving

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.Assembly.LowTwoRank

theorem glaPPrimeCore_eq_bot_of_isSimpleGroup {p : ℕ} (hp : p.Prime) {K : Type*} [Group K]
    [Finite K] [IsSimpleGroup K] (hdvd : p ∣ Nat.card K) : GLAPPrimeCore p K = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (GLAPPrimeCore p K) with h | h
  · exact h
  · exfalso
    have hc := CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.coprime_card_GLAPPrimeCore hp K
    rw [h, Subgroup.card_top] at hc
    exact (Nat.Prime.coprime_iff_not_dvd hp).mp hc hdvd

end CFSG.HardMathSupport.Timmesfeld.Proving

end
