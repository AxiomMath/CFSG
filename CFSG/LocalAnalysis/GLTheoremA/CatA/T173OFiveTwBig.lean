module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveLayer
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotHR6X
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcE6TwistedLevi
public import CFSG.LieType.Chevalley.CLSEvenCoordinateFieldsFourGroup
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcAction
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcE6TwistedCent
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8Perfect
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8Swap
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalDefs
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviPerp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.E6GraphLevi
open CFSG.LieType.Chevalley.E6GraphHighestRoot CFSG.SeitzReduction.TwistedE6Pilot
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.ComponentClassification.RankTwoExceptional.TwistedE6Sec8

local notation "Γ₂" F => ModGL TwistTag.E6.tag F


theorem false_of_le_su6Levi {f : ℕ} (hf : 2 ≤ f) {k F : Type} [Field k] [Field F] [Algebra k F]
    [Finite F] (hk : Nat.card k = 2 ^ f) (hF : Nat.card F = (2 ^ f) ^ 2) {σ : F ≃+* F}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) {d : Γ₂ F} (hd : d ∈ twistedE6InndiagGL F σ) (hd1 : d ≠ 1)
    (hd3 : d ^ 3 = 1)
    (hdθ : d ∈ Subgroup.centralizer
      (E6GraphLevi.thetaRankOneGroup (algebraMap k F) : Set (Γ₂ F)))
    (hKL : stdLayerD (twistedE6RootGroup F σ) d ≤
      CFSG.SeitzReduction.TwistedE6Pilot.su6Levi σ.toRingHom) :
    False := by
  haveI : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have hf1 : 1 ≤ f := by omega
  have hk4 : 4 ≤ Nat.card k := by
    rw [hk]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have h2 : (2 : F) = 0 := E6GraphLevi.two_eq_zero_of_card_sq hf1 hF
  let J : Subgroup (Γ₂ F) := E6GraphLevi.thetaRankOneGroup (algebraMap k F)
  have hJroot : J ≤ twistedE6RootGroup F σ := by
    simpa [J] using CFSG.SeitzReduction.TwistedE6Pilot.thetaRankOneGroup_le_C0 hf1 hk hF hσ
  have hJd : J ≤ Subgroup.centralizer ({d} : Set (Γ₂ F)) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.1 hdθ x hx
  have hJperf : ⁅J, J⁆ = J :=
    commutator_thetaRankOneGroup_twisted (k := k) (K := F) h2 (algebraMap k F) hk4
  have hJle : J ≤ stdLayerD (twistedE6RootGroup F σ) d :=
    le_stdLayerD_twE6_of_perfect hf1 hF σ hσ hd hd1 hd3 hJroot hJd hJperf
  have hJsu6 : J ≤ CFSG.SeitzReduction.TwistedE6Pilot.su6Levi σ.toRingHom :=
    hJle.trans hKL
  have hJcent : J ≤ Subgroup.centralizer (J : Set (Γ₂ F)) := by
    have hsu6 :=
      (CFSG.SeitzReduction.TwistedE6Pilot.su6Levi_facts (σ := σ.toRingHom) hf1 hk hF hσ).1
    exact hJsu6.trans (by simpa [J] using hsu6)
  have hJbot : J = ⊥ := by
    rw [← hJperf]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 hJcent
  have hne : J ≠ ⊥ := by
    have hmem : pinnedX TwistTag.E6.tag F e6HighestRoot (1 : F) ∈ J := by
      refine (show E6GraphLevi.thetaRootGroup (algebraMap k F) ≤ J from le_sup_left) ?_
      rw [E6GraphLevi.mem_thetaRootGroup]
      exact ⟨1, by rw [map_one]⟩
    intro h
    exact pinnedX_one_ne_one e6HighestRoot (by simpa [h] using hmem)
  exact hne hJbot

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
