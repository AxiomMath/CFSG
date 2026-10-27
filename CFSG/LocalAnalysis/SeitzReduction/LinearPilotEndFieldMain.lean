module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotEndField
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotUniqueTypeDet
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotWeakCTGlobal

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem false_of_fieldNeighbourParam_levTorus_four
    (hset : CFSG.SeitzReduction.SeitzSetting G L) {f : ℕ} {K : Type} [Field K]
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* LinearFlag.projectiveSL 4 K) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {F : Type} [Field F] [Finite F] (ι : K →+* F) {σ : F ≃+* F} (hσ1 : σ ≠ 1)
    (hσσ : σ * σ = 1) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) {a : Fin 4}
    (hP : Nonempty (FieldNeighbourParam e t ι σ (modelToG e (levTorus (K := K) a)) ({a}ᶜ)))
    (h02 : pieceCore e ({0, 1} : Finset (Fin 4)) ≤
      centralizer (pieceCore e ({2, 3} : Finset (Fin 4)) : Set G))
    (hexcl : NonFieldInvolutionExclusion 4 K F σ) : False := by
  have : Finite K := finite_of_card_eq_two_pow hKc
  have hF : Nat.card F = 2 ^ (2 * f) := natCard_eq_two_pow_of_fixedField hKc ι hσ1 hσσ hfix
  have : CharP F 2 := charP_two_of_card_eq_two_pow hF
  have htC := mem_centralizer_of_inf_eq_zpowers hKt
  obtain ⟨hLG₀, htG₀, hq, -, -, ψ, -, hψt⟩ :=
    exists_globalField_levTorus_four hset hKc hf e htC ht ι hσ1 hσσ hfix hP h02 rfl
  exact false_of_globalField (m := 3) hset.standardSetting
    (isSolvable_outer_of_mulEquiv (by omega) e) (by omega) ι hσ1 hσσ hfix e ht hKt
    (fieldCoreTypeDet_of_nonFieldInvolutionExclusion (by omega) ι hfix hexcl) rfl hLG₀ htG₀ hq ψ
    hψt

end CFSG.SeitzReduction.LinearPilot
