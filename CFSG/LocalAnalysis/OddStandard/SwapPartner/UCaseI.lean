module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.InputLShape
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.UAction

import CFSG.LocalAnalysis.OddStandard.SwapPartner.TrichotomySetup

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup

open scoped commutatorElement

theorem false_of_normal_abar {X : Type} [Group X] [Finite X] {t : X} {Sg V : Subgroup X}
    (h : SwapShape t Sg V) [(⁅Sg, Sg⁆ : Subgroup X).Normal]
    (h4 : ∀ U : Subgroup X, IsPGroup 2 U →
      U ≤ centralizer ((⁅Sg, Sg⁆ : Subgroup X) : Set X) → Nat.card U ≤ 4)
    (h10 : 2 ^ 10 ∣ Nat.card X) : False := by
  classical
  haveI hperf : Group.IsPerfect ↥(⁅Sg, Sg⁆ : Subgroup X) := h.isQuasisimple_abar.1
  obtain ⟨e₀⟩ := h.nonempty_equiv_abar
  let e : (↥(⁅Sg, Sg⁆ : Subgroup X) ⧸ center ↥(⁅Sg, Sg⁆ : Subgroup X)) ≃*
      alternatingGroup (Fin 8) :=
    (QuotientGroup.quotientMulEquivOfEq h.center_abar_eq_bot).trans
      (QuotientGroup.quotientBot.trans e₀)
  exact false_of_alternating_action (⁅Sg, Sg⁆ : Subgroup X) (n := 8) (b := 2) (k := 10)
    (by norm_num) (by norm_num) e (by
      intro U hU hle
      have h := h4 U hU hle
      norm_num at h ⊢
      exact h) h10 (by rw [padicValNat_two_factorial_eight]; norm_num)

end CFSG.OddStandard.AltStdSec.SwapPartner
