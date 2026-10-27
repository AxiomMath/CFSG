module

public import CFSG.LocalAnalysis.OddStandard.Seitz77OddCoreSchur
public import CFSG.LocalAnalysis.OddStandard.Seitz77OddCoreCount

import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.OddStandard.Seitz77

open Polynomial

theorem oddCore_false_of_central_on_fixedPointFree {H : Type*} [Group H]
    {U : Type*} [AddCommGroup U] [Module (ZMod 2) U] [Finite U] [Nontrivial U]
    (θ : H →* Module.End (ZMod 2) U) (hperf : commutator H = ⊤)
    (μ : H) (hμ : ∀ g, g * μ = μ * g) (p : ℕ) (hp : p.Prime) (hμp : orderOf μ = p)
    (hpR : p ∣ 3 ^ 3 * 7 ^ 2 * 17 * 31 * 127) (b : ℕ) (hb : b = 4 ∨ b = 8)
    (hU : Module.finrank (ZMod 2) U = b)
    (hfix : ∀ u, θ μ u = u → u = 0) : False := by
  have hm : θ μ ^ p = 1 := by rw [← map_pow, ← hμp, pow_orderOf_eq_one, map_one]
  have hp' := oddCore_prime_dvd_R_B hp hpR
  have : Fact p.Prime := ⟨hp⟩
  have hfixsub : (⊤ : Submodule (ZMod 2) U) ⊓ LinearMap.ker (θ μ - 1) = ⊥ := by
    rw [top_inf_eq, eq_bot_iff]
    intro u hu
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hu
    exact (Submodule.mem_bot _).mpr (hfix u (by simpa using hu))
  have hdvd := oddCore_dvd_card_sub_one p (θ μ) hm ⊤ (fun _ _ => Submodule.mem_top) hfixsub
  rw [finrank_top, hU] at hdvd
  have hodd : Odd p := hp.odd_of_ne_two (by rcases hp' with h | h | h | h | h <;> omega)
  have hm1 : θ μ ≠ 1 := by
    intro h
    obtain ⟨u, hu⟩ := exists_ne (0 : U)
    exact hu (hfix u (by simp [h]))
  have hcases : p = 3 ∨ (p = 17 ∧ b = 8) := by
    rcases hp' with rfl | rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl <;>
      first | (left; rfl) | (right; exact ⟨rfl, rfl⟩) | (exfalso; norm_num at hdvd)
  have hdom : ∀ a ∈ Algebra.adjoin (ZMod 2) {θ μ}, a ≠ 0 → Function.Injective a := by
    rcases hcases with h3 | ⟨h17, h8⟩
    · subst h3
      have hroot : θ μ ^ 2 + θ μ + 1 = 0 := by
        ext u
        have h1 : θ μ ((θ μ ^ 2 + θ μ + 1 : Module.End (ZMod 2) U) u) =
            (θ μ ^ 2 + θ μ + 1 : Module.End (ZMod 2) U) u := by
          have e : θ μ * (θ μ ^ 2 + θ μ + 1) = θ μ ^ 2 + θ μ + 1 := by
            calc θ μ * (θ μ ^ 2 + θ μ + 1) = θ μ ^ 3 + θ μ ^ 2 + θ μ := by noncomm_ring
              _ = 1 + θ μ ^ 2 + θ μ := by rw [hm]
              _ = θ μ ^ 2 + θ μ + 1 := by abel
          have := congrArg (fun f : Module.End (ZMod 2) U => f u) e
          simpa using this
        have := hfix _ h1
        simpa using this
      have hroot' : aeval (θ μ) (X ^ 2 + X + 1 : (ZMod 2)[X]) = 0 := by simpa using hroot
      exact fun a ha ha0 => oddCore_injective_of_mem_adjoin_of_aeval (θ μ) _
        oddCore_irreducible_X_sq_add_X_add_one hroot' a ha ha0
    · subst h17
      subst h8
      have hirr := oddCore_eq_bot_or_eq_top_of_pow_seventeen hU (θ μ) hm hm1
      exact fun a ha ha0 =>
        oddCore_injective_of_mem_adjoin_of_irreducible (θ μ) (θ μ) rfl hirr a ha ha0
  have hj : ∃ j, Module.finrank (ZMod 2) U = 2 ^ j := by
    rcases hb with rfl | rfl
    · exact ⟨2, by rw [hU]; norm_num⟩
    · exact ⟨3, by rw [hU]; norm_num⟩
  obtain ⟨j, hj⟩ := hj
  have hodd' : Odd (orderOf μ) := hμp ▸ hodd
  exact hm1 (oddCore_eq_one_of_central_odd θ hperf μ hμ hdom j hj hodd')

end CFSG.OddStandard.Seitz77
