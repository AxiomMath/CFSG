module

public import CFSG.GF2Type.Smith1980Orth.W4SigmaGL

public section

namespace CFSG.GF2Type.Smith1979.W4As.Surv

open Subgroup Module

theorem prod_gl_eight :
    ∏ i : Fin 8, (2 ^ 8 - 2 ^ (i : ℕ)) = 2 ^ 28 * 3 ^ 5 * 5 ^ 2 * 7 ^ 2 * 17 * 31 * 127 := by
  simp [Fin.prod_univ_succ]

theorem card_quotient_center_dvd_gl_eight {K : Type} [Group K] [Finite K] {V : Type}
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (hV : finrank (ZMod 2) V = 8) (ρ : K →* (V ≃ₗ[ZMod 2] V)) (hρ : Function.Injective ρ) :
    Nat.card (K ⧸ center K) ∣ 2 ^ 28 * 3 ^ 5 * 5 ^ 2 * 7 ^ 2 * 17 * 31 * 127 := by
  rw [← prod_gl_eight, ← CFSG.GF2Type.Smith1980Orth.W4Sigma.card_linearEquiv_eq_prod hV]
  exact (Subgroup.card_quotient_dvd_card (center K)).trans (Subgroup.card_dvd_of_injective ρ hρ)

end CFSG.GF2Type.Smith1979.W4As.Surv
