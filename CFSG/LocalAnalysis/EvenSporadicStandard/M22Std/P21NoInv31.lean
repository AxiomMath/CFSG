module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.P21F31

public section

namespace CFSG.EvenSporadicStandard.M22Std

section

variable {V : Type} [CommGroup V] [Module (ZMod 2) (Additive V)]

@[expose] noncomputable def linOfAut (α : MulAut V) : Additive V ≃ₗ[ZMod 2] Additive V :=
  AddEquiv.toLinearEquiv α.toAdditive (fun c x => ZMod.map_smul α.toAdditive c x)

@[expose] noncomputable def repAut : MulAut V →* Module.End (ZMod 2) (Additive V) where
  toFun α := (linOfAut α : Module.End (ZMod 2) (Additive V))
  map_one' := rfl
  map_mul' _ _ := rfl

theorem repAut_injective : Function.Injective (repAut (V := V)) := by
  intro α β h
  ext v
  have := congrArg (fun T => T (Additive.ofMul v)) h
  simpa [repAut, linOfAut] using this

theorem no_inv_order_31 (hcard : Nat.card V = 256) {G : Type} [Group G] (ρ : G →* MulAut V)
    (hρ : Function.Injective ρ) (x t : G) (hx : x ^ 31 = 1) (hx1 : x ≠ 1)
    (ht : t * x * t⁻¹ = x⁻¹) : False := by
  have hfin : Finite V := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hfin' : Finite (Additive V) := hfin
  have hdim : Module.finrank (ZMod 2) (Additive V) ≤ 8 := by
    have : Module.Finite (ZMod 2) (Additive V) := Module.Finite.of_finite
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    have hc : Nat.card (Additive V) = 256 := hcard
    rw [hc, Nat.card_zmod] at h
    have : (2 : ℕ) ^ Module.finrank (ZMod 2) (Additive V) = 2 ^ 8 := by rw [← h]; norm_num
    exact (Nat.pow_right_injective le_rfl this).le
  let r : G →* Module.End (ZMod 2) (Additive V) := repAut.comp ρ
  have hr : Function.Injective r := repAut_injective.comp hρ
  refine P21Field.not_inv_conj_31 hdim (r x) (r t) (r t⁻¹) (by rw [← map_pow, hx, map_one])
    (fun h => hx1 (hr (by rw [h, map_one]))) (by rw [← map_mul, mul_inv_cancel, map_one])
    (by rw [← map_mul, inv_mul_cancel, map_one]) ?_
  have h1 : t * x = x ^ 30 * t := by
    have hx30 : x⁻¹ = x ^ 30 := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ', hx]
    calc t * x = (t * x * t⁻¹) * t := by group
      _ = x⁻¹ * t := by rw [ht]
      _ = x ^ 30 * t := by rw [hx30]
  rw [← map_mul, h1, map_mul, map_pow]

end

end CFSG.EvenSporadicStandard.M22Std
