module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltSmallFacts

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm

@[expose] def Basic5 (x : Perm (Fin 5)) : Prop :=
  x ^ 3 = 1 ∧ x ≠ 1 ∧ (c5_234 * x) ^ 2 = 1 ∧ x ≠ c5_234⁻¹

instance (x : Perm (Fin 5)) : Decidable (Basic5 x) := by unfold Basic5; infer_instance

@[expose] def Conj5 (ζ x x' : Perm (Fin 5)) : Prop :=
  x' ≠ x → x' ≠ x⁻¹ → (x * x') ^ 2 = 1 → ζ * x' * ζ⁻¹ = x'⁻¹ →
    ζ * x * ζ⁻¹ ≠ c5_234⁻¹ * x ∧ ζ * x * ζ⁻¹ ≠ x * c5_234⁻¹

instance (ζ x x' : Perm (Fin 5)) : Decidable (Conj5 ζ x x') := by unfold Conj5; infer_instance

theorem conj_ne_five_aux : ∀ ζ : Perm (Fin 5), ζ * c5_234 * ζ⁻¹ = c5_234⁻¹ →
    ∀ x : Perm (Fin 5), Basic5 x → ∀ x' : Perm (Fin 5), Basic5 x' → Conj5 ζ x x' := by
  decide +kernel

theorem conj_ne_five {u ζ x x' : Perm (Fin 5)} (hu3 : u ^ 3 = 1) (hu1 : u ≠ 1)
    (hζu : ζ * u * ζ⁻¹ = u⁻¹) (hx : x ^ 3 = 1 ∧ x ≠ 1 ∧ (u * x) ^ 2 = 1 ∧ x ≠ u⁻¹)
    (hx' : x' ^ 3 = 1 ∧ x' ≠ 1 ∧ (u * x') ^ 2 = 1 ∧ x' ≠ u⁻¹) (h1 : x' ≠ x) (h2 : x' ≠ x⁻¹)
    (h3 : (x * x') ^ 2 = 1) (hζx' : ζ * x' * ζ⁻¹ = x'⁻¹) :
    ζ * x * ζ⁻¹ ≠ u⁻¹ * x ∧ ζ * x * ζ⁻¹ ≠ x * u⁻¹ := by
  have hc : c5_234.IsThreeCycle := card_support_eq_three_iff.mp (by decide)
  obtain ⟨τ, hτ⟩ : ∃ τ : Perm (Fin 5), τ * u * τ⁻¹ = c5_234 :=
    isConj_iff.mp (isConj_iff_cycleType_eq.mpr
      (Eq.trans (isThreeCycle_of_pow_three_five hu3 hu1) hc.symm))
  set f : MulAut (Perm (Fin 5)) := MulAut.conj τ with hfdef
  have hfu : f u = c5_234 := by rw [hfdef, MulAut.conj_apply, hτ]
  have tr : ∀ a : Perm (Fin 5), (a ^ 3 = 1 ∧ a ≠ 1 ∧ (u * a) ^ 2 = 1 ∧ a ≠ u⁻¹) →
      Basic5 (f a) := by
    rintro a ⟨e1, e2, e4, e5⟩
    exact ⟨by rw [← map_pow, e1, map_one], fun h => e2 (f.injective (by rw [h, map_one])),
      by rw [← hfu, ← map_mul, ← map_pow, e4, map_one],
      fun h => e5 (f.injective (by rw [h, map_inv, hfu]))⟩
  have hζ' : f ζ * c5_234 * (f ζ)⁻¹ = c5_234⁻¹ := by
    rw [← hfu, ← map_inv, ← map_mul, ← map_mul, hζu, map_inv]
  have key := conj_ne_five_aux (f ζ) hζ' (f x) (tr x hx) (f x') (tr x' hx')
    (fun h => h1 (f.injective h)) (fun h => h2 (f.injective (by rw [h, map_inv])))
    (by rw [← map_mul, ← map_pow, h3, map_one])
    (by rw [← map_inv, ← map_mul, ← map_mul, hζx', map_inv])
  rw [← hfu, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_mul] at key
  exact ⟨fun h => key.1 (by rw [h]), fun h => key.2 (by rw [h])⟩

end CFSG.ComponentClassification.RankTwoAlt
