module

public import CFSG.FeitThompson.Foundations.CyclotomicIntegerFactorization

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Polynomial

theorem map_rat_cyclotomic_eq_primitiveRootFactorProd (n : ℕ) :
    (cyclotomic n ℚ).map (algebraMap ℚ ℂ) = primitiveRootFactorProd n := by
  rw [map_cyclotomic, primitiveRootFactorProd_eq_cyclotomic]

theorem eq_cyclotomic_rat_of_map_eq_primitiveRootFactorProd {n : ℕ} {P : ℚ[X]}
    (hP : P.map (algebraMap ℚ ℂ) = primitiveRootFactorProd n) : P = cyclotomic n ℚ :=
  map_injective (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective
    (by rw [hP, map_rat_cyclotomic_eq_primitiveRootFactorProd])

theorem degree_pos_and_ne_mul_of_degree_pos_cyclotomic_rat {n : ℕ} (hn : 0 < n) :
    0 < (cyclotomic n ℚ).degree ∧
      ∀ f g : ℚ[X], 0 < f.degree → 0 < g.degree → cyclotomic n ℚ ≠ f * g := by
  have hirr := cyclotomic.irreducible_rat hn
  refine ⟨hirr.degree_pos, fun f g hf hg hfg => ?_⟩
  rcases hirr.isUnit_or_isUnit hfg with h | h
  · exact absurd h (not_isUnit_of_degree_pos f hf)
  · exact absurd h (not_isUnit_of_degree_pos g hg)

theorem exists_irreducible_rat_map_eq_primitiveRootFactorProd {n : ℕ} (hn : 0 < n) :
    ∃ P : ℚ[X], P.map (algebraMap ℚ ℂ) = primitiveRootFactorProd n ∧ Irreducible P :=
  ⟨cyclotomic n ℚ, map_rat_cyclotomic_eq_primitiveRootFactorProd n,
    cyclotomic.irreducible_rat hn⟩

theorem aeval_eq_zero_iff_cyclotomic_rat_dvd {n : ℕ} (hn : 0 < n) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ n) (A : ℚ[X]) :
    aeval ζ A = 0 ↔ cyclotomic n ℚ ∣ A := by
  rw [cyclotomic_eq_minpoly_rat hζ hn, minpoly.dvd_iff]

theorem eval_eq_zero_iff_cyclotomic_rat_dvd {n : ℕ} (hn : 0 < n) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ n) (A : ℚ[X]) :
    (A.map (algebraMap ℚ ℂ)).eval ζ = 0 ↔ cyclotomic n ℚ ∣ A := by
  rw [eval_map, ← aeval_def, aeval_eq_zero_iff_cyclotomic_rat_dvd hn hζ]

end CFSG.FeitThompson
