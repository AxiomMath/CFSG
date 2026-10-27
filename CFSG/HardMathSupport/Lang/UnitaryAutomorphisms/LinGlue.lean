module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.PGlue

public section

namespace CFSG.HardMathSupport.Lang.UnitaryAutomorphisms

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type} [Field K] {n : ℕ}

theorem fixed_conjAut_of_commute (A : GL (Fin n) K) (g : Matrix.SpecialLinearGroup (Fin n) K)
    (hcomm : (A : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K) =
      (g : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K)) :
    conjAut n K A (proj n K g) = proj n K g := by
  rw [conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation, hcomm, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

theorem fixed_fieldAut_of_map_eq (σ : K ≃+* K) (g : Matrix.SpecialLinearGroup (Fin n) K)
    (hg : (g : Matrix (Fin n) (Fin n) K).map σ = (g : Matrix (Fin n) (Fin n) K)) :
    fieldAut n K σ (proj n K g) = proj n K g := by
  rw [fieldAut_proj]
  congr 1
  apply Subtype.ext
  exact hg

theorem hasFixedThreePair_of_sl_pair [Finite K] (α : MulAut (projectiveSL n K))
    (x y : Matrix.SpecialLinearGroup (Fin n) K) (p : ℕ) (hp : p.Prime) (hp3 : p ≠ 3)
    (hxα : α (proj n K x) = proj n K x) (hyα : α (proj n K y) = proj n K y)
    (hxp : x ^ p = 1) (hyp : y ^ p = 1) (hxy3 : (x * y) ^ 3 = 1)
    (hns : ∀ s : K, ((x * y : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) ≠
      s • (1 : Matrix (Fin n) (Fin n) K)) :
    HasFixedThreePair α := by
  have hcop : (p).Coprime 3 := (Nat.coprime_primes hp Nat.prime_three).2 hp3
  have hdvd : ∀ z : Matrix.SpecialLinearGroup (Fin n) K, z ^ p = 1 →
      (orderOf (proj n K z)).Coprime 3 := fun z hz =>
    Nat.Coprime.coprime_dvd_left
      (orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hz, map_one])) hcop
  refine ⟨proj n K x, proj n K y, hxα, hyα, hdvd x hxp, hdvd y hyp, ?_⟩
  rw [← map_mul]
  have h3 : (proj n K (x * y)) ^ 3 = 1 := by rw [← map_pow, hxy3, map_one]
  rcases (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one h3) with h1 | h1
  · exfalso
    rw [orderOf_eq_one_iff, ← MonoidHom.mem_ker, ker_proj] at h1
    obtain ⟨c, -, hc⟩ := mem_scalars.1 h1
    apply hns (c : K)
    rw [hc]
    simp [Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]
  · exact h1

end CFSG.HardMathSupport.Lang.UnitaryAutomorphisms
