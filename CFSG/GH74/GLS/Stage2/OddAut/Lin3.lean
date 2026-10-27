module

public import CFSG.GH74.GLS.Stage2.OddAut.Lin3Split
public import CFSG.GH74.GLS.Stage2.OddAut.Lin3Cyc

public section

namespace CFSG.GH74.GLS.Stage2.OddAut

open Matrix

variable {K : Type} [Field K] [Finite K]

theorem lin3_classify {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrK : ¬ r ∣ Nat.card K)
    (a b : GL (Fin 3) K) (ua ub : Kˣ)
    (ha : a ^ r = GeneralLinearGroup.scalar (Fin 3) ua)
    (hb : b ^ r = GeneralLinearGroup.scalar (Fin 3) ub) (u : Kˣ)
    (hab : a * b = GeneralLinearGroup.scalar (Fin 3) u * (b * a))
    (hind : ∀ i j : ℕ, (∃ w : Kˣ, a ^ i * b ^ j = GeneralLinearGroup.scalar (Fin 3) w) →
      r ∣ i ∧ r ∣ j) :
    (∃ (B : GL (Fin 3) K) (da db : Fin 3 → K),
        (a : Matrix (Fin 3) (Fin 3) K) * (B : Matrix (Fin 3) (Fin 3) K) =
          (B : Matrix (Fin 3) (Fin 3) K) * Matrix.diagonal da ∧
        (b : Matrix (Fin 3) (Fin 3) K) * (B : Matrix (Fin 3) (Fin 3) K) =
          (B : Matrix (Fin 3) (Fin 3) K) * Matrix.diagonal db) ∨
      (r = 3 ∧ u ≠ 1) := by
  by_cases hu : u = 1
  · left
    subst hu
    have hcomm : a * b = b * a := by simpa using hab
    by_cases hdiv : r ∣ Nat.card K - 1
    · have ha' : (a : Matrix (Fin 3) (Fin 3) K) ^ r = (ua : K) • (1 : Matrix (Fin 3) (Fin 3) K) := by
        rw [← Units.val_pow_eq_pow_val, ha, coe_scalar_smul]
      have hb' : (b : Matrix (Fin 3) (Fin 3) K) ^ r = (ub : K) • (1 : Matrix (Fin 3) (Fin 3) K) := by
        rw [← Units.val_pow_eq_pow_val, hb, coe_scalar_smul]
      have hcomm' : (a : Matrix (Fin 3) (Fin 3) K) * (b : Matrix (Fin 3) (Fin 3) K) =
          (b : Matrix (Fin 3) (Fin 3) K) * (a : Matrix (Fin 3) (Fin 3) K) := by
        rw [← Units.val_mul, ← Units.val_mul, hcomm]
      have hind' : ∀ (i j : ℕ) (c : K), c ≠ 0 →
          (a : Matrix (Fin 3) (Fin 3) K) ^ i * (b : Matrix (Fin 3) (Fin 3) K) ^ j =
            c • (1 : Matrix (Fin 3) (Fin 3) K) → r ∣ i ∧ r ∣ j := by
        intro i j c hc h
        apply hind i j
        refine ⟨Units.mk0 c hc, Units.ext ?_⟩
        rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, h, coe_scalar_smul]
        rfl
      obtain ⟨B₀, da, db, hB, h1, h2⟩ := lin3_comm_diag hr hdiv (a : Matrix (Fin 3) (Fin 3) K)
        (b : Matrix (Fin 3) (Fin 3) K) (ua : K) (ub : K) ua.ne_zero ub.ne_zero ha' hb' hcomm' hind'
      exact ⟨Matrix.nonsingInvUnit B₀ hB, da, db, h1, h2⟩
    · exact (lin3_false_of_not_dvd hr hr2 hrK hdiv a b ua ub ha hb hcomm hind).elim
  · exact Or.inr ⟨heis_r_eq_three hr hab hb hu, hu⟩

end CFSG.GH74.GLS.Stage2.OddAut
