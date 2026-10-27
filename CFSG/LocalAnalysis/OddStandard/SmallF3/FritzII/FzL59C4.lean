module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL59Stmt


public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.ComponentClassification.AschbacherTheorem5.DeltaLocal

variable {G : Type} [Group G] {t s lam rho u : G} {b : Fin 3 → Fin 2 → G}

theorem fzl59c_p_conj_q {p q : G} (h : IsQ8Pair p q) : p * q * p⁻¹ = q * p ^ 2 := by
  have h1 := h.swap
  rw [h1.2.2.1, h1.inv_eq, h.swap.2.1]

theorem fzl59c_q_conj_p {p q : G} (h : IsQ8Pair p q) : q * p * q⁻¹ = p * p ^ 2 := by
  rw [h.2.2.1, h.inv_eq]

theorem fzl59c_sq_sq {p q : G} (h : IsQ8Pair p q) : (p ^ 2) ^ 2 = 1 := by
  rw [← pow_mul]
  exact h.1

theorem fzl59c_commute_z (hg : Fz59Grid t s lam rho b) (i j : Fin 3) (k : Fin 2) :
    Commute (b i 0 ^ 2) (b j k) := by
  by_cases hij : i = j
  · subst hij
    match k with
    | 0 => exact (Commute.refl (b i 0)).pow_left 2
    | 1 => exact (hg.quat i).mul_comm_sq.symm
  · exact (hg.comm i j hij 0 k).pow_left 2

theorem fzl59c_commute_zz (hg : Fz59Grid t s lam rho b) (i j : Fin 3) :
    Commute (b i 0 ^ 2) (b j 0 ^ 2) :=
  (fzl59c_commute_z hg i j 0).pow_right 2

theorem fzl59c_t_sq (hg : Fz59Grid t s lam rho b) : t ^ 2 = 1 := by
  have c01 : Commute (b 0 0) (b 1 0) := hg.comm 0 1 (by decide) 0 0
  have c02 : Commute (b 0 0) (b 2 0) := hg.comm 0 2 (by decide) 0 0
  have c12 : Commute (b 1 0) (b 2 0) := hg.comm 1 2 (by decide) 0 0
  rw [hg.t_eq, (c02.mul_left c12).mul_pow, c01.mul_pow, hg.sq_eq,
    ← sq (b 0 0 ^ 2 * b 1 0 ^ 2), (fzl59c_commute_zz hg 0 1).mul_pow,
    fzl59c_sq_sq (hg.quat 0), fzl59c_sq_sq (hg.quat 1), one_mul]

theorem fzl59c_s_sq (hg : Fz59Grid t s lam rho b) : s ^ 2 = 1 := by
  have c01 : Commute (b 0 1) (b 1 1) := hg.comm 0 1 (by decide) 1 1
  have c02 : Commute (b 0 1) (b 2 1) := hg.comm 0 2 (by decide) 1 1
  have c12 : Commute (b 1 1) (b 2 1) := hg.comm 1 2 (by decide) 1 1
  rw [hg.s_eq, (c02.mul_left c12).mul_pow, c01.mul_pow, (hg.quat 0).2.1, (hg.quat 1).2.1,
    (hg.quat 2).2.1, hg.sq_eq, ← sq (b 0 0 ^ 2 * b 1 0 ^ 2), (fzl59c_commute_zz hg 0 1).mul_pow,
    fzl59c_sq_sq (hg.quat 0), fzl59c_sq_sq (hg.quat 1), one_mul]

theorem fzl59c_s_row (hg : Fz59Grid t s lam rho b) (i : Fin 3) :
    ∃ w, Commute w (b i 0) ∧ Commute w (b i 1) ∧ s = b i 1 * w := by
  match i with
  | 0 =>
    refine ⟨b 1 1 * b 2 1, ?_, ?_, ?_⟩
    · exact (hg.comm 1 0 (by decide) 1 0).mul_left (hg.comm 2 0 (by decide) 1 0)
    · exact (hg.comm 1 0 (by decide) 1 1).mul_left (hg.comm 2 0 (by decide) 1 1)
    · rw [hg.s_eq, mul_assoc]
  | 1 =>
    refine ⟨b 0 1 * b 2 1, ?_, ?_, ?_⟩
    · exact (hg.comm 0 1 (by decide) 1 0).mul_left (hg.comm 2 1 (by decide) 1 0)
    · exact (hg.comm 0 1 (by decide) 1 1).mul_left (hg.comm 2 1 (by decide) 1 1)
    · rw [hg.s_eq, ← mul_assoc, (hg.comm 0 1 (by decide) 1 1).eq, mul_assoc]
  | 2 =>
    refine ⟨b 0 1 * b 1 1, ?_, ?_, ?_⟩
    · exact (hg.comm 0 2 (by decide) 1 0).mul_left (hg.comm 1 2 (by decide) 1 0)
    · exact (hg.comm 0 2 (by decide) 1 1).mul_left (hg.comm 1 2 (by decide) 1 1)
    · rw [hg.s_eq]
      exact ((hg.comm 0 2 (by decide) 1 1).mul_left (hg.comm 1 2 (by decide) 1 1)).eq

theorem fzl59c_t_row (hg : Fz59Grid t s lam rho b) (i : Fin 3) :
    ∃ w, Commute w (b i 0) ∧ Commute w (b i 1) ∧ t = b i 0 * w := by
  match i with
  | 0 =>
    refine ⟨b 1 0 * b 2 0, ?_, ?_, ?_⟩
    · exact (hg.comm 1 0 (by decide) 0 0).mul_left (hg.comm 2 0 (by decide) 0 0)
    · exact (hg.comm 1 0 (by decide) 0 1).mul_left (hg.comm 2 0 (by decide) 0 1)
    · rw [hg.t_eq, mul_assoc]
  | 1 =>
    refine ⟨b 0 0 * b 2 0, ?_, ?_, ?_⟩
    · exact (hg.comm 0 1 (by decide) 0 0).mul_left (hg.comm 2 1 (by decide) 0 0)
    · exact (hg.comm 0 1 (by decide) 0 1).mul_left (hg.comm 2 1 (by decide) 0 1)
    · rw [hg.t_eq, ← mul_assoc, (hg.comm 0 1 (by decide) 0 0).eq, mul_assoc]
  | 2 =>
    refine ⟨b 0 0 * b 1 0, ?_, ?_, ?_⟩
    · exact (hg.comm 0 2 (by decide) 0 0).mul_left (hg.comm 1 2 (by decide) 0 0)
    · exact (hg.comm 0 2 (by decide) 0 1).mul_left (hg.comm 1 2 (by decide) 0 1)
    · rw [hg.t_eq]
      exact ((hg.comm 0 2 (by decide) 0 0).mul_left (hg.comm 1 2 (by decide) 0 0)).eq

theorem fzl59c_p_s (hg : Fz59Grid t s lam rho b) (i : Fin 3) :
    b i 0 * s * (b i 0)⁻¹ = s * b i 0 ^ 2 := by
  obtain ⟨w, hwp, hwq, hs⟩ := fzl59c_s_row hg i
  rw [hs]
  have hw2 : Commute (b i 0 ^ 2) w := (hwp.pow_right 2).symm
  calc b i 0 * (b i 1 * w) * (b i 0)⁻¹
      = (b i 0 * b i 1 * (b i 0)⁻¹) * (b i 0 * w * (b i 0)⁻¹) := by group
    _ = (b i 1 * b i 0 ^ 2) * w := by
      rw [fzl59c_p_conj_q (hg.quat i), hwp.symm.mul_inv_cancel]
    _ = b i 1 * w * b i 0 ^ 2 := by rw [mul_assoc, hw2.eq, ← mul_assoc]

theorem fzl59c_q_t (hg : Fz59Grid t s lam rho b) (i : Fin 3) :
    b i 1 * t * (b i 1)⁻¹ = t * b i 0 ^ 2 := by
  obtain ⟨w, hwp, hwq, ht⟩ := fzl59c_t_row hg i
  rw [ht]
  have hw2 : Commute (b i 0 ^ 2) w := (hwp.pow_right 2).symm
  calc b i 1 * (b i 0 * w) * (b i 1)⁻¹
      = (b i 1 * b i 0 * (b i 1)⁻¹) * (b i 1 * w * (b i 1)⁻¹) := by group
    _ = (b i 0 * b i 0 ^ 2) * w := by
      rw [fzl59c_q_conj_p (hg.quat i), hwq.symm.mul_inv_cancel]
    _ = b i 0 * w * b i 0 ^ 2 := by rw [mul_assoc, hw2.eq, ← mul_assoc]

theorem fzl59c_p_t (hg : Fz59Grid t s lam rho b) (i : Fin 3) : b i 0 * t * (b i 0)⁻¹ = t := by
  obtain ⟨w, hwp, hwq, ht⟩ := fzl59c_t_row hg i
  rw [ht]
  calc b i 0 * (b i 0 * w) * (b i 0)⁻¹ = b i 0 * (b i 0 * w * (b i 0)⁻¹) := by group
    _ = b i 0 * w := by rw [hwp.symm.mul_inv_cancel]

theorem fzl59c_q_s (hg : Fz59Grid t s lam rho b) (i : Fin 3) : b i 1 * s * (b i 1)⁻¹ = s := by
  obtain ⟨w, hwp, hwq, hs⟩ := fzl59c_s_row hg i
  rw [hs]
  calc b i 1 * (b i 1 * w) * (b i 1)⁻¹ = b i 1 * (b i 1 * w * (b i 1)⁻¹) := by group
    _ = b i 1 * w := by rw [hwq.symm.mul_inv_cancel]

theorem fzl59c_ts_comm (hg : Fz59Grid t s lam rho b) : s * t = t * s := by
  have h0 := fzl59c_p_s hg 0
  have h1 := fzl59c_p_s hg 1
  have h2 := fzl59c_p_s hg 2
  have e : t * s * t⁻¹ = s := by
    have e1 : t * s * t⁻¹ = b 0 0 * (b 1 0 * (b 2 0 * s * (b 2 0)⁻¹) * (b 1 0)⁻¹) * (b 0 0)⁻¹ := by
      rw [hg.t_eq]
      group
    rw [e1, h2]
    have e2 : b 1 0 * (s * b 2 0 ^ 2) * (b 1 0)⁻¹ =
        (b 1 0 * s * (b 1 0)⁻¹) * (b 1 0 * b 2 0 ^ 2 * (b 1 0)⁻¹) := by group
    rw [e2, h1, ((fzl59c_commute_z hg 2 1 0).symm).mul_inv_cancel]
    have e3 : b 0 0 * (s * b 1 0 ^ 2 * b 2 0 ^ 2) * (b 0 0)⁻¹ =
        (b 0 0 * s * (b 0 0)⁻¹) * (b 0 0 * b 1 0 ^ 2 * (b 0 0)⁻¹) *
          (b 0 0 * b 2 0 ^ 2 * (b 0 0)⁻¹) := by group
    rw [e3, h0, ((fzl59c_commute_z hg 1 0 0).symm).mul_inv_cancel,
      ((fzl59c_commute_z hg 2 0 0).symm).mul_inv_cancel]
    have hz : b 0 0 ^ 2 * b 1 0 ^ 2 * b 2 0 ^ 2 = 1 := by
      rw [hg.sq_eq, ← sq (b 0 0 ^ 2 * b 1 0 ^ 2), (fzl59c_commute_zz hg 0 1).mul_pow,
        fzl59c_sq_sq (hg.quat 0), fzl59c_sq_sq (hg.quat 1), one_mul]
    rw [mul_assoc s, mul_assoc s, hz, mul_one]
  have e4 : t * s = s * t := by
    calc t * s = (t * s * t⁻¹) * t := by group
      _ = s * t := by rw [e]
  exact e4.symm

end CFSG.OddStandard.SmallF3.FritzII
