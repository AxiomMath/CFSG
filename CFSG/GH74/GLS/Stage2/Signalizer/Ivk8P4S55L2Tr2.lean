module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55L2Tr

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L2Ord

open Matrix Polynomial
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem prime_dvd_6600 {r : ℕ} (hr : r.Prime) (h : r ∣ 6600) :
    r = 2 ∨ r = 3 ∨ r = 5 ∨ r = 11 := by
  rw [show (6600 : ℕ) = 2 * 2 * 2 * 3 * 5 * 5 * 11 by norm_num] at h
  have h2 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two)
  have h3 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three)
  have h5 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_five)
  have h11 := (Nat.prime_dvd_prime_iff_eq hr (by decide : Nat.Prime 11))
  simp only [hr.dvd_mul] at h
  tauto

theorem exists_good_t [Finite F] {r f : ℕ} [CharP F r] (hr : r.Prime) (hr2 : r ≠ 2)
    (hF : Nat.card F = r ^ f) (hf : 1 ≤ f) (h3 : Nat.card F ≠ 3) (h5 : Nat.card F ≠ 5)
    (h9 : Nat.card F ≠ 9) : ∃ t : F, ordPoly (2 + t ^ 2) ≠ 0 := by
  by_cases hr7 : 7 ≤ r
  · by_cases hr11 : r = 11
    · refine ⟨2, fun h => ?_⟩
      have h1 : ordPoly ((2 : F) + 2 ^ 2) = (7990080 : F) := by
        simp only [ordPoly]
        norm_num
      rw [h1] at h
      have := (CharP.cast_eq_zero_iff F r 7990080).mp (by exact_mod_cast h)
      rw [hr11] at this
      norm_num at this
    · refine ⟨1, fun h => ?_⟩
      have h1 : ordPoly ((2 : F) + 1 ^ 2) = (6600 : F) := by
        simp only [ordPoly]
        norm_num
      rw [h1] at h
      have h2 := (CharP.cast_eq_zero_iff F r 6600).mp (by exact_mod_cast h)
      rcases prime_dvd_6600 hr h2 with h | h | h | h <;> omega
  · apply exists_t_of_card
    have hr35 : r = 3 ∨ r = 5 := by
      have h2 := hr.two_le
      interval_cases r
      · exact absurd rfl hr2
      · exact Or.inl rfl
      · exact absurd hr (by decide)
      · exact Or.inr rfl
      · exact absurd hr (by decide)
    rcases hr35 with rfl | rfl
    · have : 3 ≤ f := by
        by_contra hlt
        have : f = 1 ∨ f = 2 := by omega
        rcases this with rfl | rfl
        · exact h3 (by simpa using hF)
        · exact h9 (by simpa using hF)
      rw [hF]
      calc 19 ≤ 3 ^ 3 := by norm_num
        _ ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) this
    · have : 2 ≤ f := by
        by_contra hlt
        have : f = 1 := by omega
        subst this
        exact h5 (by simpa using hF)
      rw [hF]
      calc 19 ≤ 5 ^ 2 := by norm_num
        _ ≤ 5 ^ f := Nat.pow_le_pow_right (by norm_num) this

theorem bad_t9 [CharP F 3] {α : F} (hα : α ^ 4 - 3 * α ^ 2 + 1 = 0) :
    ordPoly (α ^ 2 - 2 - 1 ^ 2) ≠ 0 := by
  have h3 : (3 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 3
  have h4 : α ^ 4 = -1 := by linear_combination hα + α ^ 2 * h3
  set u : F := α ^ 2 - 2 - 1 ^ 2 with hu
  have hu2 : u ^ 2 = -1 := by
    rw [hu]
    linear_combination h4 + (3 - 2 * α ^ 2) * h3
  intro hP
  have hu4 : u ^ 4 = 1 := by
    rw [show u ^ 4 = (u ^ 2) ^ 2 by ring, hu2]
    norm_num
  have hP' : (50 : F) * u = 0 := by
    have : ordPoly u = 50 * u := by
      rw [ordPoly]
      calc (u ^ 2 - 4) * u * (u ^ 2 - 1) * (u ^ 4 - 3 * u ^ 2 + 1) =
          ((-1) - 4) * u * ((-1) - 1) * (1 - 3 * (-1) + 1) := by rw [hu2, hu4]
        _ = 50 * u := by ring
    rw [this] at hP
    exact hP
  have h50 : (50 : F) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff F 3 50).mp (by exact_mod_cast h)
    norm_num at this
  have hu0 : u = 0 := by
    rcases mul_eq_zero.mp hP' with h | h
    · exact absurd h h50
    · exact h
  rw [hu0] at hu2
  norm_num at hu2

theorem not_scalar_of_ne_one {Mh : Matrix.SpecialLinearGroup (Fin 2) F}
    (h : (QuotientGroup.mk Mh : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) ≠ 1) :
    ∀ c : F, (Mh : Matrix (Fin 2) (Fin 2) F) ≠ c • 1 := by
  intro c hc
  apply h
  rw [QuotientGroup.eq_one_iff]
  refine Matrix.SpecialLinearGroup.mem_center_iff.mpr ⟨c, ?_, ?_⟩
  · have := Mh.2
    rw [hc, Matrix.det_smul, Matrix.det_one] at this
    simpa [pow_two] using this
  · rw [hc]
    simp [Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]

theorem exists_conj_traces (y' : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) (hy1 : y' ≠ 1)
    (t : F) :
    ∃ G Mh : Matrix.SpecialLinearGroup (Fin 2) F,
      (QuotientGroup.mk Mh : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) = y' ∧
      ((Mh⁻¹ * (G * Mh * G⁻¹) : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F).trace = 2 + t ^ 2 ∧
      ((Mh * (G * Mh * G⁻¹) : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F).trace =
        (Mh : Matrix (Fin 2) (Fin 2) F).trace ^ 2 - 2 - t ^ 2 := by
  obtain ⟨Mh, rfl⟩ := QuotientGroup.mk_surjective y'
  obtain ⟨v, hv⟩ := exists_cycQ_ne_zero _ (not_scalar_of_ne_one hy1)
  have hs : t / cycQ (Mh : Matrix (Fin 2) (Fin 2) F) v *
      cycQ (Mh : Matrix (Fin 2) (Fin 2) F) v = t := div_mul_cancel₀ t hv
  refine ⟨gSL (t / cycQ (Mh : Matrix (Fin 2) (Fin 2) F) v) v, Mh, rfl, ?_, ?_⟩
  · rw [trace_inv_conj, hs]
  · rw [trace_mul_conj, hs]

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L2Ord
