module

public import CFSG.GH74.Generic.BProg.B2.GenLocL4QNsq

public section

namespace CFSG.GH74.Generic.BProg.B2

open Matrix Matrix.SpecialLinearGroup CFSG GenLocL4Q

namespace GenLocL4QNsqU

variable {F : Type} [Field F]

@[expose] def Ub (c m s0 s1 : F) : Matrix (Fin 4) (Fin 4) F :=
  !![1, c, s0, c * s1; 1, 1, s1, s0; -s0 / m, c * s1 / m, 1, -c; s1 / m, -s0 / m, -1, 1]

@[expose] def Ab (c m p s0 s1 : F) : Matrix (Fin 4) (Fin 4) F :=
  G1 c m p (-(p * s1)) (-(p * s0) / c)

theorem Ub_comm_X (c m s0 s1 : F) : Ub c m s0 s1 * Xr c = Xr c * Ub c m s0 s1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Ub, Xr, Matrix.mul_apply, Fin.sum_univ_four]
  all_goals ring

theorem Ub_comm_YZ (c m s0 s1 : F) (hm : m ≠ 0) :
    Ub c m s0 s1 * (Yr m * Z0 c) = (Yr m * Z0 c) * Ub c m s0 s1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Ub, Yr, Z0, Matrix.mul_apply, Fin.sum_univ_four]
  all_goals field_simp

theorem det_Ub (c m s0 s1 : F) (hm : m ≠ 0) (hn : s0 ^ 2 - c * s1 ^ 2 = m * c) :
    (Ub c m s0 s1).det = 1 := by
  simp [Ub, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  field_simp
  linear_combination (s0 ^ 2 - c * s1 ^ 2 - c * m + m + m) * hn

theorem Ab_comm_X (c m p s0 s1 : F) (hm : m ≠ 0) : Ab c m p s0 s1 * Xr c = Xr c * Ab c m p s0 s1 :=
  G1_comm_X c m p _ _ hm

theorem Ab_comm_Y (c m p s0 s1 : F) (hm : m ≠ 0) : Ab c m p s0 s1 * Yr m = Yr m * Ab c m p s0 s1 :=
  G1_comm_Y c m p _ _ hm

theorem det_Ab (c m p s0 s1 : F) (hc : c ≠ 0) (hm : m ≠ 0) (hn : s0 ^ 2 - c * s1 ^ 2 = m * c)
    (hp : (2 * p ^ 2) ^ 2 = 1) : (Ab c m p s0 s1).det = 1 := by
  have h : ((-(p * s1)) ^ 2 - c * (-(p * s0) / c) ^ 2) / m = -p ^ 2 := by
    field_simp
    linear_combination (-p ^ 2) * hn
  rw [Ab, det_G1 c m p _ _ hm, h]
  linear_combination hp

theorem Ab_mul_Ub (c m p s0 s1 : F) (hc : c ≠ 0) (hm : m ≠ 0) (hn : s0 ^ 2 - c * s1 ^ 2 = m * c) :
    Ab c m p s0 s1 * Ub c m s0 s1 = Uc c (2 * s0) (2 * s1) * Ab c m p s0 s1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Ab, Ub, G1, Uc, Matrix.mul_apply, Fin.sum_univ_four]
  all_goals (try field_simp)
  all_goals first | ring1 | linear_combination p * hn | linear_combination (-p) * hn

theorem exists_two_sq_sq [Finite F] (hF : ringChar F ≠ 2) (hF4 : Nat.card F % 4 = 3) :
    ∃ p : F, (2 * p ^ 2) ^ 2 = 1 := by
  classical
  have := Fintype.ofFinite F
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  rcases isSquare_or_neg (Nat.card_eq_fintype_card (α := F) ▸ hF4) (a := (2 : F)⁻¹) with
    ⟨r, hr⟩ | ⟨r, hr⟩
  · refine ⟨r, ?_⟩
    have : 2 * r ^ 2 = 1 := by rw [sq, ← hr]; exact mul_inv_cancel₀ h2
    rw [this]; norm_num
  · refine ⟨r, ?_⟩
    have : 2 * r ^ 2 = -1 := by rw [sq, ← hr, mul_neg, mul_inv_cancel₀ h2]
    rw [this]; norm_num

theorem base_up_explicit [Finite F] (hF : ringChar F ≠ 2) (hF4 : Nat.card F % 4 = 3) {c m : F}
    (hc : ¬ IsSquare c) (hm : m ≠ 0) (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 4) F))
    (H1 : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * Xr c = Xr c * (g : Matrix (Fin 4) (Fin 4) F) →
      (g : Matrix (Fin 4) (Fin 4) F) * Yr m = Yr m * (g : Matrix (Fin 4) (Fin 4) F) → g ∈ Γ)
    (H2 : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * Xr c = Xr c * (g : Matrix (Fin 4) (Fin 4) F) →
      (g : Matrix (Fin 4) (Fin 4) F) * (Yr m * Z0 c) =
        (Yr m * Z0 c) * (g : Matrix (Fin 4) (Fin 4) F) →
        g ∈ Γ) :
    ∃ s0 s1 : F, s0 ^ 2 - c * s1 ^ 2 = m * c ∧
      Uel (!![2 * s0, c * (2 * s1); 2 * s1, 2 * s0]) ∈ Γ := by
  have hc0 : c ≠ 0 := ne_zero_of_not_isSquare hc
  obtain ⟨s0, s1, hn⟩ := exists_norm_eq hF hc0 (m * c)
  obtain ⟨p, hp⟩ := exists_two_sq_sq (F := F) hF hF4
  let a : Matrix.SpecialLinearGroup (Fin 4) F := ⟨Ab c m p s0 s1, det_Ab c m p s0 s1 hc0 hm hn hp⟩
  let u : Matrix.SpecialLinearGroup (Fin 4) F := ⟨Ub c m s0 s1, det_Ub c m s0 s1 hm hn⟩
  have ha : a ∈ Γ := H1 a (Ab_comm_X c m p s0 s1 hm) (Ab_comm_Y c m p s0 s1 hm)
  have hu : u ∈ Γ := H2 u (Ub_comm_X c m s0 s1) (Ub_comm_YZ c m s0 s1 hm)
  refine ⟨s0, s1, hn, mem_of_conj Γ ha hu ?_⟩
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Uel_eq_Uc]
  exact Ab_mul_Ub c m p s0 s1 hc0 hm hn

theorem two_mul_ne (hF : ringChar F ≠ 2) {c m s0 s1 : F} (hc0 : c ≠ 0) (hm : m ≠ 0)
    (hn : s0 ^ 2 - c * s1 ^ 2 = m * c) : 2 * s0 ≠ 0 ∨ 2 * s1 ≠ 0 := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  by_contra hcon
  push Not at hcon
  obtain ⟨h0, h1⟩ := hcon
  have h0' : s0 = 0 := (mul_eq_zero.1 h0).resolve_left h2
  have h1' : s1 = 0 := (mul_eq_zero.1 h1).resolve_left h2
  rw [h0', h1'] at hn
  exact mul_ne_zero hm hc0 (by linear_combination -hn)

@[expose] def Wb (c m w0 w1 : F) : Matrix (Fin 4) (Fin 4) F := G1 c m 0 w0 w1

theorem det_Wb (c m w0 w1 : F) (hm : m ≠ 0) (hw : w0 ^ 2 - c * w1 ^ 2 = m) :
    (Wb c m w0 w1).det = 1 := by
  have h : (w0 ^ 2 - c * w1 ^ 2) / m = 1 := by rw [hw]; exact div_self hm
  have h' : (0 ^ 2 - (w0 ^ 2 - c * w1 ^ 2) / m) ^ 2 = 1 := by rw [h]; norm_num
  rw [Wb, det_G1 c m 0 w0 w1 hm]
  exact h'

theorem Wb_mul_Uc (c m w0 w1 s t : F) (hm : m ≠ 0) (hw : w0 ^ 2 - c * w1 ^ 2 = m) :
    Wb c m w0 w1 * Uc c s t =
      Lc c (((w0 ^ 2 + c * w1 ^ 2) * s - 2 * c * w0 * w1 * t) / m ^ 2)
        (((w0 ^ 2 + c * w1 ^ 2) * t - 2 * w0 * w1 * s) / m ^ 2) * Wb c m w0 w1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Wb, G1, Uc, Lc, Matrix.mul_apply, Fin.sum_univ_four]
  all_goals (try field_simp)
  all_goals first
    | ring1
    | linear_combination (-(w0 * s - c * w1 * t)) * hw
    | linear_combination (-(c * (w0 * t - w1 * s))) * hw
    | linear_combination (-(w0 * t - w1 * s)) * hw

theorem low_ne_zero (c m w0 w1 s t : F) (hm : m ≠ 0) (hw : w0 ^ 2 - c * w1 ^ 2 = m)
    (h : s ≠ 0 ∨ t ≠ 0) :
    ((w0 ^ 2 + c * w1 ^ 2) * s - 2 * c * w0 * w1 * t) / m ^ 2 ≠ 0 ∨
      ((w0 ^ 2 + c * w1 ^ 2) * t - 2 * w0 * w1 * s) / m ^ 2 ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hm2 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm
  have h1' : (w0 ^ 2 + c * w1 ^ 2) * s - 2 * c * w0 * w1 * t = 0 :=
    (div_eq_zero_iff.1 h1).resolve_right hm2
  have h2' : (w0 ^ 2 + c * w1 ^ 2) * t - 2 * w0 * w1 * s = 0 :=
    (div_eq_zero_iff.1 h2).resolve_right hm2
  have hs : m ^ 2 * s = 0 := by
    linear_combination (w0 ^ 2 + c * w1 ^ 2) * h1' + c * (2 * w0 * w1) * h2' -
      (w0 ^ 2 - c * w1 ^ 2 + m) * s * hw
  have ht : m ^ 2 * t = 0 := by
    linear_combination (2 * w0 * w1) * h1' + (w0 ^ 2 + c * w1 ^ 2) * h2' -
      (w0 ^ 2 - c * w1 ^ 2 + m) * t * hw
  rcases h with h | h
  · exact h ((mul_eq_zero.1 hs).resolve_left hm2)
  · exact h ((mul_eq_zero.1 ht).resolve_left hm2)

end GenLocL4QNsqU

variable {F : Type} [Field F]

theorem base_up_uniform [Finite F] (hF : ringChar F ≠ 2) (hF4 : Nat.card F % 4 = 3) {c m : F}
    (hc : ¬ IsSquare c) (hm : m ≠ 0) (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 4) F))
    (H1 : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * Xr c = Xr c * (g : Matrix (Fin 4) (Fin 4) F) →
      (g : Matrix (Fin 4) (Fin 4) F) * Yr m = Yr m * (g : Matrix (Fin 4) (Fin 4) F) → g ∈ Γ)
    (H2 : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * Xr c = Xr c * (g : Matrix (Fin 4) (Fin 4) F) →
      (g : Matrix (Fin 4) (Fin 4) F) * (Yr m * Z0 c) =
        (Yr m * Z0 c) * (g : Matrix (Fin 4) (Fin 4) F) →
        g ∈ Γ) :
    ∃ s t : F, (s ≠ 0 ∨ t ≠ 0) ∧ Uel (!![s, c * t; t, s]) ∈ Γ := by
  obtain ⟨s0, s1, hn, hup⟩ := GenLocL4QNsqU.base_up_explicit hF hF4 hc hm Γ H1 H2
  exact ⟨2 * s0, 2 * s1, GenLocL4QNsqU.two_mul_ne hF (ne_zero_of_not_isSquare hc) hm hn, hup⟩

theorem base_low_uniform [Finite F] (hF : ringChar F ≠ 2) (hF4 : Nat.card F % 4 = 3) {c m : F}
    (hc : ¬ IsSquare c) (hm : m ≠ 0) (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 4) F))
    (H1 : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * Xr c = Xr c * (g : Matrix (Fin 4) (Fin 4) F) →
      (g : Matrix (Fin 4) (Fin 4) F) * Yr m = Yr m * (g : Matrix (Fin 4) (Fin 4) F) → g ∈ Γ)
    (H2 : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * Xr c = Xr c * (g : Matrix (Fin 4) (Fin 4) F) →
      (g : Matrix (Fin 4) (Fin 4) F) * (Yr m * Z0 c) =
        (Yr m * Z0 c) * (g : Matrix (Fin 4) (Fin 4) F) →
        g ∈ Γ) :
    ∃ s t : F, (s ≠ 0 ∨ t ≠ 0) ∧ Lel (!![s, c * t; t, s]) ∈ Γ := by
  have hc0 : c ≠ 0 := ne_zero_of_not_isSquare hc
  obtain ⟨s0, s1, hn, hup⟩ := GenLocL4QNsqU.base_up_explicit hF hF4 hc hm Γ H1 H2
  obtain ⟨w0, w1, hw⟩ := exists_norm_eq hF hc0 m
  let w : Matrix.SpecialLinearGroup (Fin 4) F :=
    ⟨GenLocL4QNsqU.Wb c m w0 w1, GenLocL4QNsqU.det_Wb c m w0 w1 hm hw⟩
  have hwΓ : w ∈ Γ := H1 w (G1_comm_X c m 0 w0 w1 hm) (G1_comm_Y c m 0 w0 w1 hm)
  refine ⟨_, _,
    GenLocL4QNsqU.low_ne_zero c m w0 w1 _ _ hm hw (GenLocL4QNsqU.two_mul_ne hF hc0 hm hn),
    mem_of_conj Γ hwΓ hup ?_⟩
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Uel_eq_Uc, Lel_eq_Lc]
  exact GenLocL4QNsqU.Wb_mul_Uc c m w0 w1 _ _ hm hw

theorem top_of_nsq_model_uniform [Finite F] (hF : ringChar F ≠ 2) (hF4 : Nat.card F % 4 = 3)
    {c m : F} (hc : ¬ IsSquare c) (hm : m ≠ 0) (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 4) F))
    (H1 : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * Xr c = Xr c * (g : Matrix (Fin 4) (Fin 4) F) →
      (g : Matrix (Fin 4) (Fin 4) F) * Yr m = Yr m * (g : Matrix (Fin 4) (Fin 4) F) → g ∈ Γ)
    (H2 : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * Xr c = Xr c * (g : Matrix (Fin 4) (Fin 4) F) →
      (g : Matrix (Fin 4) (Fin 4) F) * (Yr m * Z0 c) =
        (Yr m * Z0 c) * (g : Matrix (Fin 4) (Fin 4) F) →
        g ∈ Γ)
    (H3 : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * Yr m = Yr m * (g : Matrix (Fin 4) (Fin 4) F) →
      (g : Matrix (Fin 4) (Fin 4) F) * (Xr c * Z0 c) =
        (Xr c * Z0 c) * (g : Matrix (Fin 4) (Fin 4) F) →
        g ∈ Γ)
    (H4 : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * (Xr c * Yr m) =
        (Xr c * Yr m) * (g : Matrix (Fin 4) (Fin 4) F) →
      (g : Matrix (Fin 4) (Fin 4) F) * (Xr c * Z0 c) =
        (Xr c * Z0 c) * (g : Matrix (Fin 4) (Fin 4) F) →
        g ∈ Γ)
    (H5 : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * Xr c = Xr c * (g : Matrix (Fin 4) (Fin 4) F) →
      (g : Matrix (Fin 4) (Fin 4) F) * Z0 c = Z0 c * (g : Matrix (Fin 4) (Fin 4) F) → g ∈ Γ) :
    Γ = ⊤ := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hc0 : c ≠ 0 := ne_zero_of_not_isSquare hc
  have hc1 : c ≠ 1 := fun h => hc ⟨1, by rw [h]; ring⟩
  obtain ⟨s0, t0, hne, hup⟩ := base_up_uniform hF hF4 hc hm Γ H1 H2
  obtain ⟨s1, t1, hne', hlow⟩ := base_low_uniform hF hF4 hc hm Γ H1 H2
  obtain ⟨hadd, hscale, hmul⟩ := upper_closure hF4 c Γ H5
  obtain ⟨hadd', hscale', hmul'⟩ := lower_closure hF4 c Γ H5
  have h1c : 1 - c ≠ 0 := sub_ne_zero.2 (Ne.symm hc1)
  have hu : ((1 + c) / (1 - c)) ^ 2 - c * (2 / (1 - c)) ^ 2 = 1 := by field_simp; ring
  have hu1 : 2 / (1 - c) ≠ 0 := div_ne_zero h2 h1c
  have hzeroU : Uel (!![(0 : F), c * 0; 0, 0]) ∈ Γ := by
    have : (!![(0 : F), c * 0; 0, 0]) = 0 := by ext i j; fin_cases i <;> fin_cases j <;> simp
    rw [this]
    have : Uel (0 : Matrix (Fin 2) (Fin 2) F) = 1 := by simp [Uel, tv_zero']
    rw [this]; exact Γ.one_mem
  have hzeroL : Lel (!![(0 : F), c * 0; 0, 0]) ∈ Γ := by
    have : (!![(0 : F), c * 0; 0, 0]) = 0 := by ext i j; fin_cases i <;> fin_cases j <;> simp
    rw [this]
    have : Lel (0 : Matrix (Fin 2) (Fin 2) F) = 1 := by simp [Lel, tv_zero']
    rw [this]; exact Γ.one_mem
  have hPall := span_all (P := fun s t => Uel (!![s, c * t; t, s]) ∈ Γ) hc hu1 hzeroU hadd hscale
    (fun s t h => hmul _ _ hu s t h) hne hup
  have hQall := span_all (P := fun s t => Lel (!![s, c * t; t, s]) ∈ Γ) hc hu1 hzeroL hadd' hscale'
    (fun s t h => hmul' _ _ hu s t h) hne' hlow
  refine top_of_generators h2 hc0 Γ (fun s => ?_) (fun t => ?_) (fun s => ?_) (fun t => ?_)
    (fun a => H3 _ (b1_comm m a) (b1_comm_XZ c a))
    (fun a => H4 _ (b2_comm c m a hc0) (b2_comm_XZ c a hc0))
  · have := hPall s 0
    simpa [Uel, a1, tv_zero'] using this
  · have := hPall 0 t
    simpa [Uel, a2, tv_zero', mul_comm] using this
  · have := hQall s 0
    simpa [Lel, l1, tv_zero'] using this
  · have := hQall 0 t
    simpa [Lel, l2, tv_zero', mul_comm] using this

end CFSG.GH74.Generic.BProg.B2
