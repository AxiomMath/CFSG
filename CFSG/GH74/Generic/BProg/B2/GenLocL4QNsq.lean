module

public import CFSG.GH74.Generic.BProg.B2.GenLocL4QSplit

public section

namespace CFSG.GH74.Generic.BProg.B2

open Matrix Polynomial Matrix.SpecialLinearGroup CFSG

namespace GenLocL4Q

variable {F : Type} [Field F]

theorem ne_zero_of_not_isSquare {a : F} (ha : ¬ IsSquare a) : a ≠ 0 := by
  rintro rfl; exact ha ⟨0, by simp⟩

theorem isSquare_mul_of_not [Fintype F] {a b : F} (ha : ¬ IsSquare a)
    (hb : ¬ IsSquare b) : IsSquare (a * b) := by
  classical
  have h1 := quadraticChar_neg_one_iff_not_isSquare.2 ha
  have h2 := quadraticChar_neg_one_iff_not_isSquare.2 hb
  have h3 : quadraticChar F (a * b) = 1 := by rw [map_mul, h1, h2]; norm_num
  exact (quadraticChar_one_iff_isSquare (mul_ne_zero (ne_zero_of_not_isSquare ha)
    (ne_zero_of_not_isSquare hb))).1 h3

theorem isSquare_or_neg [Fintype F] (hF4 : Fintype.card F % 4 = 3) {a : F} : IsSquare a ∨ IsSquare (-a) := by
  by_contra hcon
  push Not at hcon
  have hneg : ¬ IsSquare (-1 : F) := fun h => (FiniteField.isSquare_neg_one_iff.1 h) hF4
  have := isSquare_mul_of_not hneg hcon.1
  apply hcon.2
  simpa using this

theorem exists_norm_eq [Finite F] (hF : ringChar F ≠ 2) {c : F} (hc : c ≠ 0) (e : F) :
    ∃ q0 q1 : F, q0 ^ 2 - c * q1 ^ 2 = e := by
  classical
  have := Fintype.ofFinite F
  have hodd : Fintype.card F % 2 = 1 := FiniteField.odd_card_of_char_ne_two hF
  have hf : (X ^ 2 : F[X]).degree = 2 := degree_X_pow 2
  have hg : (-(C c) * X ^ 2 - C e : F[X]).degree = 2 := by
    have h1 : (-(C c) * X ^ 2 : F[X]).degree = 2 := by
      rw [← C_neg, degree_C_mul (neg_ne_zero.2 hc)]; exact degree_X_pow 2
    rw [degree_sub_eq_left_of_degree_lt (by rw [h1]; exact lt_of_le_of_lt degree_C_le (by norm_num))]
    exact h1
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic hf hg hodd
  refine ⟨a, b, ?_⟩
  simp at hab
  linear_combination hab

theorem exists_good_p [Finite F] (h2 : (2 : F) ≠ 0) (h7 : 7 ≤ Nat.card F) :
    ∃ p : F, p ≠ 0 ∧ p ^ 2 ≠ 1 ∧ 2 * p ^ 2 ≠ 1 := by
  classical
  have := Fintype.ofFinite F
  obtain ⟨S, hS, hcard⟩ : ∃ S : Finset F, (∀ p : F, (p = 0 ∨ p ^ 2 = 1 ∨ 2 * p ^ 2 = 1) → p ∈ S) ∧
      S.card ≤ 5 := by
    by_cases hex : ∃ p0 : F, 2 * p0 ^ 2 = 1
    · obtain ⟨p0, hp0⟩ := hex
      refine ⟨{0, 1, -1, p0, -p0}, ?_, Finset.card_le_five⟩
      intro p hp
      rcases hp with h | h | h
      · simp [h]
      · have h' : (p - 1) * (p + 1) = 0 := by linear_combination h
        rcases mul_eq_zero.1 h' with h'' | h''
        · have : p = 1 := by linear_combination h''
          simp [this]
        · have : p = -1 := by linear_combination h''
          simp [this]
      · have h3 : 2 * (p ^ 2 - p0 ^ 2) = 0 := by linear_combination h - hp0
        have h4 : p ^ 2 - p0 ^ 2 = 0 := (mul_eq_zero.1 h3).resolve_left h2
        have h' : (p - p0) * (p + p0) = 0 := by linear_combination h4
        rcases mul_eq_zero.1 h' with h'' | h''
        · have : p = p0 := by linear_combination h''
          simp [this]
        · have : p = -p0 := by linear_combination h''
          simp [this]
    · refine ⟨{0, 1, -1}, ?_, (Finset.card_le_three (a := (0 : F)) (b := 1) (c := -1)).trans (by norm_num)⟩
      intro p hp
      rcases hp with h | h | h
      · simp [h]
      · have h' : (p - 1) * (p + 1) = 0 := by linear_combination h
        rcases mul_eq_zero.1 h' with h'' | h''
        · have : p = 1 := by linear_combination h''
          simp [this]
        · have : p = -1 := by linear_combination h''
          simp [this]
      · exact absurd ⟨p, h⟩ hex
  obtain ⟨p, -, hp⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := S) (t := Finset.univ)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; omega)
  exact ⟨p, fun h => hp (hS p (Or.inl h)), fun h => hp (hS p (Or.inr (Or.inl h))),
    fun h => hp (hS p (Or.inr (Or.inr h)))⟩

@[expose] def Z0 (c : F) : Matrix (Fin 4) (Fin 4) F :=
  !![0, c, 0, 0; 1, 0, 0, 0; 0, 0, 0, -c; 0, 0, -1, 0]

@[expose] def G1 (c m p q0 q1 : F) : Matrix (Fin 4) (Fin 4) F :=
  !![p, 0, q0, c * q1; 0, p, q1, q0; q0 / m, -(c * q1) / m, p, 0; -q1 / m, q0 / m, 0, p]

@[expose] def G2 (c m ρ p q0 q1 : F) : Matrix (Fin 4) (Fin 4) F :=
  !![ρ * p, 0, -(ρ * q0), -(ρ * (c * q1)); 0, ρ * p, -(ρ * q1), -(ρ * q0);
    ρ * q0 / m, -(ρ * (c * q1)) / m, ρ * p, 0; -(ρ * q1) / m, ρ * q0 / m, 0, ρ * p]

@[expose] def G2' (c m ρ p q0 q1 : F) : Matrix (Fin 4) (Fin 4) F :=
  !![ρ * p, 0, ρ * q0, ρ * (c * q1); 0, ρ * p, ρ * q1, ρ * q0;
    -(ρ * q0) / m, ρ * (c * q1) / m, ρ * p, 0; ρ * q1 / m, -(ρ * q0) / m, 0, ρ * p]

@[expose] def Td (a d : F) : Matrix (Fin 4) (Fin 4) F := Matrix.diagonal ![a, a, d, d]

theorem G1_comm_X (c m p q0 q1 : F) (hm : m ≠ 0) :
    G1 c m p q0 q1 * Xr c = Xr c * G1 c m p q0 q1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [G1, Xr, Matrix.mul_apply, Fin.sum_univ_four]
  all_goals field_simp

theorem G1_comm_Y (c m p q0 q1 : F) (hm : m ≠ 0) :
    G1 c m p q0 q1 * Yr m = Yr m * G1 c m p q0 q1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [G1, Yr, Matrix.mul_apply, Fin.sum_univ_four]
  all_goals field_simp

theorem G2_comm_X (c m ρ p q0 q1 : F) (hm : m ≠ 0) :
    G2 c m ρ p q0 q1 * Xr c = Xr c * G2 c m ρ p q0 q1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [G2, Xr, Matrix.mul_apply, Fin.sum_univ_four]
  all_goals field_simp

theorem G2_comm_YZ (c m ρ p q0 q1 : F) (hm : m ≠ 0) :
    G2 c m ρ p q0 q1 * (Yr m * Z0 c) = (Yr m * Z0 c) * G2 c m ρ p q0 q1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [G2, Yr, Z0, Matrix.mul_apply, Fin.sum_univ_four]
  all_goals field_simp

theorem G2'_comm_X (c m ρ p q0 q1 : F) (hm : m ≠ 0) :
    G2' c m ρ p q0 q1 * Xr c = Xr c * G2' c m ρ p q0 q1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [G2', Xr, Matrix.mul_apply, Fin.sum_univ_four]
  all_goals field_simp

theorem G2'_comm_YZ (c m ρ p q0 q1 : F) (hm : m ≠ 0) :
    G2' c m ρ p q0 q1 * (Yr m * Z0 c) = (Yr m * Z0 c) * G2' c m ρ p q0 q1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [G2', Yr, Z0, Matrix.mul_apply, Fin.sum_univ_four]
  all_goals field_simp

theorem Td_comm_X (c a d : F) : Td a d * Xr c = Xr c * Td a d := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Td, Xr, Matrix.mul_apply, Matrix.diagonal_apply]
  all_goals ring

theorem Td_comm_Z (c a d : F) : Td a d * Z0 c = Z0 c * Td a d := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Td, Z0, Matrix.mul_apply, Matrix.diagonal_apply]
  all_goals ring

theorem det_G1 (c m p q0 q1 : F) (hm : m ≠ 0) :
    (G1 c m p q0 q1).det = ((p ^ 2 - (q0 ^ 2 - c * q1 ^ 2) / m)) ^ 2 := by
  simp [G1, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  field_simp
  ring

theorem det_G2 (c m ρ p q0 q1 : F) (hm : m ≠ 0) :
    (G2 c m ρ p q0 q1).det = (ρ ^ 2 * (p ^ 2 + (q0 ^ 2 - c * q1 ^ 2) / m)) ^ 2 := by
  simp [G2, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  field_simp
  ring

theorem det_G2' (c m ρ p q0 q1 : F) (hm : m ≠ 0) :
    (G2' c m ρ p q0 q1).det = (ρ ^ 2 * (p ^ 2 + (q0 ^ 2 - c * q1 ^ 2) / m)) ^ 2 := by
  simp [G2', Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  field_simp
  ring

theorem det_Td (a d : F) : (Td a d).det = a * a * (d * d) := by
  simp [Td, Matrix.det_diagonal, Fin.prod_univ_four]
  ring

theorem span_all {c u0 u1 : F} {P : F → F → Prop} (hc : ¬ IsSquare c) (hu1 : u1 ≠ 0)
    (hzero : P 0 0)
    (hadd : ∀ s t s' t', P s t → P s' t' → P (s + s') (t + t'))
    (hscale : ∀ s t α, α ≠ 0 → P s t → P (α * s) (α * t))
    (hmul : ∀ s t, P s t → P (u0 * s + c * u1 * t) (u1 * s + u0 * t)) {s0 t0 : F}
    (hne : s0 ≠ 0 ∨ t0 ≠ 0) (h0 : P s0 t0) : ∀ s t, P s t := by
  have hN : s0 ^ 2 - c * t0 ^ 2 ≠ 0 := by
    intro h
    rcases hne with hs | ht
    · by_cases ht : t0 = 0
      · rw [ht] at h
        have h' : s0 ^ 2 = 0 := by simpa using h
        exact hs ((pow_eq_zero_iff two_ne_zero).1 h')
      · apply hc
        refine ⟨s0 / t0, ?_⟩
        field_simp
        linear_combination (-1 : F) * h
    · apply hc
      refine ⟨s0 / t0, ?_⟩
      field_simp
      linear_combination (-1 : F) * h
  intro s t
  set s1 := u0 * s0 + c * u1 * t0 with hs1
  set t1 := u1 * s0 + u0 * t0 with ht1
  have h1 : P s1 t1 := hmul s0 t0 h0
  have hΔ : s0 * t1 - t0 * s1 = u1 * (s0 ^ 2 - c * t0 ^ 2) := by rw [hs1, ht1]; ring
  have hΔ0 : s0 * t1 - t0 * s1 ≠ 0 := by rw [hΔ]; exact mul_ne_zero hu1 hN
  set Δ := s0 * t1 - t0 * s1 with hΔdef
  have hα : ∀ α β : F, P (α * s0 + β * s1) (α * t0 + β * t1) := by
    intro α β
    have hA : P (α * s0) (α * t0) := by
      by_cases ha : α = 0
      · simpa [ha] using hzero
      · exact hscale _ _ _ ha h0
    have hB : P (β * s1) (β * t1) := by
      by_cases hb : β = 0
      · simpa [hb] using hzero
      · exact hscale _ _ _ hb h1
    exact hadd _ _ _ _ hA hB
  have key := hα ((s * t1 - t * s1) / Δ) ((s0 * t - t0 * s) / Δ)
  have e1 : (s * t1 - t * s1) / Δ * s0 + (s0 * t - t0 * s) / Δ * s1 = s := by
    field_simp; rw [hΔdef]; ring
  have e2 : (s * t1 - t * s1) / Δ * t0 + (s0 * t - t0 * s) / Δ * t1 = t := by
    field_simp; rw [hΔdef]; ring
  rw [e1, e2] at key
  exact key

@[expose] def Uc (c s t : F) : Matrix (Fin 4) (Fin 4) F :=
  !![1, 0, s, c * t; 0, 1, t, s; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def Lc (c s t : F) : Matrix (Fin 4) (Fin 4) F :=
  !![1, 0, 0, 0; 0, 1, 0, 0; s, c * t, 1, 0; t, s, 0, 1]

@[expose] def Tu (c u0 u1 : F) : Matrix (Fin 4) (Fin 4) F :=
  !![u0, c * u1, 0, 0; u1, u0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

theorem Tu_comm_X (c u0 u1 : F) : Tu c u0 u1 * Xr c = Xr c * Tu c u0 u1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Tu, Xr, Matrix.mul_apply, Fin.sum_univ_four]
  all_goals ring

theorem Tu_comm_Z (c u0 u1 : F) : Tu c u0 u1 * Z0 c = Z0 c * Tu c u0 u1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Tu, Z0, Matrix.mul_apply, Fin.sum_univ_four]
  all_goals ring

theorem det_Tu (c u0 u1 : F) : (Tu c u0 u1).det = u0 ^ 2 - c * u1 ^ 2 := by
  simp [Tu, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

theorem Uel_eq_Uc (c s t : F) :
    ((Uel (!![s, c * t; t, s]) : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = Uc c s t := by
  rw [Uel_coe]; rfl

theorem Lel_eq_Lc (c s t : F) :
    ((Lel (!![s, c * t; t, s]) : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = Lc c s t := by
  rw [Lel_coe]; rfl

theorem Td_Uc (c a d s t : F) (hd : d ≠ 0) :
    Td a d * Uc c s t = Uc c (a / d * s) (a / d * t) * Td a d := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Td, Uc, Matrix.mul_apply, Matrix.diagonal_apply]
  all_goals (field_simp)

theorem Tu_Uc (c u0 u1 s t : F) :
    Tu c u0 u1 * Uc c s t = Uc c (u0 * s + c * u1 * t) (u1 * s + u0 * t) * Tu c u0 u1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Tu, Uc, Matrix.mul_apply, Fin.sum_univ_four]
  all_goals ring

theorem Td_Lc (c a d s t : F) (ha : a ≠ 0) :
    Td a d * Lc c s t = Lc c (d / a * s) (d / a * t) * Td a d := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Td, Lc, Matrix.mul_apply, Matrix.diagonal_apply]
  all_goals (field_simp)

theorem Tu_Lc (c u0 u1 s t : F) (hu : u0 ^ 2 - c * u1 ^ 2 = 1) :
    Tu c u0 (-u1) * Lc c s t = Lc c (s * u0 + c * t * u1) (s * u1 + t * u0) * Tu c u0 (-u1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Tu, Lc, Matrix.mul_apply, Fin.sum_univ_four]
  all_goals first | ring1 | linear_combination (-s) * hu | linear_combination (-(c * t)) * hu |
    linear_combination (-t) * hu

theorem chain_up_id (c m ρ p q0 q1 : F) (hm : m ≠ 0) (h2p : 2 * p ^ 2 - 1 ≠ 0) (hρ : ρ ≠ 0)
    (hQ : q0 ^ 2 - c * q1 ^ 2 = m * (p ^ 2 - 1)) :
    Uc c ((-(2 * p) / (2 * p ^ 2 - 1)) * q0) ((-(2 * p) / (2 * p ^ 2 - 1)) * q1) * G1 c m p q0 q1 =
      Td (1 / (ρ * (2 * p ^ 2 - 1))) (1 / ρ) * G2 c m ρ p q0 q1 := by
  have h2p' : p ^ 2 * 2 - 1 ≠ 0 := by intro h; apply h2p; linear_combination h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Uc, G1, G2, Td, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal_apply]
  all_goals (try field_simp)
  all_goals first | ring1 | linear_combination (-(2 * p)) * hQ

theorem chain_low_id (c m ρ p q0 q1 : F) (hm : m ≠ 0) (h2p : 2 * p ^ 2 - 1 ≠ 0) (hρ : ρ ≠ 0)
    (hQ : q0 ^ 2 - c * q1 ^ 2 = m * (p ^ 2 - 1)) :
    Lc c ((-(2 * p) / (m * (2 * p ^ 2 - 1))) * q0) (-((-(2 * p) / (m * (2 * p ^ 2 - 1))) * q1)) *
        G1 c m p q0 q1 = Td (1 / ρ) (1 / (ρ * (2 * p ^ 2 - 1))) * G2' c m ρ p q0 q1 := by
  have h2p' : p ^ 2 * 2 - 1 ≠ 0 := by intro h; apply h2p; linear_combination h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Lc, G1, G2', Td, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal_apply]
  all_goals (try field_simp)
  all_goals first | ring1 | linear_combination (-(2 * p)) * hQ

theorem mem_of_conj {G : Type*} [Group G] (Γ : Subgroup G) {D h u : G} (hD : D ∈ Γ) (hh : h ∈ Γ)
    (e : D * h = u * D) : u ∈ Γ := by
  have : u = D * h * D⁻¹ := by rw [e]; group
  rw [this]
  exact Γ.mul_mem (Γ.mul_mem hD hh) (Γ.inv_mem hD)

theorem upper_closure [Finite F] (hF4 : Nat.card F % 4 = 3) (c : F)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 4) F))
    (H5 : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * Xr c = Xr c * (g : Matrix (Fin 4) (Fin 4) F) →
      (g : Matrix (Fin 4) (Fin 4) F) * Z0 c = Z0 c * (g : Matrix (Fin 4) (Fin 4) F) → g ∈ Γ) :
    (∀ s t s' t' : F, Uel (!![s, c * t; t, s]) ∈ Γ → Uel (!![s', c * t'; t', s']) ∈ Γ →
      Uel (!![s + s', c * (t + t'); t + t', s + s']) ∈ Γ) ∧
    (∀ s t α : F, α ≠ 0 → Uel (!![s, c * t; t, s]) ∈ Γ → Uel (!![α * s, c * (α * t); α * t, α * s]) ∈ Γ) ∧
    (∀ (u0 u1 : F), u0 ^ 2 - c * u1 ^ 2 = 1 → ∀ s t : F, Uel (!![s, c * t; t, s]) ∈ Γ →
      Uel (!![u0 * s + c * u1 * t, c * (u1 * s + u0 * t); u1 * s + u0 * t, u0 * s + c * u1 * t]) ∈ Γ) := by
  classical
  have := Fintype.ofFinite F
  refine ⟨fun s t s' t' h h' => ?_, fun s t α hα h => ?_, fun u0 u1 hu s t h => ?_⟩
  · have e : (!![s, c * t; t, s] : Matrix (Fin 2) (Fin 2) F) + !![s', c * t'; t', s'] =
        !![s + s', c * (t + t'); t + t', s + s'] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
      all_goals ring
    rw [← e, ← Uel_add]
    exact Γ.mul_mem h h'
  · obtain ⟨d, hd⟩ : ∃ d : F, (α * (d * d) = 1 ∨ α * (d * d) = -1) := by
      have hα' : α⁻¹ ≠ 0 := inv_ne_zero hα
      rcases isSquare_or_neg (Nat.card_eq_fintype_card (α := F) ▸ hF4) (a := α⁻¹) with ⟨r, hr⟩ | ⟨r, hr⟩
      · refine ⟨r, Or.inl ?_⟩
        rw [← hr]; field_simp
      · refine ⟨r, Or.inr ?_⟩
        have : α * (r * r) = α * (-α⁻¹) := by rw [← hr]
        rw [this]; field_simp
    have hd0 : d ≠ 0 := by
      rintro rfl
      rcases hd with h0 | h0 <;> simp at h0
    have hdet : (Td (α * d) d).det = 1 := by
      rw [det_Td]
      rcases hd with h0 | h0
      · linear_combination (α * (d * d) + 1) * h0
      · linear_combination (α * (d * d) - 1) * h0
    let D : Matrix.SpecialLinearGroup (Fin 4) F := ⟨Td (α * d) d, hdet⟩
    have hD : D ∈ Γ := H5 D (Td_comm_X c _ _) (Td_comm_Z c _ _)
    refine mem_of_conj Γ hD h ?_
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Uel_eq_Uc, Uel_eq_Uc]
    have := Td_Uc c (α * d) d s t hd0
    have hdd : α * d / d = α := by field_simp
    rw [hdd] at this
    exact this
  · have hdet : (Tu c u0 u1).det = 1 := by rw [det_Tu]; exact hu
    let D : Matrix.SpecialLinearGroup (Fin 4) F := ⟨Tu c u0 u1, hdet⟩
    have hD : D ∈ Γ := H5 D (Tu_comm_X c _ _) (Tu_comm_Z c _ _)
    refine mem_of_conj Γ hD h ?_
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Uel_eq_Uc, Uel_eq_Uc]
    exact Tu_Uc c u0 u1 s t

theorem lower_closure [Finite F] (hF4 : Nat.card F % 4 = 3) (c : F)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 4) F))
    (H5 : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * Xr c = Xr c * (g : Matrix (Fin 4) (Fin 4) F) →
      (g : Matrix (Fin 4) (Fin 4) F) * Z0 c = Z0 c * (g : Matrix (Fin 4) (Fin 4) F) → g ∈ Γ) :
    (∀ s t s' t' : F, Lel (!![s, c * t; t, s]) ∈ Γ → Lel (!![s', c * t'; t', s']) ∈ Γ →
      Lel (!![s + s', c * (t + t'); t + t', s + s']) ∈ Γ) ∧
    (∀ s t α : F, α ≠ 0 → Lel (!![s, c * t; t, s]) ∈ Γ → Lel (!![α * s, c * (α * t); α * t, α * s]) ∈ Γ) ∧
    (∀ (u0 u1 : F), u0 ^ 2 - c * u1 ^ 2 = 1 → ∀ s t : F, Lel (!![s, c * t; t, s]) ∈ Γ →
      Lel (!![u0 * s + c * u1 * t, c * (u1 * s + u0 * t); u1 * s + u0 * t, u0 * s + c * u1 * t]) ∈ Γ) := by
  classical
  have := Fintype.ofFinite F
  refine ⟨fun s t s' t' h h' => ?_, fun s t α hα h => ?_, fun u0 u1 hu s t h => ?_⟩
  · have e : (!![s, c * t; t, s] : Matrix (Fin 2) (Fin 2) F) + !![s', c * t'; t', s'] =
        !![s + s', c * (t + t'); t + t', s + s'] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
      all_goals ring
    rw [← e, ← Lel_add]
    exact Γ.mul_mem h h'
  · obtain ⟨d, hd⟩ : ∃ d : F, (α * (d * d) = 1 ∨ α * (d * d) = -1) := by
      have hα' : α⁻¹ ≠ 0 := inv_ne_zero hα
      rcases isSquare_or_neg (Nat.card_eq_fintype_card (α := F) ▸ hF4) (a := α⁻¹) with ⟨r, hr⟩ | ⟨r, hr⟩
      · refine ⟨r, Or.inl ?_⟩
        rw [← hr]; field_simp
      · refine ⟨r, Or.inr ?_⟩
        have : α * (r * r) = α * (-α⁻¹) := by rw [← hr]
        rw [this]; field_simp
    have hd0 : d ≠ 0 := by
      rintro rfl
      rcases hd with h0 | h0 <;> simp at h0
    have hdet : (Td d (α * d)).det = 1 := by
      rw [det_Td]
      rcases hd with h0 | h0
      · linear_combination (α * (d * d) + 1) * h0
      · linear_combination (α * (d * d) - 1) * h0
    let D : Matrix.SpecialLinearGroup (Fin 4) F := ⟨Td d (α * d), hdet⟩
    have hD : D ∈ Γ := H5 D (Td_comm_X c _ _) (Td_comm_Z c _ _)
    refine mem_of_conj Γ hD h ?_
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Lel_eq_Lc, Lel_eq_Lc]
    have := Td_Lc c d (α * d) s t hd0
    have hdd : α * d / d = α := by field_simp
    rw [hdd] at this
    exact this
  · have hdet : (Tu c u0 (-u1)).det = 1 := by rw [det_Tu]; linear_combination hu
    let D : Matrix.SpecialLinearGroup (Fin 4) F := ⟨Tu c u0 (-u1), hdet⟩
    have hD : D ∈ Γ := H5 D (Tu_comm_X c _ _) (Tu_comm_Z c _ _)
    refine mem_of_conj Γ hD h ?_
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Lel_eq_Lc, Lel_eq_Lc]
    have := Tu_Lc c u0 u1 s t hu
    rw [show s * u0 + c * t * u1 = u0 * s + c * u1 * t by ring,
      show s * u1 + t * u0 = u1 * s + u0 * t by ring] at this
    exact this

theorem exists_chain_data [Finite F] (hF : ringChar F ≠ 2) (hF4 : Nat.card F % 4 = 3) (h7 : 7 ≤ Nat.card F)
    {c : F} (hc0 : c ≠ 0) (m : F) :
    ∃ p q0 q1 ρ : F, p ≠ 0 ∧ p ^ 2 ≠ 1 ∧ 2 * p ^ 2 - 1 ≠ 0 ∧ q0 ^ 2 - c * q1 ^ 2 = m * (p ^ 2 - 1) ∧
      ρ ≠ 0 ∧ (ρ ^ 2 * (2 * p ^ 2 - 1)) ^ 2 = 1 := by
  classical
  have := Fintype.ofFinite F
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  obtain ⟨p, hp0, hp1, hp2⟩ := exists_good_p h2 h7
  have h2p : 2 * p ^ 2 - 1 ≠ 0 := fun h => hp2 (by linear_combination h)
  obtain ⟨q0, q1, hQ⟩ := exists_norm_eq hF hc0 (m * (p ^ 2 - 1))
  have hε : (2 * p ^ 2 - 1)⁻¹ ≠ 0 := inv_ne_zero h2p
  rcases isSquare_or_neg (Nat.card_eq_fintype_card (α := F) ▸ hF4) (a := (2 * p ^ 2 - 1)⁻¹) with
    ⟨r, hr⟩ | ⟨r, hr⟩
  · have hr0 : r ≠ 0 := by rintro rfl; apply hε; rw [hr]; simp
    refine ⟨p, q0, q1, r, hp0, hp1, h2p, hQ, hr0, ?_⟩
    have : r ^ 2 * (2 * p ^ 2 - 1) = 1 := by
      rw [sq, ← hr]; field_simp
    rw [this]; norm_num
  · have hr0 : r ≠ 0 := by
      rintro rfl
      apply hε
      have h0 : -(2 * p ^ 2 - 1)⁻¹ = 0 := by simpa using hr
      exact neg_eq_zero.1 h0
    refine ⟨p, q0, q1, r, hp0, hp1, h2p, hQ, hr0, ?_⟩
    have : r ^ 2 * (2 * p ^ 2 - 1) = -1 := by
      rw [sq, ← hr]; field_simp
    rw [this]; norm_num

theorem base_up (c m p q0 q1 ρ : F) (hm : m ≠ 0) (h2p : 2 * p ^ 2 - 1 ≠ 0) (hρ0 : ρ ≠ 0)
    (hQ : q0 ^ 2 - c * q1 ^ 2 = m * (p ^ 2 - 1)) (hρ : (ρ ^ 2 * (2 * p ^ 2 - 1)) ^ 2 = 1)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 4) F))
    (H1 : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * Xr c = Xr c * (g : Matrix (Fin 4) (Fin 4) F) →
      (g : Matrix (Fin 4) (Fin 4) F) * Yr m = Yr m * (g : Matrix (Fin 4) (Fin 4) F) → g ∈ Γ)
    (H2 : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * Xr c = Xr c * (g : Matrix (Fin 4) (Fin 4) F) →
      (g : Matrix (Fin 4) (Fin 4) F) * (Yr m * Z0 c) = (Yr m * Z0 c) * (g : Matrix (Fin 4) (Fin 4) F) → g ∈ Γ)
    (H5 : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * Xr c = Xr c * (g : Matrix (Fin 4) (Fin 4) F) →
      (g : Matrix (Fin 4) (Fin 4) F) * Z0 c = Z0 c * (g : Matrix (Fin 4) (Fin 4) F) → g ∈ Γ) :
    Uel (!![(-(2 * p) / (2 * p ^ 2 - 1)) * q0, c * ((-(2 * p) / (2 * p ^ 2 - 1)) * q1);
      (-(2 * p) / (2 * p ^ 2 - 1)) * q1, (-(2 * p) / (2 * p ^ 2 - 1)) * q0]) ∈ Γ := by
  have hnQ : (q0 ^ 2 - c * q1 ^ 2) / m = p ^ 2 - 1 := by rw [hQ]; field_simp
  have hd1 : (G1 c m p q0 q1).det = 1 := by rw [det_G1 c m p q0 q1 hm, hnQ]; ring
  have hd2 : (G2 c m ρ p q0 q1).det = 1 := by
    rw [det_G2 c m ρ p q0 q1 hm, hnQ]
    have e : p ^ 2 + (p ^ 2 - 1) = 2 * p ^ 2 - 1 := by ring
    rw [e]; exact hρ
  have hd3 : (Td (1 / (ρ * (2 * p ^ 2 - 1))) (1 / ρ)).det = 1 := by
    rw [det_Td]
    have : (1 / (ρ * (2 * p ^ 2 - 1))) * (1 / (ρ * (2 * p ^ 2 - 1))) * (1 / ρ * (1 / ρ)) =
        1 / (ρ ^ 2 * (2 * p ^ 2 - 1)) ^ 2 := by field_simp
    rw [this, hρ]; norm_num
  let g1 : Matrix.SpecialLinearGroup (Fin 4) F := ⟨G1 c m p q0 q1, hd1⟩
  let g2 : Matrix.SpecialLinearGroup (Fin 4) F := ⟨G2 c m ρ p q0 q1, hd2⟩
  let tt : Matrix.SpecialLinearGroup (Fin 4) F := ⟨Td (1 / (ρ * (2 * p ^ 2 - 1))) (1 / ρ), hd3⟩
  have hg1 : g1 ∈ Γ := H1 g1 (G1_comm_X c m p q0 q1 hm) (G1_comm_Y c m p q0 q1 hm)
  have hg2 : g2 ∈ Γ := H2 g2 (G2_comm_X c m ρ p q0 q1 hm) (G2_comm_YZ c m ρ p q0 q1 hm)
  have hgt : tt ∈ Γ := H5 tt (Td_comm_X c _ _) (Td_comm_Z c _ _)
  have hid : Uel (!![(-(2 * p) / (2 * p ^ 2 - 1)) * q0, c * ((-(2 * p) / (2 * p ^ 2 - 1)) * q1);
      (-(2 * p) / (2 * p ^ 2 - 1)) * q1, (-(2 * p) / (2 * p ^ 2 - 1)) * q0]) * g1 = tt * g2 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Uel_eq_Uc]
    exact chain_up_id c m ρ p q0 q1 hm h2p hρ0 hQ
  rw [eq_mul_inv_of_mul_eq hid]
  exact Γ.mul_mem (Γ.mul_mem hgt hg2) (Γ.inv_mem hg1)

theorem base_low (c m p q0 q1 ρ : F) (hm : m ≠ 0) (h2p : 2 * p ^ 2 - 1 ≠ 0) (hρ0 : ρ ≠ 0)
    (hQ : q0 ^ 2 - c * q1 ^ 2 = m * (p ^ 2 - 1)) (hρ : (ρ ^ 2 * (2 * p ^ 2 - 1)) ^ 2 = 1)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 4) F))
    (H1 : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * Xr c = Xr c * (g : Matrix (Fin 4) (Fin 4) F) →
      (g : Matrix (Fin 4) (Fin 4) F) * Yr m = Yr m * (g : Matrix (Fin 4) (Fin 4) F) → g ∈ Γ)
    (H2 : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * Xr c = Xr c * (g : Matrix (Fin 4) (Fin 4) F) →
      (g : Matrix (Fin 4) (Fin 4) F) * (Yr m * Z0 c) = (Yr m * Z0 c) * (g : Matrix (Fin 4) (Fin 4) F) → g ∈ Γ)
    (H5 : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * Xr c = Xr c * (g : Matrix (Fin 4) (Fin 4) F) →
      (g : Matrix (Fin 4) (Fin 4) F) * Z0 c = Z0 c * (g : Matrix (Fin 4) (Fin 4) F) → g ∈ Γ) :
    Lel (!![(-(2 * p) / (m * (2 * p ^ 2 - 1))) * q0, c * (-((-(2 * p) / (m * (2 * p ^ 2 - 1))) * q1));
      -((-(2 * p) / (m * (2 * p ^ 2 - 1))) * q1), (-(2 * p) / (m * (2 * p ^ 2 - 1))) * q0]) ∈ Γ := by
  have hnQ : (q0 ^ 2 - c * q1 ^ 2) / m = p ^ 2 - 1 := by rw [hQ]; field_simp
  have hd1 : (G1 c m p q0 q1).det = 1 := by rw [det_G1 c m p q0 q1 hm, hnQ]; ring
  have hd2 : (G2' c m ρ p q0 q1).det = 1 := by
    rw [det_G2' c m ρ p q0 q1 hm, hnQ]
    have e : p ^ 2 + (p ^ 2 - 1) = 2 * p ^ 2 - 1 := by ring
    rw [e]; exact hρ
  have hd3 : (Td (1 / ρ) (1 / (ρ * (2 * p ^ 2 - 1)))).det = 1 := by
    rw [det_Td]
    have : (1 / ρ) * (1 / ρ) * (1 / (ρ * (2 * p ^ 2 - 1)) * (1 / (ρ * (2 * p ^ 2 - 1)))) =
        1 / (ρ ^ 2 * (2 * p ^ 2 - 1)) ^ 2 := by field_simp
    rw [this, hρ]; norm_num
  let g1 : Matrix.SpecialLinearGroup (Fin 4) F := ⟨G1 c m p q0 q1, hd1⟩
  let g2 : Matrix.SpecialLinearGroup (Fin 4) F := ⟨G2' c m ρ p q0 q1, hd2⟩
  let tt : Matrix.SpecialLinearGroup (Fin 4) F := ⟨Td (1 / ρ) (1 / (ρ * (2 * p ^ 2 - 1))), hd3⟩
  have hg1 : g1 ∈ Γ := H1 g1 (G1_comm_X c m p q0 q1 hm) (G1_comm_Y c m p q0 q1 hm)
  have hg2 : g2 ∈ Γ := H2 g2 (G2'_comm_X c m ρ p q0 q1 hm) (G2'_comm_YZ c m ρ p q0 q1 hm)
  have hgt : tt ∈ Γ := H5 tt (Td_comm_X c _ _) (Td_comm_Z c _ _)
  have hid : Lel (!![(-(2 * p) / (m * (2 * p ^ 2 - 1))) * q0, c * (-((-(2 * p) / (m * (2 * p ^ 2 - 1))) * q1));
      -((-(2 * p) / (m * (2 * p ^ 2 - 1))) * q1), (-(2 * p) / (m * (2 * p ^ 2 - 1))) * q0]) * g1 = tt * g2 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Lel_eq_Lc]
    exact chain_low_id c m ρ p q0 q1 hm h2p hρ0 hQ
  rw [eq_mul_inv_of_mul_eq hid]
  exact Γ.mul_mem (Γ.mul_mem hgt hg2) (Γ.inv_mem hg1)

theorem b1_comm_XZ (c a : F) :
    ((b1 a : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (Xr c * Z0 c) =
      (Xr c * Z0 c) * (b1 a : Matrix.SpecialLinearGroup (Fin 4) F) := by
  unfold b1 tv
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Xr, Z0, Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply, Matrix.add_apply]
  all_goals ring

theorem b2_comm_XZ (c a : F) (hc : c ≠ 0) :
    ((b2 c a : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (Xr c * Z0 c) =
      (Xr c * Z0 c) * (b2 c a : Matrix.SpecialLinearGroup (Fin 4) F) := by
  unfold b2 tv
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Xr, Z0, Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply, Matrix.add_apply]
  all_goals field_simp

theorem tv_zero' (i j : Fin 4) (h : i ≠ j) : tv i j h (0 : F) = 1 := by
  apply Subtype.ext; simp [tv]

theorem top_of_nsq_model [Finite F] (hF : ringChar F ≠ 2) (hF4 : Nat.card F % 4 = 3)
    (h7 : 7 ≤ Nat.card F) {c m : F} (hc : ¬ IsSquare c) (hm : m ≠ 0)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 4) F))
    (H1 : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * Xr c = Xr c * (g : Matrix (Fin 4) (Fin 4) F) →
      (g : Matrix (Fin 4) (Fin 4) F) * Yr m = Yr m * (g : Matrix (Fin 4) (Fin 4) F) → g ∈ Γ)
    (H2 : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * Xr c = Xr c * (g : Matrix (Fin 4) (Fin 4) F) →
      (g : Matrix (Fin 4) (Fin 4) F) * (Yr m * Z0 c) = (Yr m * Z0 c) * (g : Matrix (Fin 4) (Fin 4) F) → g ∈ Γ)
    (H3 : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * Yr m = Yr m * (g : Matrix (Fin 4) (Fin 4) F) →
      (g : Matrix (Fin 4) (Fin 4) F) * (Xr c * Z0 c) = (Xr c * Z0 c) * (g : Matrix (Fin 4) (Fin 4) F) → g ∈ Γ)
    (H4 : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * (Xr c * Yr m) = (Xr c * Yr m) * (g : Matrix (Fin 4) (Fin 4) F) →
      (g : Matrix (Fin 4) (Fin 4) F) * (Xr c * Z0 c) = (Xr c * Z0 c) * (g : Matrix (Fin 4) (Fin 4) F) → g ∈ Γ)
    (H5 : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * Xr c = Xr c * (g : Matrix (Fin 4) (Fin 4) F) →
      (g : Matrix (Fin 4) (Fin 4) F) * Z0 c = Z0 c * (g : Matrix (Fin 4) (Fin 4) F) → g ∈ Γ) :
    Γ = ⊤ := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hc0 : c ≠ 0 := ne_zero_of_not_isSquare hc
  have hc1 : c ≠ 1 := fun h => hc ⟨1, by rw [h]; ring⟩
  obtain ⟨p, q0, q1, ρ, hp0, hp1, h2p, hQ, hρ0, hρ⟩ := exists_chain_data hF hF4 h7 hc0 m
  have hup := base_up c m p q0 q1 ρ hm h2p hρ0 hQ hρ Γ H1 H2 H5
  have hlow := base_low c m p q0 q1 ρ hm h2p hρ0 hQ hρ Γ H1 H2 H5
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
  have hqq : q0 ≠ 0 ∨ q1 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨h0, h1⟩ := hcon
    have : m * (p ^ 2 - 1) = 0 := by rw [← hQ, h0, h1]; ring
    rcases mul_eq_zero.1 this with h | h
    · exact hm h
    · exact hp1 (by linear_combination h)
  have hκ : (-(2 * p) / (2 * p ^ 2 - 1)) ≠ 0 :=
    div_ne_zero (neg_ne_zero.2 (mul_ne_zero h2 hp0)) h2p
  have hκl : (-(2 * p) / (m * (2 * p ^ 2 - 1))) ≠ 0 :=
    div_ne_zero (neg_ne_zero.2 (mul_ne_zero h2 hp0)) (mul_ne_zero hm h2p)
  have hPall := span_all (P := fun s t => Uel (!![s, c * t; t, s]) ∈ Γ) hc hu1 hzeroU hadd hscale
    (fun s t h => hmul _ _ hu s t h) (s0 := (-(2 * p) / (2 * p ^ 2 - 1)) * q0)
    (t0 := (-(2 * p) / (2 * p ^ 2 - 1)) * q1)
    (by rcases hqq with h | h
        · exact Or.inl (mul_ne_zero hκ h)
        · exact Or.inr (mul_ne_zero hκ h)) hup
  have hQall := span_all (P := fun s t => Lel (!![s, c * t; t, s]) ∈ Γ) hc hu1 hzeroL hadd' hscale'
    (fun s t h => hmul' _ _ hu s t h) (s0 := (-(2 * p) / (m * (2 * p ^ 2 - 1))) * q0)
    (t0 := -((-(2 * p) / (m * (2 * p ^ 2 - 1))) * q1))
    (by rcases hqq with h | h
        · exact Or.inl (mul_ne_zero hκl h)
        · exact Or.inr (by simpa using mul_ne_zero hκl h)) hlow
  refine top_of_generators h2 hc0 Γ (fun s => ?_) (fun t => ?_) (fun s => ?_) (fun t => ?_)
    (fun a => H3 _ (b1_comm m a) (b1_comm_XZ c a)) (fun a => H4 _ (b2_comm c m a hc0) (b2_comm_XZ c a hc0))
  · have := hPall s 0
    simpa [Uel, a1, tv_zero'] using this
  · have := hPall 0 t
    simpa [Uel, a2, tv_zero', mul_comm] using this
  · have := hQall s 0
    simpa [Lel, l1, tv_zero'] using this
  · have := hQall 0 t
    simpa [Lel, l2, tv_zero', mul_comm] using this

end GenLocL4Q

end CFSG.GH74.Generic.BProg.B2
