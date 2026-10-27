module

public import CFSG.Assembly.Defs
public import CFSG.LieType.Chevalley.RankOneGaussian

public noncomputable section

namespace CFSG.ClassicalInvolution.G2D4Models

open CFSG.LieType.Chevalley Matrix Polynomial
open scoped MatrixGroups

section Antidiag

variable {F : Type} [Field F]

theorem conj_vSL_step (τ : F) (p q r : F) :
    ((vSL τ : SL2 F) : Matrix (Fin 2) (Fin 2) F) * !![p, q; r, -p] *
      ((((vSL τ)⁻¹ : SL2 F)) : Matrix (Fin 2) (Fin 2) F) =
      !![p - τ * q, q; r + 2 * τ * p - τ ^ 2 * q, -(p - τ * q)] := by
  rw [Matrix.SpecialLinearGroup.coe_inv, coe_vSL, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem conj_uSL_step (σ : F) (p q r : F) :
    ((uSL σ : SL2 F) : Matrix (Fin 2) (Fin 2) F) * !![p, q; r, -p] *
      ((((uSL σ)⁻¹ : SL2 F)) : Matrix (Fin 2) (Fin 2) F) =
      !![p + σ * r, q - 2 * σ * p - σ ^ 2 * r; r, -(p + σ * r)] := by
  rw [Matrix.SpecialLinearGroup.coe_inv, coe_uSL, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem exists_antidiag_conj (h2 : (2 : F) ≠ 0) (M : Matrix (Fin 2) (Fin 2) F) {l : F}
    (hM : M * M = l • 1) (hl : l ≠ 0) (hns : ∀ c : F, M ≠ c • 1) :
    ∃ (R : SL2 F) (b c : F), b ≠ 0 ∧ c ≠ 0 ∧
      (R : Matrix (Fin 2) (Fin 2) F) * M * ((R⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) =
        !![0, b; c, 0] := by
  have hM' := Matrix.eta_fin_two M
  set p := M 0 0 with hp
  set q := M 0 1 with hq
  set r := M 1 0 with hr
  set s := M 1 1 with hs
  have e00 : p * p + q * r = l := by
    have := congrFun (congrFun hM 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two, hp, hq, hr, hs] using this
  have e11 : r * q + s * s = l := by
    have := congrFun (congrFun hM 1) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two, hp, hq, hr, hs] using this
  have e01 : q * (p + s) = 0 := by
    have := congrFun (congrFun hM 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at this
    linear_combination this
  have e10 : r * (p + s) = 0 := by
    have := congrFun (congrFun hM 1) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at this
    linear_combination this
  have htr : s = -p := by
    by_contra hne
    have hps : p + s ≠ 0 := fun h => hne (by linear_combination h)
    have hq0 : q = 0 := (mul_eq_zero.mp e01).resolve_right hps
    have hr0 : r = 0 := (mul_eq_zero.mp e10).resolve_right hps
    have hpp : p * p = s * s := by
      rw [hq0] at e00; rw [hr0] at e11; linear_combination e00 - e11
    have hps2 : (p - s) * (p + s) = 0 := by linear_combination hpp
    have hpe : p = s := by
      have := (mul_eq_zero.mp hps2).resolve_right hps
      linear_combination this
    apply hns p
    rw [hM']
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hq0, hr0, hpe]
  rw [htr] at hM'
  have h4 : (4 : F) ≠ 0 := by
    have : (4 : F) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  have hex : ∃ τ : F, r + 2 * τ * p - τ ^ 2 * q ≠ 0 := by
    by_contra hall
    have hall' : ∀ τ : F, r + 2 * τ * p - τ ^ 2 * q = 0 := fun τ =>
      not_not.mp (not_exists.mp hall τ)
    have h0 := hall' 0
    have h1 := hall' 1
    have h1' := hall' (-1)
    have hr0 : r = 0 := by simpa using h0
    have hp0 : p = 0 := by
      have : 4 * p = 0 := by
        rw [hr0] at h1 h1'
        linear_combination (h1 - h1')
      exact (mul_eq_zero.mp this).resolve_left h4
    have hq0 : q = 0 := by
      rw [hr0, hp0] at h1; linear_combination -h1
    apply hl
    rw [← e00, hp0, hq0]; ring
  obtain ⟨τ, hτ⟩ := hex
  set r₁ := r + 2 * τ * p - τ ^ 2 * q with hr₁
  set p₁ := p - τ * q with hp₁
  have hstep1 : ((vSL τ : SL2 F) : Matrix (Fin 2) (Fin 2) F) * M *
      ((((vSL τ)⁻¹ : SL2 F)) : Matrix (Fin 2) (Fin 2) F) = !![p₁, q; r₁, -p₁] := by
    rw [hM', conj_vSL_step]
  have hdet : p₁ * p₁ + q * r₁ = l := by
    rw [hp₁, hr₁, ← e00]; ring
  refine ⟨uSL (-p₁ / r₁) * vSL τ, q + p₁ ^ 2 / r₁, r₁, ?_, hτ, ?_⟩
  · have : q + p₁ ^ 2 / r₁ = l / r₁ := by
      field_simp; linear_combination hdet
    rw [this]; exact div_ne_zero hl hτ
  · have hmul : (((uSL (-p₁ / r₁) * vSL τ : SL2 F)) : Matrix (Fin 2) (Fin 2) F) * M *
        ((((uSL (-p₁ / r₁) * vSL τ)⁻¹ : SL2 F)) : Matrix (Fin 2) (Fin 2) F) =
        ((uSL (-p₁ / r₁) : SL2 F) : Matrix (Fin 2) (Fin 2) F) *
          (((vSL τ : SL2 F) : Matrix (Fin 2) (Fin 2) F) * M *
            ((((vSL τ)⁻¹ : SL2 F)) : Matrix (Fin 2) (Fin 2) F)) *
          ((((uSL (-p₁ / r₁))⁻¹ : SL2 F)) : Matrix (Fin 2) (Fin 2) F) := by
      rw [_root_.mul_inv_rev]
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc]
    rw [hmul, hstep1, conj_uSL_step]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> ring

end Antidiag

section Conic

variable {F : Type} [Field F]

theorem exists_eval_ne_zero_fin [Finite F] (f : F[X]) (hf : f ≠ 0)
    (hd : f.natDegree < Nat.card F) : ∃ m : F, f.eval m ≠ 0 := by
  have := Fintype.ofFinite F
  exact Polynomial.exists_eval_ne_zero_of_natDegree_lt_card f hf (by
    simpa [Cardinal.mk_fintype, ← Nat.card_eq_fintype_card] using hd)

theorem conic_point (κ m : F) (h : 1 - κ * m ^ 2 ≠ 0) :
    ((1 + κ * m ^ 2) / (1 - κ * m ^ 2)) ^ 2 - κ * (2 * m / (1 - κ * m ^ 2)) ^ 2 = 1 := by
  field_simp
  ring

theorem exists_conic_points [Finite F] (h11 : 11 ≤ Nat.card F) (h2 : (2 : F) ≠ 0) (κ : F) :
    ∃ u₁ v₁ u₂ v₂ : F, u₁ ^ 2 - κ * v₁ ^ 2 = 1 ∧ u₂ ^ 2 - κ * v₂ ^ 2 = 1 ∧ u₁ ≠ 0 ∧ u₂ ≠ 0 ∧
      v₁ ≠ 0 ∧ v₂ ≠ 0 ∧ v₁ ^ 2 ≠ v₂ ^ 2 := by
  have hex1 : ∃ m : F, m * ((1 + κ * m ^ 2) * (1 - κ * m ^ 2)) ≠ 0 := by
    let f : F[X] := X * ((1 + C κ * X ^ 2) * (1 - C κ * X ^ 2))
    have hf : f ≠ 0 := by
      intro h
      have := congrArg (fun p => p.coeff 1) h
      simp [f] at this
    have hdeg : f.natDegree < Nat.card F := by
      have : f.natDegree ≤ 5 := by simp only [f]; compute_degree
      omega
    obtain ⟨m, hm⟩ := exists_eval_ne_zero_fin f hf hdeg
    exact ⟨m, by simpa [f] using hm⟩
  obtain ⟨m₁, hm₁⟩ := hex1
  have hm₁0 : m₁ ≠ 0 := left_ne_zero_of_mul hm₁
  have hm₁p : 1 + κ * m₁ ^ 2 ≠ 0 := left_ne_zero_of_mul (right_ne_zero_of_mul hm₁)
  have hm₁m : 1 - κ * m₁ ^ 2 ≠ 0 := right_ne_zero_of_mul (right_ne_zero_of_mul hm₁)
  have hex2 : ∃ m : F, m * ((1 + κ * m ^ 2) * (1 - κ * m ^ 2)) *
      ((m₁ - m) * (1 + κ * m₁ * m) * ((m₁ + m) * (1 - κ * m₁ * m))) ≠ 0 := by
    let f : F[X] := X * ((1 + C κ * X ^ 2) * (1 - C κ * X ^ 2)) *
      ((C m₁ - X) * (1 + C (κ * m₁) * X) * ((C m₁ + X) * (1 - C (κ * m₁) * X)))
    have hf : f ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero X_ne_zero (mul_ne_zero ?_ ?_))
        (mul_ne_zero (mul_ne_zero ?_ ?_) (mul_ne_zero ?_ ?_))
      · intro h; simpa using congrArg (fun p => p.coeff 0) h
      · intro h; simpa using congrArg (fun p => p.coeff 0) h
      · intro h; simpa using congrArg (fun p => p.coeff 1) h
      · intro h; simpa using congrArg (fun p => p.coeff 0) h
      · intro h; simpa using congrArg (fun p => p.coeff 1) h
      · intro h; simpa using congrArg (fun p => p.coeff 0) h
    have hdeg : f.natDegree < Nat.card F := by
      have : f.natDegree ≤ 9 := by simp only [f]; compute_degree
      omega
    obtain ⟨m, hm⟩ := exists_eval_ne_zero_fin f hf hdeg
    exact ⟨m, by simpa [f] using hm⟩
  obtain ⟨m₂, hm₂⟩ := hex2
  have hm₂0 : m₂ ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hm₂)
  have hm₂p : 1 + κ * m₂ ^ 2 ≠ 0 :=
    left_ne_zero_of_mul (right_ne_zero_of_mul (left_ne_zero_of_mul hm₂))
  have hm₂m : 1 - κ * m₂ ^ 2 ≠ 0 :=
    right_ne_zero_of_mul (right_ne_zero_of_mul (left_ne_zero_of_mul hm₂))
  have hr := right_ne_zero_of_mul hm₂
  have hf1 : m₁ - m₂ ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hr)
  have hf2 : 1 + κ * m₁ * m₂ ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hr)
  have hf3 : m₁ + m₂ ≠ 0 := left_ne_zero_of_mul (right_ne_zero_of_mul hr)
  have hf4 : 1 - κ * m₁ * m₂ ≠ 0 := right_ne_zero_of_mul (right_ne_zero_of_mul hr)
  refine ⟨(1 + κ * m₁ ^ 2) / (1 - κ * m₁ ^ 2), 2 * m₁ / (1 - κ * m₁ ^ 2),
    (1 + κ * m₂ ^ 2) / (1 - κ * m₂ ^ 2), 2 * m₂ / (1 - κ * m₂ ^ 2),
    conic_point κ m₁ hm₁m, conic_point κ m₂ hm₂m, div_ne_zero hm₁p hm₁m, div_ne_zero hm₂p hm₂m,
    div_ne_zero (mul_ne_zero h2 hm₁0) hm₁m, div_ne_zero (mul_ne_zero h2 hm₂0) hm₂m, ?_⟩
  intro heq
  have h3 : (2 * m₁) ^ 2 * (1 - κ * m₂ ^ 2) ^ 2 = (2 * m₂) ^ 2 * (1 - κ * m₁ ^ 2) ^ 2 := by
    rw [div_pow, div_pow, div_eq_div_iff (pow_ne_zero 2 hm₁m) (pow_ne_zero 2 hm₂m)] at heq
    linear_combination heq
  have h4 : 4 * ((m₁ - m₂) * (1 + κ * m₁ * m₂) * ((m₁ + m₂) * (1 - κ * m₁ * m₂))) = 0 := by
    linear_combination h3
  have h44 : (4 : F) ≠ 0 := by
    have : (4 : F) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  exact (mul_ne_zero h44 (mul_ne_zero (mul_ne_zero hf1 hf2) (mul_ne_zero hf3 hf4))) h4

end Conic

section Torus

variable {F : Type} [Field F]

@[expose] def normTorusSL (κ : F) (s : Fˣ) (u v : F) (h : u ^ 2 - κ * v ^ 2 = 1) : SL2 F :=
  ⟨!![u, (s : F) * v; ((s⁻¹ : Fˣ) : F) * κ * v, u], by
    rw [det_fin_two]
    simp only [of_apply, cons_val', cons_val_zero, cons_val_fin_one, cons_val_one]
    have hs : (s : F) * ((s⁻¹ : Fˣ) : F) = 1 := by simp
    linear_combination h - κ * v ^ 2 * hs⟩

theorem coe_normTorusSL (κ : F) (s : Fˣ) (u v : F) (h : u ^ 2 - κ * v ^ 2 = 1) :
    ((normTorusSL κ s u v h : SL2 F) : Matrix (Fin 2) (Fin 2) F) =
      !![u, (s : F) * v; ((s⁻¹ : Fˣ) : F) * κ * v, u] := rfl

theorem uSL_mul_uSL_tt (a b : F) : uSL a * uSL b = uSL (a + b) := by
  apply SL2_ext <;> simp [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, Matrix.mul_apply,
    Fin.sum_univ_two, add_comm]

theorem uSL_inv_tt (a : F) : (uSL a)⁻¹ = uSL (-a) := by
  rw [inv_eq_iff_mul_eq_one, uSL_mul_uSL_tt, add_neg_cancel]
  apply SL2_ext <;> simp [coe_uSL]

theorem uSL_zero_tt : (uSL (0 : F) : SL2 F) = 1 := by
  apply SL2_ext <;> simp [coe_uSL]

theorem uSL_sub_tt (a b : F) : uSL (a - b) = uSL a * (uSL b)⁻¹ := by
  rw [uSL_inv_tt, uSL_mul_uSL_tt, sub_eq_add_neg]

theorem HSL_conj_uSL_tt (t : Fˣ) (c : F) :
    HSL t * uSL c * (HSL t)⁻¹ = uSL ((t : F) ^ 2 * c) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply SL2_ext <;> simp [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, coe_HSL, Matrix.mul_apply,
    Fin.sum_univ_two]
  field_simp

theorem normTorus_prod (κ : F) (u₁ v₁ u₂ v₂ : F) (h₁ : u₁ ^ 2 - κ * v₁ ^ 2 = 1)
    (h₂ : u₂ ^ 2 - κ * v₂ ^ 2 = 1) (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0)
    (r : Fˣ) (hr : (r : F) = -(u₁ * v₂) / (u₂ * v₁)) (ρ : Fˣ) (hρ : (ρ : F) = u₂ / u₁) :
    HSL ρ⁻¹ * (normTorusSL κ 1 u₁ v₁ h₁ * normTorusSL κ r u₂ v₂ h₂) =
      uSL (u₁ * (v₁ ^ 2 - v₂ ^ 2) / (u₂ ^ 2 * v₁)) := by
  have hr' : ((r⁻¹ : Fˣ) : F) = -(u₂ * v₁) / (u₁ * v₂) := by
    rw [Units.val_inv_eq_inv_val, hr, inv_div, neg_div, ← div_neg]
  have hρ' : ((ρ⁻¹ : Fˣ) : F) = u₁ / u₂ := by
    rw [Units.val_inv_eq_inv_val, hρ, inv_div]
  apply SL2_ext <;> simp [Matrix.SpecialLinearGroup.coe_mul, coe_normTorusSL, coe_HSL, coe_uSL,
    Matrix.mul_apply, Fin.sum_univ_two, hρ', hr', hr, hρ] <;> field_simp
  · linear_combination h₁
  · linear_combination (-v₂ ^ 2) * h₁ + v₁ ^ 2 * h₂
  · right; ring
  · linear_combination h₂

theorem eq_top_of_normTorus [Finite F] (h11 : 11 ≤ Nat.card F) (h2 : (2 : F) ≠ 0) (κ : Fˣ)
    {H : Subgroup (SL2 F)} (hA : ∀ t : Fˣ, HSL t ∈ H)
    (hB : ∀ (s : Fˣ) (u v : F) (h : u ^ 2 - (κ : F) * v ^ 2 = 1),
      normTorusSL (κ : F) s u v h ∈ H) :
    H = ⊤ := by
  obtain ⟨u₁, v₁, u₂, v₂, h₁, h₂, hu₁, hu₂, hv₁, hv₂, hv⟩ := exists_conic_points h11 h2 (κ : F)
  have hrne : -(u₁ * v₂) / (u₂ * v₁) ≠ 0 :=
    div_ne_zero (neg_ne_zero.2 (mul_ne_zero hu₁ hv₂)) (mul_ne_zero hu₂ hv₁)
  set r : Fˣ := Units.mk0 _ hrne with hrdef
  set ρ : Fˣ := Units.mk0 (u₂ / u₁) (div_ne_zero hu₂ hu₁) with hρdef
  set c₀ : F := u₁ * (v₁ ^ 2 - v₂ ^ 2) / (u₂ ^ 2 * v₁) with hc₀def
  have hc₀ne : c₀ ≠ 0 := by
    refine div_ne_zero (mul_ne_zero hu₁ (sub_ne_zero.2 hv)) (mul_ne_zero (pow_ne_zero 2 hu₂) hv₁)
  have hprod := normTorus_prod (κ : F) u₁ v₁ u₂ v₂ h₁ h₂ hu₁ hu₂ hv₁ hv₂ r rfl ρ rfl
  have hM₁ := hB 1 u₁ v₁ h₁
  have hc₀H : uSL c₀ ∈ H := by
    rw [← hprod]
    exact H.mul_mem (hA _) (H.mul_mem hM₁ (hB r u₂ v₂ h₂))
  have hsq : ∀ t : F, uSL (t ^ 2 * c₀) ∈ H := by
    intro t
    by_cases ht : t = 0
    · rw [ht, zero_pow two_ne_zero, zero_mul, uSL_zero_tt]
      exact H.one_mem
    · have := H.mul_mem (H.mul_mem (hA (Units.mk0 t ht)) hc₀H) (H.inv_mem (hA (Units.mk0 t ht)))
      rwa [HSL_conj_uSL_tt] at this
  have hU : ∀ c : F, uSL c ∈ H := by
    intro c
    have e : c = ((c / c₀ + 1) / 2) ^ 2 * c₀ - ((c / c₀ - 1) / 2) ^ 2 * c₀ := by
      field_simp
      ring
    rw [e, uSL_sub_tt]
    exact H.mul_mem (hsq _) (H.inv_mem (hsq _))
  have hW : (WSL : SL2 F) ∈ H := by
    have hc : ((normTorusSL (κ : F) 1 u₁ v₁ h₁ : SL2 F) : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := by
      simp only [coe_normTorusSL, of_apply, cons_val', cons_val_zero, cons_val_fin_one,
        cons_val_one, inv_one, Units.val_one, one_mul]
      exact mul_ne_zero κ.ne_zero hv₁
    obtain ⟨X, Y, hXH, hYH, hform⟩ : ∃ X Y : SL2 F, X ∈ H ∧ Y ∈ H ∧
        normTorusSL (κ : F) 1 u₁ v₁ h₁ = X * WSL * Y :=
      ⟨_, _, H.mul_mem (hU _) (hA _), hU _, eq_uSL_mul_HSL_mul_WSL_mul_uSL hc⟩
    have : (WSL : SL2 F) = X⁻¹ * normTorusSL (κ : F) 1 u₁ v₁ h₁ * Y⁻¹ := by
      rw [hform]
      group
    rw [this]
    exact H.mul_mem (H.mul_mem (H.inv_mem hXH) hM₁) (H.inv_mem hYH)
  refine eq_top_iff.mpr fun g _ => ?_
  exact SL2_induction (p := fun g : SL2 F => g ∈ H) (fun g g' => H.mul_mem) hU hA hW g

end Torus

end CFSG.ClassicalInvolution.G2D4Models
