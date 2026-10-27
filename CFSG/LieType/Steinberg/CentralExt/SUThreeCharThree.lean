module

public import CFSG.RankThree.CentralLiftU.UnitaryThreeHeisenberg
public import CFSG.LocalAnalysis.ComponentInitial.CoprimeSeriesCoverTrivialAlt
public import CFSG.LieType.Steinberg.CentralExt.FiniteFieldPairing

public section

namespace CFSG.LieType.Steinberg.CentralExt.SUThreeCharThree

open Matrix CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.RankThree.CentralLiftU

section Matrices

variable {F : Type} [Field F] (σ : F ≃+* F)

theorem heisM_zero : heisM σ (0 : F) 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [heisM]

@[expose] noncomputable def uG (a b : F) : GL (Fin 3) F :=
  ⟨heisM σ a b, heisM σ (-a) (-b - a * σ a),
    by rw [heisM_mul, map_neg, ← heisM_zero σ]; congr 1 <;> ring,
    by rw [heisM_mul, ← heisM_zero σ]; congr 1 <;> ring⟩

theorem coe_uG (a b : F) : ((uG σ a b : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = heisM σ a b :=
  rfl

theorem uG_mul (a b a' b' : F) : uG σ a b * uG σ a' b' = uG σ (a + a') (b + b' - a * σ a') :=
  Units.ext (heisM_mul σ a b a' b')

theorem uG_inv (a b : F) : (uG σ a b)⁻¹ = uG σ (-a) (-b - a * σ a) :=
  Units.ext rfl

theorem uG_zero : uG σ (0 : F) 0 = 1 :=
  Units.ext (heisM_zero σ)

theorem uG_inj {a b a' b' : F} (h : uG σ a b = uG σ a' b') : a = a' ∧ b = b' := by
  have h' := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) h
  simp only [coe_uG] at h'
  have h1 := congrFun (congrFun h' 0) 1
  have h2 := congrFun (congrFun h' 0) 2
  simp only [heisM] at h1 h2
  exact ⟨by simpa using h1, by simpa using h2⟩

theorem uG_pow_three (a b : F) : uG σ a b ^ 3 = uG σ (3 * a) (3 * b - 3 * (a * σ a)) := by
  rw [pow_three, uG_mul, uG_mul, map_add]
  congr 1 <;> ring

@[expose] noncomputable def torusMat (s : F) : Matrix (Fin 3) (Fin 3) F :=
  diagonal ![s, σ s / s, (σ s)⁻¹]

theorem torusMat_mul (s t : F) : torusMat σ s * torusMat σ t = torusMat σ (s * t) := by
  rw [torusMat, torusMat, torusMat, diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp [map_mul] <;> ring

theorem torusMat_one : torusMat σ (1 : F) = 1 := by
  rw [torusMat, ← diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

@[expose] noncomputable def torusHom : Fˣ →* GL (Fin 3) F where
  toFun s := ⟨torusMat σ s, torusMat σ (s⁻¹ : Fˣ),
    by rw [torusMat_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, torusMat_one],
    by rw [torusMat_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, torusMat_one]⟩
  map_one' := Units.ext (by
    change torusMat σ ((1 : Fˣ) : F) = 1
    rw [Units.val_one, torusMat_one])
  map_mul' s t := Units.ext (by
    change torusMat σ ((s * t : Fˣ) : F) = torusMat σ s * torusMat σ t
    rw [Units.val_mul, torusMat_mul])

theorem coe_torusHom (s : Fˣ) :
    ((torusHom σ s : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = torusMat σ s :=
  rfl

theorem coe_torusHom_inv (s : Fˣ) :
    (((torusHom σ s)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = torusMat σ (s : F)⁻¹ := by
  rw [← Units.val_inv_eq_inv_val]
  rfl

variable {σ} (hσ : ∀ c, σ (σ c) = c)
include hσ

theorem torus_conj (s : Fˣ) (a b : F) :
    torusHom σ s * uG σ a b * (torusHom σ s)⁻¹ =
      uG σ ((s : F) ^ 2 / σ s * a) (s * σ s * b) := by
  have hs : (s : F) ≠ 0 := s.ne_zero
  have hσs : σ (s : F) ≠ 0 := (map_ne_zero σ).2 hs
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_torusHom, coe_torusHom_inv, coe_uG, coe_uG]
  ext i j
  rw [torusMat, torusMat, mul_diagonal, diagonal_mul]
  fin_cases i <;> fin_cases j <;> simp [heisM, map_inv₀, map_div₀, hσ] <;> field_simp

theorem torusHom_mem (s : Fˣ) : torusHom σ s ∈ SU σ 3 := by
  have hs : (s : F) ≠ 0 := s.ne_zero
  have hσs : σ (s : F) ≠ 0 := (map_ne_zero σ).2 hs
  refine ⟨?_, ?_⟩
  · rw [coe_torusHom, torusMat, det_diagonal, Fin.prod_univ_three]
    simp
    field_simp
  · rw [coe_torusHom, torusMat, CFSG.LieType.Steinberg.conjTr_diagonal]
    ext i j
    rw [mul_diagonal, diagonal_mul]
    fin_cases i <;> fin_cases j <;> simp [antidiag, map_inv₀, map_div₀, hσ]

theorem torus_conj_neg_one (a b : F) :
    torusHom σ (-1) * uG σ a b * (torusHom σ (-1))⁻¹ = uG σ (-a) b := by
  rw [torus_conj hσ]
  congr 1 <;> simp

theorem map_norm (s : F) : σ (s * σ s) = s * σ s := by
  rw [map_mul, hσ, mul_comm]

theorem map_lam_mul_lam {s : F} (hs : s ≠ 0) : σ (s ^ 2 / σ s) * (s ^ 2 / σ s) = s * σ s := by
  have hσs : σ s ≠ 0 := (map_ne_zero σ).2 hs
  rw [map_div₀, map_pow, hσ]
  field_simp

end Matrices

section Series

variable {F : Type} [Field F] (σ : F ≃+* F)

@[expose] noncomputable def zSub : Subgroup (GL (Fin 3) F) where
  carrier := {x | ∃ c, c + σ c = 0 ∧ x = uG σ 0 c}
  mul_mem' {x y} hx hy := by
    obtain ⟨c, hc, rfl⟩ := hx
    obtain ⟨d, hd, rfl⟩ := hy
    refine ⟨c + d, by rw [map_add]; linear_combination hc + hd, ?_⟩
    rw [uG_mul]
    congr 1 <;> simp
  one_mem' := ⟨0, by simp, (uG_zero σ).symm⟩
  inv_mem' {x} hx := by
    obtain ⟨c, hc, rfl⟩ := hx
    refine ⟨-c, by rw [map_neg]; linear_combination -hc, ?_⟩
    rw [uG_inv]
    congr 1 <;> simp

@[expose] noncomputable def xSub (hσ : ∀ c, σ (σ c) = c) : Subgroup (GL (Fin 3) F) where
  carrier := {x | ∃ a b, b + σ b + σ a * a = 0 ∧ x = uG σ a b}
  mul_mem' {x y} hx hy := by
    obtain ⟨a, b, hab, rfl⟩ := hx
    obtain ⟨a', b', hab', rfl⟩ := hy
    refine ⟨a + a', b + b' - a * σ a', ?_, uG_mul σ a b a' b'⟩
    simp only [map_add, map_sub, map_mul, hσ]
    linear_combination hab + hab'
  one_mem' := ⟨0, 0, by simp, (uG_zero σ).symm⟩
  inv_mem' {x} hx := by
    obtain ⟨a, b, hab, rfl⟩ := hx
    refine ⟨-a, -b - a * σ a, ?_, uG_inv σ a b⟩
    simp only [map_neg, map_sub, map_mul, hσ]
    linear_combination -hab

@[expose] noncomputable def series (hσ : ∀ c, σ (σ c) = c) : ℕ → Subgroup (GL (Fin 3) F)
  | 0 => ⊥
  | 1 => zSub σ
  | _ => xSub σ hσ

@[expose] noncomputable def coord : ℕ → F → GL (Fin 3) F
  | 0 => fun u => uG σ 0 (u - σ u)
  | _ => fun a => uG σ a (σ a * a)

@[expose] noncomputable def wtc : ℕ → Fˣ → F
  | 0 => fun s => s * σ s
  | _ => fun s => (s : F) ^ 2 / σ s

variable {σ} (hσ : ∀ c, σ (σ c) = c)

theorem uG_mem_zSub {a b : F} (ha : a = 0) (hb : b + σ b = 0) : uG σ a b ∈ zSub σ :=
  ⟨b, hb, by rw [ha]⟩

theorem series_mono {i : ℕ} (hi : i < 2) : series σ hσ i ≤ series σ hσ (i + 1) := by
  interval_cases i
  · exact bot_le
  · rintro x ⟨c, hc, rfl⟩
    exact ⟨0, c, by rw [map_zero, zero_mul, add_zero]; exact hc, rfl⟩

include hσ in
theorem coord_conj {i : ℕ} (hi : i < 2) (s : Fˣ) (u : F) :
    torusHom σ s * coord σ i u * (torusHom σ s)⁻¹ = coord σ i (wtc σ i s * u) := by
  interval_cases i
  · change torusHom σ s * uG σ 0 (u - σ u) * (torusHom σ s)⁻¹ =
      uG σ 0 (s * σ s * u - σ (s * σ s * u))
    rw [torus_conj hσ, mul_zero, map_mul _ ((s : F) * σ s), map_norm hσ]
    congr 1
    ring
  · change torusHom σ s * uG σ u (σ u * u) * (torusHom σ s)⁻¹ =
      uG σ ((s : F) ^ 2 / σ s * u) (σ ((s : F) ^ 2 / σ s * u) * ((s : F) ^ 2 / σ s * u))
    rw [torus_conj hσ, map_mul _ ((s : F) ^ 2 / σ s)]
    congr 1
    linear_combination (-(σ u * u)) * map_lam_mul_lam hσ s.ne_zero

theorem series_inv {i : ℕ} (hi : i ≤ 2) (s : Fˣ) {x : GL (Fin 3) F} (hx : x ∈ series σ hσ i) :
    torusHom σ s * x * (torusHom σ s)⁻¹ ∈ series σ hσ i := by
  interval_cases i
  · change x ∈ (⊥ : Subgroup (GL (Fin 3) F)) at hx
    change _ ∈ (⊥ : Subgroup (GL (Fin 3) F))
    rw [Subgroup.mem_bot] at hx ⊢
    rw [hx, mul_one, mul_inv_cancel]
  · obtain ⟨c, hc, rfl⟩ := hx
    rw [torus_conj hσ]
    refine uG_mem_zSub (mul_zero _) ?_
    rw [map_mul, map_norm hσ]
    linear_combination ((s : F) * σ s) * hc
  · obtain ⟨a, b, hab, rfl⟩ := hx
    rw [torus_conj hσ]
    refine ⟨_, _, ?_, rfl⟩
    rw [map_mul _ ((s : F) * σ s), map_norm hσ, map_mul _ ((s : F) ^ 2 / σ s)]
    linear_combination ((s : F) * σ s) * hab + (σ a * a) * map_lam_mul_lam hσ s.ne_zero

theorem series_cent {i : ℕ} (hi : i < 2) {x : GL (Fin 3) F} (hx : x ∈ series σ hσ (i + 1))
    {g : GL (Fin 3) F} (hg : g ∈ xSub σ hσ) : x⁻¹ * g⁻¹ * x * g ∈ series σ hσ i := by
  obtain ⟨a', b', -, rfl⟩ := hg
  interval_cases i
  · obtain ⟨c, -, rfl⟩ := hx
    change _ ∈ (⊥ : Subgroup (GL (Fin 3) F))
    rw [Subgroup.mem_bot, uG_inv, uG_inv, uG_mul, uG_mul, uG_mul, ← uG_zero σ]
    simp only [map_neg, map_zero]
    congr 1 <;> ring
  · obtain ⟨a, b, -, rfl⟩ := hx
    rw [uG_inv, uG_inv, uG_mul, uG_mul, uG_mul]
    refine uG_mem_zSub (by ring) ?_
    simp only [map_add, map_sub, map_neg, map_mul, hσ]
    ring

include hσ in
theorem neg_one_conj_of_mem_zSub {x : GL (Fin 3) F} (hx : x ∈ zSub σ) :
    torusHom σ (-1) * x * (torusHom σ (-1))⁻¹ = x := by
  obtain ⟨c, -, rfl⟩ := hx
  rw [torus_conj_neg_one hσ, neg_zero]

theorem neg_one_conj_mul_mem {x : GL (Fin 3) F} (hx : x ∈ xSub σ hσ) :
    torusHom σ (-1) * x * (torusHom σ (-1))⁻¹ * x ∈ zSub σ := by
  obtain ⟨a, b, hab, rfl⟩ := hx
  rw [torus_conj_neg_one hσ, uG_mul]
  refine uG_mem_zSub (by ring) ?_
  simp only [map_add, map_sub, map_neg, map_mul, hσ]
  linear_combination 2 * hab

theorem zmod_three_eq_zero_of_add_self : ∀ c : ZMod 3, c + c = 0 → c = 0 := by
  decide

theorem bil_zero_one (bf : GL (Fin 3) F → GL (Fin 3) F → ZMod 3)
    (hb₂ : ∀ x ∈ series σ hσ 1, ∀ y ∈ series σ hσ 2, ∀ y' ∈ series σ hσ 2,
      bf x (y * y') = bf x y + bf x y')
    (hv₂ : ∀ x ∈ series σ hσ 1, ∀ y ∈ series σ hσ 1, bf x y = 0)
    (hT : ∀ (t : Fˣ), ∀ x ∈ series σ hσ 1, ∀ y ∈ series σ hσ 2,
      bf (torusHom σ t * x * (torusHom σ t)⁻¹) (torusHom σ t * y * (torusHom σ t)⁻¹) = bf x y) :
    ∀ x ∈ series σ hσ 1, ∀ y ∈ series σ hσ 2, bf x y = 0 := by
  intro x hx y hy
  have h1 := hT (-1) x hx y hy
  rw [neg_one_conj_of_mem_zSub hσ hx] at h1
  have h2 := hb₂ x hx _ (series_inv hσ le_rfl (-1) hy) y hy
  rw [hv₂ x hx _ (neg_one_conj_mul_mem hσ hy), h1] at h2
  exact zmod_three_eq_zero_of_add_self _ h2.symm

theorem bil_one_zero (bf : GL (Fin 3) F → GL (Fin 3) F → ZMod 3)
    (hb₁ : ∀ x ∈ series σ hσ 2, ∀ x' ∈ series σ hσ 2, ∀ y ∈ series σ hσ 1,
      bf (x * x') y = bf x y + bf x' y)
    (hv₁ : ∀ x ∈ series σ hσ 1, ∀ y ∈ series σ hσ 1, bf x y = 0)
    (hT : ∀ (t : Fˣ), ∀ x ∈ series σ hσ 2, ∀ y ∈ series σ hσ 1,
      bf (torusHom σ t * x * (torusHom σ t)⁻¹) (torusHom σ t * y * (torusHom σ t)⁻¹) = bf x y) :
    ∀ x ∈ series σ hσ 2, ∀ y ∈ series σ hσ 1, bf x y = 0 := by
  intro x hx y hy
  have h1 := hT (-1) x hx y hy
  rw [neg_one_conj_of_mem_zSub hσ hy] at h1
  have h2 := hb₁ _ (series_inv hσ le_rfl (-1) hx) x hx y hy
  rw [hv₁ _ (neg_one_conj_mul_mem hσ hx) y hy, h1] at h2
  exact zmod_three_eq_zero_of_add_self _ h2.symm

theorem bil_zero_zero_of_fixed (hfix3 : ∀ w : F, σ w = w → w = 0 ∨ w = 1 ∨ w = -1)
    (bf : GL (Fin 3) F → GL (Fin 3) F → ZMod 3)
    (hb₂ : ∀ x ∈ series σ hσ 1, ∀ y ∈ series σ hσ 1, ∀ y' ∈ series σ hσ 1,
      bf x (y * y') = bf x y + bf x y')
    (hv₁ : ∀ x ∈ series σ hσ 0, ∀ y ∈ series σ hσ 1, bf x y = 0)
    (hv₂ : ∀ x ∈ series σ hσ 1, ∀ y ∈ series σ hσ 0, bf x y = 0)
    (halt : ∀ x ∈ series σ hσ 1, bf x x = 0) :
    ∀ x ∈ series σ hσ 1, ∀ y ∈ series σ hσ 1, bf x y = 0 := by
  have h1 : (1 : GL (Fin 3) F) ∈ series σ hσ 0 := one_mem _
  intro x hx y hy
  obtain ⟨c, hc, rfl⟩ := hx
  obtain ⟨c', hc', rfl⟩ := hy
  by_cases hc0 : c = 0
  · subst hc0
    rw [uG_zero]
    exact hv₁ _ h1 _ ⟨c', hc', rfl⟩
  have hw : σ (c' / c) = c' / c := by
    rw [map_div₀, show σ c = -c by linear_combination hc,
      show σ c' = -c' by linear_combination hc', neg_div_neg_eq]
  rcases hfix3 _ hw with h | h | h
  · obtain rfl : c' = 0 := (div_eq_zero_iff.1 h).resolve_right hc0
    rw [uG_zero]
    exact hv₂ _ ⟨c, hc, rfl⟩ _ h1
  · obtain rfl : c' = c := (div_eq_one_iff_eq hc0).1 h
    exact halt _ ⟨c', hc, rfl⟩
  · obtain rfl : c' = -c := by rw [div_eq_iff hc0] at h; rw [h, neg_one_mul]
    have h2 := hb₂ _ ⟨c, hc, rfl⟩ _ ⟨c, hc, rfl⟩ _ ⟨-c, hc', rfl⟩
    have he : uG σ 0 c * uG σ 0 (-c) = 1 := by
      rw [uG_mul, ← uG_zero σ]
      congr 1 <;> ring
    rw [he, hv₂ _ ⟨c, hc, rfl⟩ _ h1, halt _ ⟨c, hc, rfl⟩, zero_add] at h2
    exact h2.symm

end Series

section CharThree

variable {F : Type} [Field F] [CharP F 3] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c)

variable (F) in
theorem three_eq_zero : (3 : F) = 0 := by
  exact_mod_cast CharP.cast_eq_zero F 3

theorem uG_pow_three_eq_one (a b : F) : uG σ a b ^ 3 = 1 := by
  rw [uG_pow_three, three_eq_zero F]
  simp only [zero_mul, sub_zero]
  exact uG_zero σ

theorem coord_mem {i : ℕ} (hi : i < 2) (u : F) : coord σ i u ∈ series σ hσ (i + 1) := by
  interval_cases i
  · exact uG_mem_zSub rfl (by rw [map_sub, hσ]; ring)
  · refine ⟨u, σ u * u, ?_, rfl⟩
    rw [map_mul, hσ]
    linear_combination (σ u * u) * three_eq_zero F

theorem exists_coord {i : ℕ} (hi : i < 2) {x : GL (Fin 3) F} (hx : x ∈ series σ hσ (i + 1)) :
    ∃ u, ∃ z ∈ series σ hσ i, x = coord σ i u * z := by
  interval_cases i
  · obtain ⟨c, hc, rfl⟩ := hx
    refine ⟨-c, 1, one_mem _, ?_⟩
    change _ = uG σ 0 (-c - σ (-c)) * 1
    rw [mul_one, map_neg]
    congr 1
    linear_combination c * three_eq_zero F - hc
  · obtain ⟨a, b, hab, rfl⟩ := hx
    refine ⟨a, uG σ 0 (b - σ a * a), uG_mem_zSub rfl ?_, ?_⟩
    · rw [map_sub, map_mul, hσ]
      linear_combination hab - (σ a * a) * three_eq_zero F
    · change _ = uG σ a (σ a * a) * uG σ 0 (b - σ a * a)
      rw [uG_mul, map_zero]
      congr 1 <;> ring

theorem coord_add {i : ℕ} (hi : i < 2) (u u' : F) :
    ∃ z ∈ series σ hσ i, coord σ i u * coord σ i u' = coord σ i (u + u') * z := by
  interval_cases i
  · refine ⟨1, one_mem _, ?_⟩
    change uG σ 0 (u - σ u) * uG σ 0 (u' - σ u') = uG σ 0 (u + u' - σ (u + u')) * 1
    rw [uG_mul, mul_one, map_add]
    congr 1 <;> ring
  · refine ⟨uG σ 0 (-(u * σ u') - σ u * u' - σ u' * u), uG_mem_zSub rfl ?_, ?_⟩
    · simp only [map_sub, map_neg, map_mul, hσ]
      linear_combination (-(u * σ u') - σ u * u') * three_eq_zero F
    · change uG σ u (σ u * u) * uG σ u' (σ u' * u') =
        uG σ (u + u') (σ (u + u') * (u + u')) * uG σ 0 (-(u * σ u') - σ u * u' - σ u' * u)
      rw [uG_mul, uG_mul, map_add, map_zero]
      congr 1 <;> ring

theorem series_sq {i : ℕ} (hi : i < 2) {x : GL (Fin 3) F} (hx : x ∈ series σ hσ (i + 1)) :
    x ^ 3 ∈ series σ hσ i := by
  interval_cases i
  · obtain ⟨c, -, rfl⟩ := hx
    change _ ∈ (⊥ : Subgroup (GL (Fin 3) F))
    rw [Subgroup.mem_bot, uG_pow_three_eq_one]
  · obtain ⟨a, b, -, rfl⟩ := hx
    rw [uG_pow_three_eq_one]
    exact one_mem _

theorem series_fix {s₀ : Fˣ} (hs₀ : (s₀ : F) * σ s₀ ≠ 1) {i : ℕ} (hi : i < 2)
    {x : GL (Fin 3) F} (hx : x ∈ series σ hσ (i + 1))
    (hfx : ∀ s : Fˣ, (torusHom σ s * x * (torusHom σ s)⁻¹)⁻¹ * x ∈ series σ hσ i) :
    x ∈ series σ hσ i := by
  interval_cases i
  · obtain ⟨c, -, rfl⟩ := hx
    have h := hfx s₀
    change _ ∈ (⊥ : Subgroup (GL (Fin 3) F)) at h
    change _ ∈ (⊥ : Subgroup (GL (Fin 3) F))
    rw [Subgroup.mem_bot, inv_mul_eq_one, torus_conj hσ] at h
    have hc := (uG_inj σ h).2
    have hc0 : c = 0 := by
      have h' : ((s₀ : F) * σ s₀ - 1) * c = 0 := by linear_combination hc
      exact (mul_eq_zero.1 h').resolve_left (sub_ne_zero.2 hs₀)
    rw [Subgroup.mem_bot, hc0, uG_zero]
  · obtain ⟨a, b, hab, rfl⟩ := hx
    have h := hfx (-1)
    rw [torus_conj_neg_one hσ, uG_inv, uG_mul] at h
    obtain ⟨c, -, hc⟩ := h
    have ha := (uG_inj σ hc).1
    have ha0 : a = 0 := by linear_combination a * three_eq_zero F - ha
    subst ha0
    exact uG_mem_zSub rfl (by simpa using hab)

theorem bil_diag [Finite F] {n : ℕ} (hn : 1 ≤ n) (hFn : Nat.card F = 3 ^ n) {i : ℕ} (hi : i < 2)
    {e : ℤ} (he : ∀ s : Fˣ, wtc σ i s = ((s ^ e : Fˣ) : F))
    (hnd : ∀ k l : ℕ, k < n → l < n → ¬ ((3 : ℤ) ^ n - 1) ∣ 3 ^ k * e + 3 ^ l * e)
    (bf : GL (Fin 3) F → GL (Fin 3) F → ZMod 3)
    (hb₁ : ∀ x ∈ series σ hσ (i + 1), ∀ x' ∈ series σ hσ (i + 1), ∀ y ∈ series σ hσ (i + 1),
      bf (x * x') y = bf x y + bf x' y)
    (hb₂ : ∀ x ∈ series σ hσ (i + 1), ∀ y ∈ series σ hσ (i + 1), ∀ y' ∈ series σ hσ (i + 1),
      bf x (y * y') = bf x y + bf x y')
    (hv₁ : ∀ x ∈ series σ hσ i, ∀ y ∈ series σ hσ (i + 1), bf x y = 0)
    (hv₂ : ∀ x ∈ series σ hσ (i + 1), ∀ y ∈ series σ hσ i, bf x y = 0)
    (hT : ∀ (t : Fˣ), ∀ x ∈ series σ hσ (i + 1), ∀ y ∈ series σ hσ (i + 1),
      bf (torusHom σ t * x * (torusHom σ t)⁻¹) (torusHom σ t * y * (torusHom σ t)⁻¹) = bf x y) :
    ∀ x ∈ series σ hσ (i + 1), ∀ y ∈ series σ hσ (i + 1), bf x y = 0 := by
  set G : F → F → ZMod 3 := fun u v => bf (coord σ i u) (coord σ i v) with hGdef
  have hG₁ : ∀ u u' v, G (u + u') v = G u v + G u' v := by
    intro u u' v
    obtain ⟨z, hz, hzeq⟩ := coord_add hσ hi u u'
    have h1 := hb₁ _ (coord_mem hσ hi u) _ (coord_mem hσ hi u') _ (coord_mem hσ hi v)
    rw [hzeq, hb₁ _ (coord_mem hσ hi (u + u')) _ (series_mono hσ hi hz) _ (coord_mem hσ hi v),
      hv₁ _ hz _ (coord_mem hσ hi v), add_zero] at h1
    exact h1
  have hG₂ : ∀ u v v', G u (v + v') = G u v + G u v' := by
    intro u v v'
    obtain ⟨z, hz, hzeq⟩ := coord_add hσ hi v v'
    have h1 := hb₂ _ (coord_mem hσ hi u) _ (coord_mem hσ hi v) _ (coord_mem hσ hi v')
    rw [hzeq, hb₂ _ (coord_mem hσ hi u) _ (coord_mem hσ hi (v + v')) _ (series_mono hσ hi hz),
      hv₂ _ (coord_mem hσ hi u) _ hz, add_zero] at h1
    exact h1
  have hGT : ∀ (t : Fˣ) u v, G (((t ^ e : Fˣ) : F) * u) (((t ^ e : Fˣ) : F) * v) = G u v := by
    intro t u v
    simp only [hGdef]
    rw [← he, ← coord_conj hσ hi, ← coord_conj hσ hi]
    exact hT t _ (coord_mem hσ hi u) _ (coord_mem hσ hi v)
  have hG0 := zpow_form_eq_zero (p := 3) hn hFn (e₁ := e) (e₂ := e)
    (fun k l hk hl h => hnd k l hk hl (by
      rw [Nat.cast_sub (Nat.one_le_pow _ _ (by norm_num)), Nat.cast_pow, Nat.cast_ofNat,
        Nat.cast_one] at h
      exact h)) G hG₁ hG₂ hGT
  intro x hx y hy
  obtain ⟨u, z, hz, rfl⟩ := exists_coord hσ hi hx
  obtain ⟨v, z', hz', rfl⟩ := exists_coord hσ hi hy
  rw [hb₁ _ (coord_mem hσ hi u) _ (series_mono hσ hi hz) _ hy, hv₁ _ hz _ hy, add_zero,
    hb₂ _ (coord_mem hσ hi u) _ (coord_mem hσ hi v) _ (series_mono hσ hi hz'),
    hv₂ _ (coord_mem hσ hi u) _ hz', add_zero]
  exact hG0 u v

end CharThree

theorem three_pow_mul_le {e n : ℕ} (h : e < n) : (3 : ℤ) ^ e * 3 ≤ 3 ^ n := by
  rw [← pow_succ]
  exact pow_le_pow_right₀ (by norm_num) h

theorem dvd_pow_sub_pow_mod (f k : ℕ) : ((3 : ℤ) ^ f - 1) ∣ (3 : ℤ) ^ k - 3 ^ (k % f) := by
  have h : (3 : ℤ) ^ k = ((3 : ℤ) ^ f) ^ (k / f) * 3 ^ (k % f) := by
    rw [← pow_mul, ← pow_add, Nat.div_add_mod]
  rw [h, ← sub_one_mul]
  apply dvd_mul_of_dvd_left
  simpa using sub_dvd_pow_sub_pow ((3 : ℤ) ^ f) 1 (k / f)

@[expose] def wt (f : ℕ) : ℕ → ℤ
  | 0 => 1 + 3 ^ f
  | _ => 2 - 3 ^ f

theorem not_dvd_wt_zero {f : ℕ} (hf : 2 ≤ f) (k l : ℕ) :
    ¬ ((3 : ℤ) ^ (2 * f) - 1) ∣ 3 ^ k * wt f 0 + 3 ^ l * wt f 0 := by
  intro h
  have h1 : ((3 : ℤ) ^ f - 1) * (3 ^ f + 1) ∣ (3 ^ k + 3 ^ l) * (3 ^ f + 1) := by
    have e1 : ((3 : ℤ) ^ (2 * f) - 1) = (3 ^ f - 1) * (3 ^ f + 1) := by ring
    have e2 : (3 : ℤ) ^ k * wt f 0 + 3 ^ l * wt f 0 = (3 ^ k + 3 ^ l) * (3 ^ f + 1) := by
      simp only [wt]
      ring
    rwa [e1, e2] at h
  have h2 := (mul_dvd_mul_iff_right (by positivity : (3 : ℤ) ^ f + 1 ≠ 0)).1 h1
  have h3 : ((3 : ℤ) ^ f - 1) ∣ 3 ^ (k % f) + 3 ^ (l % f) := by
    have e : (3 : ℤ) ^ (k % f) + 3 ^ (l % f) =
        (3 ^ k + 3 ^ l) - (3 ^ k - 3 ^ (k % f)) - (3 ^ l - 3 ^ (l % f)) := by ring
    rw [e]
    exact dvd_sub (dvd_sub h2 (dvd_pow_sub_pow_mod f k)) (dvd_pow_sub_pow_mod f l)
  have hk3 := three_pow_mul_le (Nat.mod_lt k (by omega : 0 < f))
  have hl3 := three_pow_mul_le (Nat.mod_lt l (by omega : 0 < f))
  have h9 : (9 : ℤ) ≤ 3 ^ f := by
    calc (9 : ℤ) = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ f := pow_le_pow_right₀ (by norm_num) hf
  have h4 := Int.le_of_dvd (by positivity) h3
  linarith

theorem not_dvd_wt_one {f k l : ℕ} (hf : 1 ≤ f) (hk : k < 2 * f) (hl : l < 2 * f) :
    ¬ ((3 : ℤ) ^ (2 * f) - 1) ∣ 3 ^ k * wt f 1 + 3 ^ l * wt f 1 := by
  intro h
  obtain ⟨m, rfl⟩ : ∃ m, f = m + 1 := ⟨f - 1, by omega⟩
  have hc : IsCoprime ((3 : ℤ) ^ (2 * (m + 1)) - 1) (wt (m + 1) 1) :=
    ⟨1 - 3 ^ m, (1 - 3 ^ m) * (3 ^ (m + 1) + 2) - 1, by simp only [wt]; ring⟩
  have h1 : ((3 : ℤ) ^ (2 * (m + 1)) - 1) ∣ (3 ^ k + 3 ^ l) * wt (m + 1) 1 := by
    rwa [add_mul]
  have h2 := Int.le_of_dvd (by positivity) (hc.dvd_of_dvd_mul_right h1)
  have hk3 := three_pow_mul_le hk
  have hl3 := three_pow_mul_le hl
  have h9 : (9 : ℤ) ≤ 3 ^ (2 * (m + 1)) := by
    calc (9 : ℤ) = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ (2 * (m + 1)) := pow_le_pow_right₀ (by norm_num) (by omega)
  linarith

section Main

variable {F : Type} [Field F] [Finite F] [CharP F 3] {f : ℕ}

local notation "σ₀" => unitaryInvolution F 3 f

theorem coe_zpow_wt {i : ℕ} (hi : i < 2) (s : Fˣ) : ((s ^ wt f i : Fˣ) : F) = wtc σ₀ i s := by
  interval_cases i
  · change ((s ^ ((1 : ℤ) + 3 ^ f) : Fˣ) : F) = s * σ₀ s
    rw [show ((1 : ℤ) + 3 ^ f) = ((1 + 3 ^ f : ℕ) : ℤ) by push_cast; rfl, zpow_natCast,
      Units.val_pow_eq_pow_val, pow_add, pow_one, unitaryInvolution_apply]
  · change ((s ^ ((2 : ℤ) - 3 ^ f) : Fˣ) : F) = (s : F) ^ 2 / σ₀ s
    rw [show ((2 : ℤ) - 3 ^ f) = ((2 : ℕ) : ℤ) - ((3 ^ f : ℕ) : ℤ) by push_cast; rfl,
      _root_.zpow_sub, zpow_natCast, zpow_natCast, Units.val_mul, Units.val_inv_eq_inv_val,
      Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, unitaryInvolution_apply, div_eq_mul_inv]

omit [Finite F] [CharP F 3] in
theorem coprime_three_card_units (hF : Nat.card F = (3 ^ f) ^ 2) (hf : 1 ≤ f) :
    Nat.Coprime 3 (Nat.card Fˣ) := by
  rw [Nat.card_units, hF, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
  rintro ⟨c, hc⟩
  obtain ⟨m, rfl⟩ : ∃ m, f = m + 1 := ⟨f - 1, by omega⟩
  have h3 : (3 ^ (m + 1)) ^ 2 = 3 * (3 ^ m * 3 ^ (m + 1)) := by ring
  have h1 : 1 ≤ 3 ^ m * 3 ^ (m + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
  omega

theorem exists_norm_ne_one (hF : Nat.card F = (3 ^ f) ^ 2) (hf : 1 ≤ f) :
    ∃ s : Fˣ, (s : F) * σ₀ s ≠ 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hord : orderOf g = (3 ^ f) ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hF]
  refine ⟨g, fun h => ?_⟩
  have h1 : g ^ (1 + 3 ^ f) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, pow_add, pow_one, ← unitaryInvolution_apply]
    exact h
  have h2 := Nat.le_of_dvd (by positivity) (orderOf_dvd_of_pow_eq_one h1)
  rw [hord] at h2
  have h3 : 3 ≤ 3 ^ f := by
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have h4 : 3 * 3 ^ f ≤ (3 ^ f) ^ 2 := by nlinarith
  omega

theorem xSub_le_SU (hF : Nat.card F = (3 ^ f) ^ 2) :
    xSub σ₀ (unitaryInvolution_involutive hF) ≤ SU σ₀ 3 := by
  rintro _ ⟨a, b, hab, rfl⟩
  exact ⟨det_heisM σ₀ a b, heisM_isometry hF hab⟩

theorem xSub_subgroupOf (hF : Nat.card F = (3 ^ f) ^ 2) :
    (xSub σ₀ (unitaryInvolution_involutive hF)).subgroupOf (SU σ₀ 3) = heisX hF := by
  ext x
  rw [Subgroup.mem_subgroupOf, CFSG.LieType.Steinberg.mem_rootGroup_three]
  constructor
  · rintro ⟨a, b, hab, hx⟩
    exact ⟨a, b, hab, by rw [SUExtras.mat_apply, hx]; rfl⟩
  · rintro ⟨a, b, hab, hx⟩
    exact ⟨a, b, hab, Units.ext (by rw [← SUExtras.mat_apply, hx]; rfl)⟩

theorem series_bil (hF : Nat.card F = (3 ^ f) ^ 2) (hf : 2 ≤ f) (hσ : ∀ c, σ₀ (σ₀ c) = c)
    {i : ℕ} (hi : i < 2) {j : ℕ} (hj : j < 2) (bf : GL (Fin 3) F → GL (Fin 3) F → ZMod 3)
    (hb₁ : ∀ x ∈ series σ₀ hσ (i + 1), ∀ x' ∈ series σ₀ hσ (i + 1), ∀ y ∈ series σ₀ hσ (j + 1),
      bf (x * x') y = bf x y + bf x' y)
    (hb₂ : ∀ x ∈ series σ₀ hσ (i + 1), ∀ y ∈ series σ₀ hσ (j + 1), ∀ y' ∈ series σ₀ hσ (j + 1),
      bf x (y * y') = bf x y + bf x y')
    (hv₁ : ∀ x ∈ series σ₀ hσ i, ∀ y ∈ series σ₀ hσ (j + 1), bf x y = 0)
    (hv₂ : ∀ x ∈ series σ₀ hσ (i + 1), ∀ y ∈ series σ₀ hσ j, bf x y = 0)
    (hT : ∀ (t : Fˣ), ∀ x ∈ series σ₀ hσ (i + 1), ∀ y ∈ series σ₀ hσ (j + 1),
      bf (torusHom σ₀ t * x * (torusHom σ₀ t)⁻¹) (torusHom σ₀ t * y * (torusHom σ₀ t)⁻¹) =
        bf x y) :
    ∀ x ∈ series σ₀ hσ (i + 1), ∀ y ∈ series σ₀ hσ (j + 1), bf x y = 0 := by
  have hFn : Nat.card F = 3 ^ (2 * f) := by rw [hF, ← pow_mul, mul_comm]
  interval_cases i <;> interval_cases j
  · exact bil_diag hσ (by omega) hFn (by norm_num) (fun s => (coe_zpow_wt (by norm_num) s).symm)
      (fun k l _ _ => not_dvd_wt_zero hf k l) bf hb₁ hb₂ hv₁ hv₂ hT
  · exact bil_zero_one hσ bf hb₂ hv₂ hT
  · exact bil_one_zero hσ bf hb₁ hv₁ hT
  · exact bil_diag hσ (by omega) hFn (by norm_num) (fun s => (coe_zpow_wt (by norm_num) s).symm)
      (fun k l hk hl => not_dvd_wt_one (by omega) hk hl) bf hb₁ hb₂ hv₁ hv₂ hT

theorem su_three_char_three_cover_trivial (hF : Nat.card F = (3 ^ f) ^ 2) (hf : 2 ≤ f)
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (η : E →* SU (unitaryInvolution F 3 f) 3) (hη : Function.Surjective η)
    (hC : η.ker ≤ Subgroup.center E) (h3 : IsPGroup 3 η.ker) : η.ker = ⊥ := by
  have hσ := unitaryInvolution_involutive hF
  obtain ⟨s₀, hs₀⟩ := exists_norm_ne_one hF (by omega)
  have hUp : IsPGroup 3 ((xSub σ₀ hσ).subgroupOf (SU σ₀ 3)) := by
    rw [xSub_subgroupOf hF]
    exact isPGroup_heisX hF
  have hUi : ¬ 3 ∣ ((xSub σ₀ hσ).subgroupOf (SU σ₀ 3)).index := by
    rw [xSub_subgroupOf hF]
    exact not_dvd_index_heisX hF
  exact CFSG.LocalAnalysis.ComponentInitial.ker_eq_bot_of_coprime_central_series_prime η hη hC
    h3 (xSub_le_SU hF) hUp hUi (coprime_three_card_units hF (by omega)) (torusHom σ₀)
    (fun s => torusHom_mem hσ s) (fun s x hx => series_inv hσ (i := 2) le_rfl s hx) 2
    (series σ₀ hσ) rfl rfl (fun i hi => series_mono hσ hi)
    (fun i hi s x hx => series_inv hσ hi s hx) (fun i hi x hx g hg => series_cent hσ hi hx hg)
    (fun i hi x hx => series_sq hσ hi hx) (fun i hi x hx hfx => series_fix hσ hs₀ hi hx hfx)
    (fun i hi j hj bf hb₁ hb₂ hv₁ hv₂ hT => series_bil hF hf hσ hi hj bf hb₁ hb₂ hv₁ hv₂ hT)

omit [CharP F 3] in
theorem one_le_of_card (hF : Nat.card F = (3 ^ f) ^ 2) : 1 ≤ f := by
  have hq := CFSG.ClassicalGroups.Unitary.one_lt_pow_of_card hF
  rcases Nat.eq_zero_or_pos f with rfl | h
  · norm_num at hq
  · exact h

theorem eq_zero_or_eq_one_or_eq_neg_one_of_fixed {w : F} (hw : unitaryInvolution F 3 1 w = w) :
    w = 0 ∨ w = 1 ∨ w = -1 := by
  rw [unitaryInvolution_apply, pow_one] at hw
  have h : w * (w - 1) * (w + 1) = 0 := by linear_combination hw
  rcases mul_eq_zero.1 h with h | h
  · rcases mul_eq_zero.1 h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (sub_eq_zero.1 h))
  · exact Or.inr (Or.inr (eq_neg_of_add_eq_zero_left h))

theorem series_bil_alt (hF : Nat.card F = (3 ^ f) ^ 2) (hσ : ∀ c, σ₀ (σ₀ c) = c)
    {i : ℕ} (hi : i < 2) {j : ℕ} (hj : j < 2) (bf : GL (Fin 3) F → GL (Fin 3) F → ZMod 3)
    (hb₁ : ∀ x ∈ series σ₀ hσ (i + 1), ∀ x' ∈ series σ₀ hσ (i + 1), ∀ y ∈ series σ₀ hσ (j + 1),
      bf (x * x') y = bf x y + bf x' y)
    (hb₂ : ∀ x ∈ series σ₀ hσ (i + 1), ∀ y ∈ series σ₀ hσ (j + 1), ∀ y' ∈ series σ₀ hσ (j + 1),
      bf x (y * y') = bf x y + bf x y')
    (hv₁ : ∀ x ∈ series σ₀ hσ i, ∀ y ∈ series σ₀ hσ (j + 1), bf x y = 0)
    (hv₂ : ∀ x ∈ series σ₀ hσ (i + 1), ∀ y ∈ series σ₀ hσ j, bf x y = 0)
    (halt : i = j → ∀ x ∈ series σ₀ hσ (i + 1), bf x x = 0)
    (hT : ∀ (t : Fˣ), ∀ x ∈ series σ₀ hσ (i + 1), ∀ y ∈ series σ₀ hσ (j + 1),
      bf (torusHom σ₀ t * x * (torusHom σ₀ t)⁻¹) (torusHom σ₀ t * y * (torusHom σ₀ t)⁻¹) =
        bf x y) :
    ∀ x ∈ series σ₀ hσ (i + 1), ∀ y ∈ series σ₀ hσ (j + 1), bf x y = 0 := by
  rcases Nat.lt_or_ge f 2 with hf | hf
  · obtain rfl : f = 1 := by have := one_le_of_card hF; omega
    interval_cases i <;> interval_cases j
    · exact bil_zero_zero_of_fixed hσ (fun w hw => eq_zero_or_eq_one_or_eq_neg_one_of_fixed hw)
        bf hb₂ hv₁ hv₂ (halt rfl)
    · exact bil_zero_one hσ bf hb₂ hv₂ hT
    · exact bil_one_zero hσ bf hb₁ hv₁ hT
    · have hFn : Nat.card F = 3 ^ (2 * 1) := by rw [hF]; norm_num
      exact bil_diag hσ (by omega) hFn (by norm_num)
        (fun s => (coe_zpow_wt (by norm_num) s).symm)
        (fun k l hk hl => not_dvd_wt_one le_rfl hk hl) bf hb₁ hb₂ hv₁ hv₂ hT
  · exact series_bil hF hf hσ hi hj bf hb₁ hb₂ hv₁ hv₂ hT

theorem su_three_char_three_cover_trivial' (hF : Nat.card F = (3 ^ f) ^ 2)
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (η : E →* SU (unitaryInvolution F 3 f) 3) (hη : Function.Surjective η)
    (hC : η.ker ≤ Subgroup.center E) (h3 : IsPGroup 3 η.ker) : η.ker = ⊥ := by
  have hσ := unitaryInvolution_involutive hF
  have hf := one_le_of_card hF
  obtain ⟨s₀, hs₀⟩ := exists_norm_ne_one hF hf
  have hUp : IsPGroup 3 ((xSub σ₀ hσ).subgroupOf (SU σ₀ 3)) := by
    rw [xSub_subgroupOf hF]
    exact isPGroup_heisX hF
  have hUi : ¬ 3 ∣ ((xSub σ₀ hσ).subgroupOf (SU σ₀ 3)).index := by
    rw [xSub_subgroupOf hF]
    exact not_dvd_index_heisX hF
  exact CFSG.LocalAnalysis.ComponentInitial.ker_eq_bot_of_coprime_central_series_prime_alt η hη
    hC h3 (xSub_le_SU hF) hUp hUi (coprime_three_card_units hF hf) (torusHom σ₀)
    (fun s => torusHom_mem hσ s) (fun s x hx => series_inv hσ (i := 2) le_rfl s hx) 2
    (series σ₀ hσ) rfl rfl (fun i hi => series_mono hσ hi)
    (fun i hi s x hx => series_inv hσ hi s hx) (fun i hi x hx g hg => series_cent hσ hi hx hg)
    (fun i hi x hx => series_sq hσ hi hx) (fun i hi x hx hfx => series_fix hσ hs₀ hi hx hfx)
    (fun i hi j hj bf hb₁ hb₂ hv₁ hv₂ halt hT =>
      series_bil_alt hF hσ hi hj bf hb₁ hb₂ hv₁ hv₂ halt hT)

end Main

end CFSG.LieType.Steinberg.CentralExt.SUThreeCharThree
