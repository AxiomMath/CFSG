module

public import CFSG.LieType.SeitzGeneration.HeisTorusUDefs
public import CFSG.LieType.SeitzGeneration.HeisTorusIdent

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

variable {ℓ f : ℕ} {K : Type} [Field K] {r : ℕ}

theorem ug86_bar_eq_inv (h : UnitaryFieldData ℓ f K) {x : K} (hx : x ^ (ℓ ^ f + 1) = 1) :
    h.bar x = x⁻¹ := by
  rw [UnitaryFieldData.bar_apply]
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← pow_succ]
  exact hx

theorem ug86_pow_pow_eq_one {x : K} (hx : x ^ (ℓ ^ f + 1) = 1) (n : ℕ) :
    (x ^ n) ^ (ℓ ^ f + 1) = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, hx, one_pow]

theorem ug86_pow_eq_one_of_dvd {ζ : K} (hζ : ζ ^ r = 1) (hrq : r ∣ ℓ ^ f + 1) :
    ζ ^ (ℓ ^ f + 1) = 1 := by
  obtain ⟨m, hm⟩ := hrq
  rw [hm, pow_mul, hζ, one_pow]

theorem ug86_exists_kappa (h : UnitaryFieldData ℓ f K) (hr : r.Prime) (hne : ℓ ^ f + 1 ≠ r) :
    ∃ κ : K, κ ^ (ℓ ^ f + 1) = 1 ∧ κ ^ r ≠ 1 := by
  have := h.finite
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hℓ := h.prime.two_le
  have he := h.one_le
  set q := ℓ ^ f with hq
  have hq2 : 2 ≤ q := by
    calc 2 ≤ ℓ := hℓ
      _ = ℓ ^ 1 := (pow_one ℓ).symm
      _ ≤ ℓ ^ f := Nat.pow_le_pow_right (by omega) he
  have hqq : ℓ ^ (2 * f) = q * q := by rw [two_mul, pow_add]
  have hcard : Nat.card Kˣ = q * q - 1 := by rw [Nat.card_units, h.card, hqq]
  have hord : orderOf g = q * q - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcard]
  have hfac : q * q - 1 = (q - 1) * (q + 1) := by
    zify [show 1 ≤ q * q from by nlinarith, show 1 ≤ q by omega]
    ring
  have hdvd : q - 1 ∣ orderOf g := by rw [hord, hfac]; exact Dvd.intro _ rfl
  have hu : orderOf (g ^ (q - 1)) = q + 1 := by
    rw [orderOf_pow_of_dvd (by omega) hdvd, hord, hfac, Nat.mul_div_cancel_left _ (by omega)]
  refine ⟨((g ^ (q - 1) : Kˣ) : K), ?_, ?_⟩
  · have h1 : (g ^ (q - 1)) ^ (q + 1) = 1 := by rw [← hu]; exact pow_orderOf_eq_one _
    rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
  · intro hkr
    have h1 : (g ^ (q - 1)) ^ r = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      exact hkr
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hu] at h2
    rcases (Nat.dvd_prime hr).mp h2 with h3 | h3
    · omega
    · exact hne h3

@[expose] def ug86_diag [NeZero r] (ζ : K) (k : Fin r) : K :=
  ζ ^ ((Equiv.swap (0 : Fin r) 1 k : Fin r) : ℕ)

theorem ug86_val_one [NeZero r] (hr : 2 ≤ r) : ((1 : Fin r) : ℕ) = 1 := by
  rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]

theorem ug86_zero_ne_one [NeZero r] (hr : 2 ≤ r) : (0 : Fin r) ≠ 1 := by
  intro h
  have h' := congrArg Fin.val h
  rw [ug86_val_one hr, Fin.val_zero] at h'
  exact zero_ne_one h'

theorem ug86_prod_diag [NeZero r] [Fact r.Prime] (hr : 5 ≤ r) {ζ : K} (hζ : ζ ^ r = 1) :
    ∏ k : Fin r, ug86_diag ζ k = 1 := by
  have hodd : Odd r := (Fact.out : r.Prime).eq_two_or_odd'.resolve_left (by omega)
  unfold ug86_diag
  rw [Finset.prod_pow_eq_pow_sum,
    Equiv.sum_comp (Equiv.swap (0 : Fin r) 1) (fun k : Fin r => (k : ℕ)),
    Fin.sum_univ_eq_sum_range (fun i => i) r]
  obtain ⟨m, hm⟩ := hodd
  have h2 := Finset.sum_range_id_mul_two r
  have h3 : (∑ i ∈ Finset.range r, i) = r * m := by
    have : (∑ i ∈ Finset.range r, i) * 2 = (r * m) * 2 := by
      rw [h2]
      conv_lhs => rw [hm]
      simp only [Nat.add_sub_cancel]
      rw [← hm]
      ring
    omega
  rw [h3, pow_mul, hζ, one_pow]

theorem ug86_diag_pow_eq_one [NeZero r] {ζ : K} (hζ : ζ ^ (ℓ ^ f + 1) = 1) (k : Fin r) :
    ug86_diag ζ k ^ (ℓ ^ f + 1) = 1 :=
  ug86_pow_pow_eq_one hζ _

theorem ug86_sum_diag [NeZero r] {ζ : K} (hζ : IsPrimitiveRoot ζ r) (hr : 5 ≤ r) (i : Fin r)
    (hi : (i : ℕ) + 1 < r) :
    ∑ a : Fin r, ζ ^ ((i : ℕ) * (a : ℕ)) * ug86_diag ζ a = (ζ - 1) * (1 - ζ ^ (i : ℕ)) := by
  have h10 := ug86_zero_ne_one (r := r) (by omega)
  have hv1 := ug86_val_one (r := r) (by omega)
  have key : ∀ a : Fin r, ζ ^ ((i : ℕ) * (a : ℕ)) * ug86_diag ζ a =
      (ζ ^ ((i : ℕ) + 1)) ^ (a : ℕ) + (if a = 0 then ζ - 1 else 0) +
        (if a = 1 then ζ ^ (i : ℕ) * (1 - ζ) else 0) := by
    intro a
    by_cases ha0 : a = 0
    · subst ha0
      rw [if_pos rfl, if_neg h10]
      unfold ug86_diag
      rw [Equiv.swap_apply_left, hv1, Fin.val_zero]
      ring
    · by_cases ha1 : a = 1
      · subst ha1
        rw [if_neg ha0, if_pos rfl]
        unfold ug86_diag
        rw [Equiv.swap_apply_right, hv1, Fin.val_zero]
        ring
      · rw [if_neg ha0, if_neg ha1]
        unfold ug86_diag
        rw [Equiv.swap_apply_of_ne_of_ne ha0 ha1, add_zero, add_zero, ← pow_add, ← pow_mul]
        congr 1
        ring
  have hu : (ζ ^ ((i : ℕ) + 1)) ^ r = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hu1 : ζ ^ ((i : ℕ) + 1) ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (by omega) hi
  rw [Finset.sum_congr rfl fun a _ => key a, Finset.sum_add_distrib, Finset.sum_add_distrib,
    geom_sum_fin_eq_zero hu hu1, Finset.sum_ite_eq' Finset.univ (0 : Fin r),
    Finset.sum_ite_eq' Finset.univ (1 : Fin r)]
  simp only [Finset.mem_univ, if_true, zero_add]
  ring

theorem ug86_gamma_apply_zero [NeZero r] {ζ : K} (hζ : IsPrimitiveRoot ζ r) (hr : 5 ≤ r)
    (i : Fin r) (hi : (i : ℕ) + 1 < r) :
    (heisFourierMat ζ * diagonal (ug86_diag ζ) * (heisFourierMat ζ)⁻¹ :
      Matrix (Fin r) (Fin r) K) i 0 =
      (r : K)⁻¹ * ((ζ - 1) * (1 - ζ ^ (i : ℕ))) := by
  rw [heisFourierMat_inv hζ (by omega), Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.of_apply, heisFourierMat, Fin.val_zero, mul_zero,
    pow_zero, inv_one, mul_one]
  rw [← Finset.sum_mul, ug86_sum_diag hζ hr i hi, mul_comm]

theorem ug86_ne_zero_of_pow_eq_one {x : K} (hx : x ^ (ℓ ^ f + 1) = 1) : x ≠ 0 := by
  rintro rfl
  rw [zero_pow (Nat.succ_ne_zero _)] at hx
  exact zero_ne_one hx

theorem ug86_map_fourier (h : UnitaryFieldData ℓ f K) {ζ : K} (hζ : IsPrimitiveRoot ζ r)
    (hr : 2 ≤ r) (hrq : r ∣ ℓ ^ f + 1) :
    (heisFourierMat ζ : Matrix (Fin r) (Fin r) K).map h.bar = (r : K) • (heisFourierMat ζ)⁻¹ := by
  have hζq := ug86_pow_eq_one_of_dvd hζ.pow_eq_one hrq
  have hr0 := heis_natCast_ne_zero hζ hr
  rw [heisFourierMat_inv hζ hr]
  ext i j
  simp only [Matrix.map_apply, heisFourierMat, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  rw [ug86_bar_eq_inv h (ug86_pow_pow_eq_one hζq _), ← mul_assoc, mul_inv_cancel₀ hr0, one_mul]

theorem ug86_map_fourier_inv (h : UnitaryFieldData ℓ f K) {ζ : K} (hζ : IsPrimitiveRoot ζ r)
    (hr : 2 ≤ r) (hrq : r ∣ ℓ ^ f + 1) :
    ((heisFourierMat ζ : Matrix (Fin r) (Fin r) K)⁻¹).map h.bar =
      (r : K)⁻¹ • heisFourierMat ζ := by
  have hζq := ug86_pow_eq_one_of_dvd hζ.pow_eq_one hrq
  rw [heisFourierMat_inv hζ hr]
  ext i j
  simp only [Matrix.map_apply, heisFourierMat, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
    map_mul, map_inv₀, map_natCast]
  rw [ug86_bar_eq_inv h (ug86_pow_pow_eq_one hζq _), inv_inv]

theorem ug86_fourier_transpose {ζ : K} :
    (heisFourierMat ζ : Matrix (Fin r) (Fin r) K)ᵀ = heisFourierMat ζ := by
  ext i j
  simp only [Matrix.transpose_apply, heisFourierMat, Matrix.of_apply, mul_comm]

theorem ug86_fourier_inv_transpose {ζ : K} :
    ((heisFourierMat ζ : Matrix (Fin r) (Fin r) K)⁻¹)ᵀ = (heisFourierMat ζ)⁻¹ := by
  rw [Matrix.transpose_nonsing_inv, ug86_fourier_transpose]

theorem ug86_conj_unitary (h : UnitaryFieldData ℓ f K) {ζ : K} (hζ : IsPrimitiveRoot ζ r)
    (hr : 2 ≤ r) (hrq : r ∣ ℓ ^ f + 1) {d : Fin r → K} (hd : ∀ k, d k ^ (ℓ ^ f + 1) = 1) :
    ((heisFourierMat ζ * diagonal d * (heisFourierMat ζ)⁻¹ :
      Matrix (Fin r) (Fin r) K).map h.bar)ᵀ *
      (heisFourierMat ζ * diagonal d * (heisFourierMat ζ)⁻¹) = 1 := by
  have hΦ : IsUnit (heisFourierMat ζ : Matrix (Fin r) (Fin r) K).det :=
    isUnit_iff_ne_zero.mpr (det_heisFourierMat_ne_zero hζ)
  have hΨΦ : (heisFourierMat ζ : Matrix (Fin r) (Fin r) K)⁻¹ * heisFourierMat ζ = 1 :=
    Matrix.nonsing_inv_mul _ hΦ
  have hΦΨ : (heisFourierMat ζ : Matrix (Fin r) (Fin r) K) * (heisFourierMat ζ)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ hΦ
  have hr0 := heis_natCast_ne_zero hζ hr
  have hDD : (diagonal fun k => h.bar (d k) : Matrix (Fin r) (Fin r) K) * diagonal d = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext k
    rw [ug86_bar_eq_inv h (hd k)]
    exact inv_mul_cancel₀ (ug86_ne_zero_of_pow_eq_one (hd k))
  rw [Matrix.map_mul, Matrix.map_mul, ug86_map_fourier h hζ hr hrq,
    ug86_map_fourier_inv h hζ hr hrq, diagonal_map (map_zero _), transpose_mul, transpose_mul,
    transpose_smul, transpose_smul, ug86_fourier_transpose, ug86_fourier_inv_transpose,
    diagonal_transpose]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hr0,
    mul_inv_cancel₀ hr0, one_smul]
  calc (heisFourierMat ζ : Matrix (Fin r) (Fin r) K) *
        (diagonal (fun k => h.bar (d k)) * (heisFourierMat ζ)⁻¹) *
        (heisFourierMat ζ * diagonal d * (heisFourierMat ζ)⁻¹)
      = heisFourierMat ζ * diagonal (fun k => h.bar (d k)) *
        ((heisFourierMat ζ)⁻¹ * heisFourierMat ζ) * diagonal d * (heisFourierMat ζ)⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [hΨΦ, Matrix.mul_one, Matrix.mul_assoc _ (diagonal fun k => h.bar (d k)), hDD,
          Matrix.mul_one, hΦΨ]

theorem ug86_det_conj {ζ : K} (hζ : IsPrimitiveRoot ζ r) (d : Fin r → K) :
    (heisFourierMat ζ * diagonal d * (heisFourierMat ζ)⁻¹ : Matrix (Fin r) (Fin r) K).det =
      ∏ k, d k := by
  have hΦ : IsUnit (heisFourierMat ζ : Matrix (Fin r) (Fin r) K).det :=
    isUnit_iff_ne_zero.mpr (det_heisFourierMat_ne_zero hζ)
  rw [Matrix.det_conj ((Matrix.isUnit_iff_isUnit_det _).mpr hΦ), det_diagonal]

theorem ug86_exists_mem_fourier (h : UnitaryFieldData ℓ f K) {ζ : K} (hζ : IsPrimitiveRoot ζ r)
    (hr : 2 ≤ r) (hrq : r ∣ ℓ ^ f + 1) (H : Subgroup (GL (Fin r) K))
    (hTw : ∀ g ∈ unitarySU ℓ f K r, (∃ t, (g : Matrix (Fin r) (Fin r) K) * heisFourierMat ζ =
        heisFourierMat ζ * diagonal t) → g ∈ H)
    {d : Fin r → K} (hd : ∀ k, d k ^ (ℓ ^ f + 1) = 1) (hdet : ∏ k, d k = 1) :
    ∃ γ ∈ H, (γ : Matrix (Fin r) (Fin r) K) =
      heisFourierMat ζ * diagonal d * (heisFourierMat ζ)⁻¹ := by
  have hΦ : IsUnit (heisFourierMat ζ : Matrix (Fin r) (Fin r) K).det :=
    isUnit_iff_ne_zero.mpr (det_heisFourierMat_ne_zero hζ)
  have hdet' := ug86_det_conj hζ d
  rw [hdet] at hdet'
  let γ : GL (Fin r) K := Matrix.GeneralLinearGroup.mkOfDetNeZero
    (heisFourierMat ζ * diagonal d * (heisFourierMat ζ)⁻¹) (by rw [hdet']; exact one_ne_zero)
  have hγ : γ ∈ unitarySU ℓ f K r :=
    (mem_unitarySU_iff h).mpr ⟨hdet', ug86_conj_unitary h hζ hr hrq hd⟩
  refine ⟨γ, hTw γ hγ ⟨d, ?_⟩, rfl⟩
  show heisFourierMat ζ * diagonal d * (heisFourierMat ζ)⁻¹ * heisFourierMat ζ =
    heisFourierMat ζ * diagonal d
  rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hΦ, Matrix.mul_one]

theorem ug86_det_zFix [NeZero r] {ν : K} (hν : ν ≠ 0) :
    (zFix ν : Matrix (Fin r) (Fin r) K).det = 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by have := NeZero.pos r; omega⟩
  rw [zFix, det_diagonal, Fin.prod_univ_succ]
  simp [Fin.val_succ, hν]

theorem ug86_zFix_unitary [NeZero r] (h : UnitaryFieldData ℓ f K) {κ : K}
    (hκ : κ ^ (ℓ ^ f + 1) = 1) :
    ((zFix κ : Matrix (Fin r) (Fin r) K).map h.bar)ᵀ * zFix κ = 1 := by
  have hτ : ∀ i : Fin r, (if (i : ℕ) = 0 then (κ ^ (r - 1))⁻¹ else κ) ^ (ℓ ^ f + 1) = 1 := by
    intro i
    split_ifs
    · rw [inv_pow, ug86_pow_pow_eq_one hκ, inv_one]
    · exact hκ
  rw [zFix, diagonal_map (map_zero _), diagonal_transpose, diagonal_mul_diagonal,
    ← diagonal_one]
  congr 1
  funext i
  rw [ug86_bar_eq_inv h (hτ i)]
  exact inv_mul_cancel₀ (ug86_ne_zero_of_pow_eq_one (hτ i))

theorem ug86_exists_mem_torus [NeZero r] (h : UnitaryFieldData ℓ f K) (H : Subgroup (GL (Fin r) K))
    (hT : ∀ g ∈ unitarySU ℓ f K r, (∃ t, (g : Matrix (Fin r) (Fin r) K) = diagonal t) → g ∈ H)
    {κ : K} (hκ : κ ^ (ℓ ^ f + 1) = 1) :
    ∃ t ∈ H, (t : Matrix (Fin r) (Fin r) K) = zFix κ := by
  have hdet := ug86_det_zFix (r := r) (ug86_ne_zero_of_pow_eq_one hκ)
  let t : GL (Fin r) K := Matrix.GeneralLinearGroup.mkOfDetNeZero (zFix κ)
    (by rw [hdet]; exact one_ne_zero)
  have ht : t ∈ unitarySU ℓ f K r :=
    (mem_unitarySU_iff h).mpr ⟨hdet, ug86_zFix_unitary h hκ⟩
  exact ⟨t, hT t ht ⟨fun i : Fin r => if (i : ℕ) = 0 then (κ ^ (r - 1))⁻¹ else κ, rfl⟩, rfl⟩

theorem ug86_conj_zFix_apply [NeZero r] {A : Matrix (Fin r) (Fin r) K} (hA : IsUnit A.det)
    (ν : K) (i j : Fin r) :
    (A * zFix ν * A⁻¹ : Matrix (Fin r) (Fin r) K) i j = ν * (if i = j then 1 else 0) +
      ((ν ^ (r - 1))⁻¹ - ν) * (A i 0 * A⁻¹ 0 j) := by
  have hAA : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv _ hA
  have hz : zFix ν = diagonal (fun a : Fin r =>
      ν + (if a = 0 then (ν ^ (r - 1))⁻¹ - ν else 0)) := by
    rw [zFix]
    congr 1
    funext a
    by_cases ha : a = 0
    · subst ha
      simp
    · have ha' : (a : ℕ) ≠ 0 := fun h' => ha (Fin.val_eq_zero_iff.mp h')
      simp [ha, ha']
  have hsum : ∑ a, A i a * A⁻¹ a j = if i = j then 1 else 0 := by
    have h1 := congrFun (congrFun hAA i) j
    rwa [Matrix.mul_apply, Matrix.one_apply] at h1
  rw [hz, Matrix.mul_apply]
  have h1 : ∀ a : Fin r, (A * diagonal (fun a : Fin r =>
      ν + (if a = 0 then (ν ^ (r - 1))⁻¹ - ν else 0))) i a * A⁻¹ a j =
      ν * (A i a * A⁻¹ a j) +
        (if a = 0 then ((ν ^ (r - 1))⁻¹ - ν) * (A i 0 * A⁻¹ 0 j) else 0) := by
    intro a
    rw [Matrix.mul_diagonal]
    by_cases ha : a = 0
    · subst ha
      simp only [if_true]
      ring
    · simp only [if_neg ha]
      ring
  rw [Finset.sum_congr rfl fun a _ => h1 a, Finset.sum_add_distrib, ← Finset.mul_sum, hsum,
    Finset.sum_ite_eq']
  simp

theorem exists_fixer_of_ne (h : UnitaryFieldData ℓ f K) {r : ℕ} [Fact r.Prime] (hr : 5 ≤ r)
    (hrq : r ∣ ℓ ^ f + 1) (hne : ℓ ^ f + 1 ≠ r) {ζ : K} (hζ : IsPrimitiveRoot ζ r)
    (H : Subgroup (GL (Fin r) K))
    (hT : ∀ g ∈ unitarySU ℓ f K r, (∃ t, (g : Matrix (Fin r) (Fin r) K) = diagonal t) → g ∈ H)
    (hTw : ∀ g ∈ unitarySU ℓ f K r, (∃ t, (g : Matrix (Fin r) (Fin r) K) * heisFourierMat ζ =
        heisFourierMat ζ * diagonal t) → g ∈ H) :
    ∃ g ∈ H, (∀ i, i ≠ 0 → (g : Matrix (Fin r) (Fin r) K) i 0 = 0) ∧
      ¬ IsMonomialMat (g : Matrix (Fin r) (Fin r) K) := by
  have hζq : ζ ^ (ℓ ^ f + 1) = 1 := ug86_pow_eq_one_of_dvd hζ.pow_eq_one hrq
  have hr0 : (r : K) ≠ 0 := heis_natCast_ne_zero hζ (by omega)
  obtain ⟨κ, hκ, hκr⟩ := ug86_exists_kappa h (Fact.out : r.Prime) hne
  have hκ0 : κ ≠ 0 := ug86_ne_zero_of_pow_eq_one hκ
  obtain ⟨γ, hγH, hγ⟩ := ug86_exists_mem_fourier h hζ (by omega) hrq H hTw
    (ug86_diag_pow_eq_one hζq) (ug86_prod_diag hr hζ.pow_eq_one)
  obtain ⟨t, htH, ht⟩ := ug86_exists_mem_torus h H hT hκ
  set Γ : Matrix (Fin r) (Fin r) K :=
    heisFourierMat ζ * diagonal (ug86_diag ζ) * (heisFourierMat ζ)⁻¹ with hΓ
  have hΓdet : IsUnit Γ.det := by
    rw [hΓ, ug86_det_conj hζ, ug86_prod_diag hr hζ.pow_eq_one]
    exact isUnit_one
  have hgmat : ((γ * t * γ⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) =
      Γ * zFix κ * Γ⁻¹ := by
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
      Matrix.GeneralLinearGroup.coe_inv, hγ, ht]
  have hinv : Γ⁻¹ = (Γ.map h.bar)ᵀ :=
    Matrix.inv_eq_left_inv
      (ug86_conj_unitary h hζ (by omega) hrq (ug86_diag_pow_eq_one hζq))
  have hinv_apply : ∀ j : Fin r, Γ⁻¹ 0 j = h.bar (Γ j 0) := fun j => by
    rw [hinv, Matrix.transpose_apply, Matrix.map_apply]
  have hΓ00 : Γ 0 0 = 0 := by
    have h0 := ug86_gamma_apply_zero hζ hr (0 : Fin r) (by rw [Fin.val_zero]; omega)
    rw [Fin.val_zero, pow_zero, sub_self, mul_zero, mul_zero] at h0
    exact h0
  have hΓ0 : Γ⁻¹ 0 0 = 0 := by rw [hinv_apply, hΓ00, map_zero]
  have hΓd : ∀ i : Fin r, 0 < (i : ℕ) → (i : ℕ) + 1 < r → Γ i 0 ≠ 0 := by
    intro i hi0 hi1
    rw [hΓ, ug86_gamma_apply_zero hζ hr i hi1]
    exact mul_ne_zero (inv_ne_zero hr0) (mul_ne_zero (sub_ne_zero.mpr (hζ.ne_one (by omega)))
      (sub_ne_zero.mpr (Ne.symm (hζ.pow_ne_one_of_pos_of_lt (by omega) (by omega)))))
  have hc : (κ ^ (r - 1))⁻¹ - κ ≠ 0 := by
    intro h0
    apply hκr
    have h1 : (κ ^ (r - 1))⁻¹ = κ := sub_eq_zero.mp h0
    calc κ ^ r = κ ^ (r - 1) * κ := by
          rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ r)]
      _ = κ ^ (r - 1) * (κ ^ (r - 1))⁻¹ := by rw [h1]
      _ = 1 := mul_inv_cancel₀ (pow_ne_zero _ hκ0)
  refine ⟨γ * t * γ⁻¹, H.mul_mem (H.mul_mem hγH htH) (H.inv_mem hγH), ?_, ?_⟩
  · intro i hi
    rw [hgmat, ug86_conj_zFix_apply hΓdet, if_neg hi, hΓ0]
    ring
  · intro hmono
    have hB : Γ⁻¹ 0 ⟨1, by omega⟩ ≠ 0 := by
      rw [hinv_apply]
      exact (map_ne_zero h.bar).mpr (hΓd ⟨1, by omega⟩ (by simp) (by simp; omega))
    have hentry : ∀ i : Fin r, 2 ≤ (i : ℕ) → (i : ℕ) + 1 < r →
        ((γ * t * γ⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) i ⟨1, by omega⟩ ≠ 0 := by
      intro i hi2 hi1
      rw [hgmat, ug86_conj_zFix_apply hΓdet,
        if_neg (fun hij => by have := congrArg Fin.val hij; simp at this; omega), mul_zero,
        zero_add]
      exact mul_ne_zero hc (mul_ne_zero (hΓd i (by omega) hi1) hB)
    have h23 := hmono ⟨1, by omega⟩ ⟨2, by omega⟩ ⟨3, by omega⟩
      (hentry ⟨2, by omega⟩ (by simp) (by simp; omega))
      (hentry ⟨3, by omega⟩ (by simp) (by simp; omega))
    have h23' := congrArg Fin.val h23
    simp at h23'

end CFSG.LieType.SeitzGeneration

end
