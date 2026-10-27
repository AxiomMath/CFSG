module

public import CFSG.CGT.Stroth77.StrothAmbient
public import CFSG.CGT.Stroth77.Extension24Basic

public section

namespace CFSG.CGT.Stroth77

section Torus

variable (s : ℕ)

theorem uv_gens_t101 (x y z : ℤ) :
    (StrothTypeIndex.t101 s).action.φuv
        (x • gen (StrothTypeIndex.t101 s).k 0 + y • gen _ 1 + z • gen _ 2) =
      (-3 * x + 2 * y + 2 * z) • gen (StrothTypeIndex.t101 s).k 0 +
        (-2 * x + y + (4 * (2 ^ s) ^ 2 + 6 * 2 ^ s + 2) * z) • gen _ 1 +
        (-2 * x + (2 * 2 ^ s + 2) * y + z) • gen _ 2 := by
  have h0 : (StrothTypeIndex.t101 s).action.φuv (gen _ 0) =
      (-3 : ℤ) • gen (StrothTypeIndex.t101 s).k 0 + (-2 : ℤ) • gen _ 1 + (-2 : ℤ) • gen _ 2 :=
    Type101.uv_c s
  have h1 : (StrothTypeIndex.t101 s).action.φuv (gen _ 1) =
      (2 : ℤ) • gen (StrothTypeIndex.t101 s).k 0 + (1 : ℤ) • gen _ 1 +
        (2 * (2 ^ s) + 2 : ℤ) • gen _ 2 :=
    Type101.uv_a s
  have h2 : (StrothTypeIndex.t101 s).action.φuv (gen _ 2) =
      (2 : ℤ) • gen (StrothTypeIndex.t101 s).k 0 + (4 * (2 ^ s) ^ 2 + 6 * (2 ^ s) + 2 : ℤ) •
        gen _ 1 + (1 : ℤ) • gen _ 2 :=
    Type101.uv_b s
  rw [map_add, map_add, map_zsmul, map_zsmul, map_zsmul, h0, h1, h2]
  module

theorem t_gens_t101 (x y z : ℤ) :
    (StrothTypeIndex.t101 s).action.φt
        (x • gen (StrothTypeIndex.t101 s).k 0 + y • gen _ 1 + z • gen _ 2) =
      (x + (-4 * 2 ^ s - 2) * z) • gen (StrothTypeIndex.t101 s).k 0 +
        (2 * x + (2 * 2 ^ s - 1) * y + (-2 * 2 ^ s - 2) * z) • gen _ 1 +
        ((-2 * 2 ^ s - 1) * z) • gen _ 2 := by
  have h0 : (StrothTypeIndex.t101 s).action.φt (gen _ 0) =
      (1 : ℤ) • gen (StrothTypeIndex.t101 s).k 0 + (2 : ℤ) • gen _ 1 :=
    Type101.t_c s
  have h1 : (StrothTypeIndex.t101 s).action.φt (gen _ 1) =
      (2 * (2 ^ s) - 1 : ℤ) • gen (StrothTypeIndex.t101 s).k 1 :=
    Type101.t_a s
  have h2 : (StrothTypeIndex.t101 s).action.φt (gen _ 2) =
      (-4 * (2 ^ s) - 2 : ℤ) • gen (StrothTypeIndex.t101 s).k 0 + (-2 * (2 ^ s) - 2 : ℤ) •
        gen _ 1 + (-2 * (2 ^ s) - 1 : ℤ) • gen _ 2 :=
    Type101.t_b s
  rw [map_add, map_add, map_zsmul, map_zsmul, map_zsmul, h0, h1, h2]
  module

theorem u_gens_t101 (x y z : ℤ) :
    (StrothTypeIndex.t101 s).action.φu
        (x • gen (StrothTypeIndex.t101 s).k 0 + y • gen _ 1 + z • gen _ 2) =
      x • gen (StrothTypeIndex.t101 s).k 0 + z • gen _ 1 + y • gen _ 2 := by
  have h0 : (StrothTypeIndex.t101 s).action.φu (gen _ 0) =
      (1 : ℤ) • gen (StrothTypeIndex.t101 s).k 0 :=
    Type101.u_c s
  have h1 : (StrothTypeIndex.t101 s).action.φu (gen _ 1) =
      (1 : ℤ) • gen (StrothTypeIndex.t101 s).k 2 :=
    Type101.u_a s
  have h2 : (StrothTypeIndex.t101 s).action.φu (gen _ 2) =
      (1 : ℤ) • gen (StrothTypeIndex.t101 s).k 1 :=
    Type101.u_b s
  rw [map_add, map_add, map_zsmul, map_zsmul, map_zsmul, h0, h1, h2]
  module

theorem k_zero_t101 : (StrothTypeIndex.t101 s).k 0 = s + 1 := rfl
theorem k_one_t101 : (StrothTypeIndex.t101 s).k 1 = s + 2 := rfl
theorem k_two_t101 : (StrothTypeIndex.t101 s).k 2 = s + 2 := rfl

theorem exists_u_class_t101 (r : Torus (StrothTypeIndex.t101 s).k)
    (h : r + (StrothTypeIndex.t101 s).action.φu r = 0) :
    ∃ d : Torus (StrothTypeIndex.t101 s).k,
      r = d - (StrothTypeIndex.t101 s).action.φu d ∨
        r = d - (StrothTypeIndex.t101 s).action.φu d +
          (2 ^ s : ℤ) • gen (StrothTypeIndex.t101 s).k 0 := by
  obtain ⟨x, y, z, rfl⟩ := torus_eq_zsmul_gens _ r
  rw [u_gens_t101] at h
  have e : (x + x) • gen (StrothTypeIndex.t101 s).k 0 + (y + z) • gen _ 1 + (z + y) • gen _ 2 =
      (0 : ℤ) • gen (StrothTypeIndex.t101 s).k 0 + (0 : ℤ) • gen _ 1 + (0 : ℤ) • gen _ 2 := by
    rw [zero_smul, zero_smul, zero_smul, add_zero, add_zero, ← h]
    module
  obtain ⟨h0, h1, -⟩ := zsmul_gens_dvd_of_eq e
  rw [k_zero_t101] at h0
  rw [k_one_t101] at h1
  have hx : (2 : ℤ) ^ s ∣ x := by
    obtain ⟨q, hq⟩ := h0
    have : (2 : ℤ) ^ (s + 1) = 2 ^ s * 2 := pow_succ 2 s
    rw [this] at hq
    exact ⟨-q, mul_left_cancel₀ (two_ne_zero (α := ℤ)) (by linear_combination -hq)⟩
  obtain ⟨q, rfl⟩ := hx
  refine ⟨y • gen _ 1, ?_⟩
  have ed : y • gen (StrothTypeIndex.t101 s).k 1 -
      (StrothTypeIndex.t101 s).action.φu (y • gen (StrothTypeIndex.t101 s).k 1) =
      (0 : ℤ) • gen (StrothTypeIndex.t101 s).k 0 + y • gen _ 1 + (-y) • gen _ 2 := by
    have := u_gens_t101 s 0 y 0
    simp only [zero_smul, zero_add, add_zero] at this
    rw [this]
    module
  rcases Int.even_or_odd q with ⟨q', rfl⟩ | ⟨q', rfl⟩
  · left
    rw [ed]
    refine zsmul_gens_eq_of_dvd ?_ (by simp) ?_
    · rw [k_zero_t101]
      exact ⟨-q', by rw [pow_succ]; ring⟩
    · rw [k_two_t101]
      obtain ⟨w, hw⟩ := h1
      exact ⟨w, by linear_combination hw⟩
  · right
    rw [ed]
    have e2 : (0 : ℤ) • gen (StrothTypeIndex.t101 s).k 0 + y • gen _ 1 + (-y) • gen _ 2 +
        (2 ^ s : ℤ) • gen _ 0 =
        (2 ^ s : ℤ) • gen (StrothTypeIndex.t101 s).k 0 + y • gen _ 1 + (-y) • gen _ 2 := by
      module
    rw [e2]
    refine zsmul_gens_eq_of_dvd ?_ (by simp) ?_
    · rw [k_zero_t101]
      exact ⟨-q', by rw [pow_succ]; ring⟩
    · rw [k_two_t101]
      obtain ⟨w, hw⟩ := h1
      exact ⟨w, by linear_combination hw⟩

theorem exists_coboundary_t101 (hs : 1 ≤ s) (ruv rt : Torus (StrothTypeIndex.t101 s).k)
    (h2 : rt + (StrothTypeIndex.t101 s).action.φt rt = 0)
    (h5 : (StrothTypeIndex.t101 s).action.φu ruv = ruv)
    (h6 : rt = (StrothTypeIndex.t101 s).action.φu ruv +
      (StrothTypeIndex.t101 s).action.φu ((StrothTypeIndex.t101 s).action.φuv rt)) :
    ∃ d : Torus (StrothTypeIndex.t101 s).k, (StrothTypeIndex.t101 s).action.φu d = d ∧
      ruv = d - (StrothTypeIndex.t101 s).action.φuv d ∧
      rt = d - (StrothTypeIndex.t101 s).action.φt d := by
  obtain ⟨w0, w1, w2, rfl⟩ := torus_eq_zsmul_gens _ rt
  obtain ⟨v0, v1, v2, rfl⟩ := torus_eq_zsmul_gens _ ruv
  obtain ⟨N', hN'⟩ : ∃ N' : ℤ, (2 : ℤ) ^ s = 2 * N' :=
    ⟨2 ^ (s - 1), by rw [← pow_succ']; congr 1; omega⟩
  have hK0 : (2 : ℤ) ^ (StrothTypeIndex.t101 s).k 0 = 4 * N' := by
    rw [k_zero_t101, pow_succ, hN']; ring
  have hK1 : (2 : ℤ) ^ (StrothTypeIndex.t101 s).k 1 = 8 * N' := by
    rw [k_one_t101, pow_succ, pow_succ, hN']; ring
  have hK2 : (2 : ℤ) ^ (StrothTypeIndex.t101 s).k 2 = 8 * N' := by
    rw [k_two_t101, pow_succ, pow_succ, hN']; ring
  have hN0 : N' ≠ 0 := by
    intro h0
    have : (2 : ℤ) ^ s ≠ 0 := pow_ne_zero _ two_ne_zero
    rw [hN', h0, mul_zero] at this
    exact this rfl
  rw [t_gens_t101] at h2
  have e2 : (w0 + (w0 + (-4 * 2 ^ s - 2) * w2)) • gen (StrothTypeIndex.t101 s).k 0 +
      (w1 + (2 * w0 + (2 * 2 ^ s - 1) * w1 + (-2 * 2 ^ s - 2) * w2)) • gen _ 1 +
      (w2 + (-2 * 2 ^ s - 1) * w2) • gen _ 2 =
      (0 : ℤ) • gen (StrothTypeIndex.t101 s).k 0 + (0 : ℤ) • gen _ 1 + (0 : ℤ) • gen _ 2 := by
    rw [zero_smul, zero_smul, zero_smul, add_zero, add_zero, ← h2]
    module
  obtain ⟨-, ⟨k2, hk2⟩, ⟨k3, hk3⟩⟩ := zsmul_gens_dvd_of_eq e2
  rw [u_gens_t101] at h5
  obtain ⟨-, ⟨f5, hf5⟩, -⟩ := zsmul_gens_dvd_of_eq h5
  rw [uv_gens_t101, u_gens_t101, u_gens_t101] at h6
  have e6 : w0 • gen (StrothTypeIndex.t101 s).k 0 + w1 • gen _ 1 + w2 • gen _ 2 =
      (v0 + (-3 * w0 + 2 * w1 + 2 * w2)) • gen (StrothTypeIndex.t101 s).k 0 +
        (v2 + (-2 * w0 + (2 * 2 ^ s + 2) * w1 + w2)) • gen _ 1 +
        (v1 + (-2 * w0 + w1 + (4 * (2 ^ s) ^ 2 + 6 * 2 ^ s + 2) * w2)) • gen _ 2 := by
    rw [h6]
    module
  obtain ⟨⟨e0, he0⟩, ⟨e1', he1'⟩, ⟨e2', he2'⟩⟩ := zsmul_gens_dvd_of_eq e6
  rw [hK1] at hk2 hf5 he1'
  rw [hK2] at hk3 he2'
  rw [hK0] at he0
  rw [hN'] at hk2 hk3 he1' he2'
  obtain ⟨ω, hω⟩ : ∃ ω, w2 = 2 * ω :=
    ⟨k3, mul_left_cancel₀ (show (4 : ℤ) * N' ≠ 0 by positivity) (by linear_combination hk3)⟩
  subst hω
  obtain ⟨μ, hμ⟩ : ∃ μ, w1 = 2 * μ :=
    ⟨e1' - e2' + f5 + 4 * N' * ω + 3 * ω, mul_left_cancel₀
      (show (4 : ℤ) * N' ≠ 0 by positivity) (by linear_combination he1' - he2' + hf5)⟩
  subst hμ
  obtain ⟨κ, hκ⟩ : ∃ κ, w0 = 2 * ω + 4 * N' * κ :=
    ⟨ω - μ - k2, mul_left_cancel₀ (two_ne_zero (α := ℤ)) (by linear_combination -hk2)⟩
  subst hκ
  have hv0 : v0 = 4 * (2 * ω + 4 * N' * κ) - 2 * (2 * μ) - 2 * (2 * ω) + 4 * N' * e0 := by
    linear_combination he0
  have hv2 : v2 = 2 * (2 * ω + 4 * N' * κ) - (4 * N' + 1) * (2 * μ) - 2 * ω + 8 * N' * e1' := by
    linear_combination he1'
  have hv1 : v1 = v2 + 8 * N' * f5 := by linear_combination hf5
  subst hv1
  subst hv0 hv2
  refine ⟨(2 * ((1 - 2 * N') * ω) - μ) • gen _ 0 + ((1 - 2 * N') * ω) • gen _ 1 +
    ((1 - 2 * N') * ω) • gen _ 2, ?_, ?_, ?_⟩
  · rw [u_gens_t101]
  · rw [uv_gens_t101, hN']
    refine (zsmul_gens_eq_of_dvd (p' := 4 * (2 * ((1 - 2 * N') * ω) - μ) - 4 * ((1 - 2 * N') * ω))
      (q' := 2 * (2 * ((1 - 2 * N') * ω) - μ) - (4 * (2 * N') ^ 2 + 6 * (2 * N') + 2) *
        ((1 - 2 * N') * ω))
      (r' := 2 * (2 * ((1 - 2 * N') * ω) - μ) - (2 * (2 * N') + 2) * ((1 - 2 * N') * ω))
      ?_ ?_ ?_).trans (by module)
    · rw [hK0]; exact ⟨-2 * ω - 4 * κ - e0, by ring⟩
    · rw [hK1]; exact ⟨4 * ω * N' ^ 2 + ω * N' - 2 * ω + μ - κ - e1' - f5, by ring⟩
    · rw [hK2]; exact ⟨ω * N' - ω + μ - κ - e1', by ring⟩
  · rw [t_gens_t101, hN']
    refine (zsmul_gens_eq_of_dvd (p' := (4 * (2 * N') + 2) * ((1 - 2 * N') * ω))
      (q' := 4 * ((1 - 2 * N') * ω) - 2 * (2 * ((1 - 2 * N') * ω) - μ))
      (r' := (2 * (2 * N') + 2) * ((1 - 2 * N') * ω)) ?_ ?_ ?_).trans (by module)
    · rw [hK0]; exact ⟨-4 * ω * N' + ω - κ, by ring⟩
    · rw [hK1]; exact ⟨0, by ring⟩
    · rw [hK2]; exact ⟨-ω * N', by ring⟩

end Torus

section Group

variable {G : Type*} [Group G]

theorem conj_mem_omegaIn_one {D : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (D : Set G))
    {y : G} (hy : y ∈ omegaIn 1 D) : g⁻¹ * y * g ∈ omegaIn 1 D := by
  obtain ⟨y', hy', rfl⟩ := hy
  induction hy' using Subgroup.closure_induction with
  | mem x hx =>
    have hx' : (x : G) ^ (2 ^ 1) = 1 := by
      have h := congrArg Subtype.val (show x ^ (2 ^ 1) = 1 from hx)
      simpa only [Subgroup.coe_pow, Subgroup.coe_one] using h
    refine ⟨⟨g⁻¹ * (x : G) * g, (Subgroup.mem_normalizer_iff''.mp hg x).mp x.2⟩,
      Subgroup.subset_closure ?_, rfl⟩
    change (⟨g⁻¹ * (x : G) * g, _⟩ : D) ^ (2 ^ 1) = 1
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    have h := conj_pow (a := g⁻¹) (b := (x : G)) (i := 2 ^ 1)
    rw [inv_inv] at h
    rw [h, hx', mul_one, inv_mul_cancel]
  | one =>
    rw [map_one, mul_one, inv_mul_cancel]
    exact one_mem _
  | mul x y _ _ hx hy =>
    have h := mul_mem hx hy
    rw [map_mul]
    convert h using 1
    group
  | inv x _ hx =>
    have h := inv_mem hx
    rw [map_inv]
    convert h using 1
    group

theorem mem_normalizer_inf_centralizer_omegaIn {S D : Subgroup G} {g : G} (hgS : g ∈ S)
    (hgD : g ∈ Subgroup.normalizer (D : Set G)) (hg2 : g * g = 1) :
    g ∈ Subgroup.normalizer ((S ⊓ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) : Subgroup G) : Set G) := by
  have hgi : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg2
  have key : ∀ h, h ∈ (S ⊓ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) : Subgroup G) →
      g⁻¹ * h * g ∈ (S ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) : Subgroup G) := by
    rintro h ⟨⟨hS, hN⟩, hC⟩
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem hgS) hS) hgS,
      mul_mem (mul_mem (inv_mem hgD) hN) hgD⟩, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    have hy' : g * y * g⁻¹ ∈ omegaIn 1 D := by
      have := conj_mem_omegaIn_one (inv_mem hgD) hy
      rwa [inv_inv] at this
    have hc := Subgroup.mem_centralizer_iff.mp hC _ hy'
    calc y * (g⁻¹ * h * g) = g⁻¹ * ((g * y * g⁻¹) * h) * g := by group
      _ = g⁻¹ * (h * (g * y * g⁻¹)) * g := by rw [hc]
      _ = g⁻¹ * h * g * y := by group
  rw [Subgroup.mem_normalizer_iff'']
  intro h
  refine ⟨key h, fun hh => ?_⟩
  have := key _ hh
  rwa [hgi, ← mul_assoc, ← mul_assoc, hg2, one_mul, mul_assoc, hg2, mul_one] at this

theorem conj_mul_mul_inv_eq {x e d : G} (hx : x * x = 1) :
    (e * d)⁻¹ * x * (e * d) * x⁻¹ = d⁻¹ * (e⁻¹ * x * e * x⁻¹) * (x⁻¹ * d * x) := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hx' : ∀ y, x * (x * y) = y := fun y => by rw [← mul_assoc, hx, one_mul]
  rw [hxi, mul_inv_rev]
  simp only [mul_assoc, hx']

end Group

section Coord

variable {G : Type*} [Group G] {D : Subgroup G} {s : ℕ}
  (eD : Additive D ≃+ Torus (StrothTypeIndex.t101 s).k)

noncomputable def crd101 (g : G) : Torus (StrothTypeIndex.t101 s).k := by
  classical
  exact if h : g ∈ D then eD (Additive.ofMul ⟨g, h⟩) else 0

theorem crd101_of_mem {g : G} (h : g ∈ D) : crd101 eD g = eD (Additive.ofMul ⟨g, h⟩) := by
  rw [crd101, dif_pos h]

theorem crd101_mul {g h : G} (hg : g ∈ D) (hh : h ∈ D) :
    crd101 eD (g * h) = crd101 eD g + crd101 eD h := by
  rw [crd101_of_mem eD (mul_mem hg hh), crd101_of_mem eD hg, crd101_of_mem eD hh, ← map_add]
  rfl

theorem crd101_inj {g h : G} (hg : g ∈ D) (hh : h ∈ D) (he : crd101 eD g = crd101 eD h) :
    g = h := by
  rw [crd101_of_mem eD hg, crd101_of_mem eD hh] at he
  exact congrArg Subtype.val (Additive.ofMul.injective (eD.injective he))

theorem crd101_one : crd101 eD (1 : G) = 0 := by
  rw [crd101_of_mem eD (one_mem D)]
  exact map_zero eD

theorem crd101_inv {g : G} (hg : g ∈ D) : crd101 eD g⁻¹ = -crd101 eD g := by
  have h := crd101_mul eD hg (inv_mem hg)
  rw [mul_inv_cancel, crd101_one] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

theorem crd101_conj {x : G} (hx : x ∈ Subgroup.normalizer (D : Set G))
    {φ : Torus (StrothTypeIndex.t101 s).k →+ Torus (StrothTypeIndex.t101 s).k}
    (hφ : ∀ y : D, eD (Additive.ofMul (conjBy hx y)) = φ (eD (Additive.ofMul y)))
    {g : G} (hg : g ∈ D) : crd101 eD (x⁻¹ * g * x) = φ (crd101 eD g) := by
  rw [crd101_of_mem eD hg, crd101_of_mem eD ((Subgroup.mem_normalizer_iff''.mp hx g).mp hg)]
  exact hφ ⟨g, hg⟩

theorem crd101_conj_mul {x e d : G} (hx : x ∈ Subgroup.normalizer (D : Set G)) (hx2 : x * x = 1)
    {φ : Torus (StrothTypeIndex.t101 s).k →+ Torus (StrothTypeIndex.t101 s).k}
    (hφ : ∀ y : D, eD (Additive.ofMul (conjBy hx y)) = φ (eD (Additive.ofMul y)))
    (hr : e⁻¹ * x * e * x⁻¹ ∈ D) (hd : d ∈ D) :
    (e * d)⁻¹ * x * (e * d) * x⁻¹ ∈ D ∧
      crd101 eD ((e * d)⁻¹ * x * (e * d) * x⁻¹) =
        crd101 eD (e⁻¹ * x * e * x⁻¹) - crd101 eD d + φ (crd101 eD d) := by
  have hxd : x⁻¹ * d * x ∈ D := (Subgroup.mem_normalizer_iff''.mp hx d).mp hd
  rw [conj_mul_mul_inv_eq hx2]
  refine ⟨mul_mem (mul_mem (inv_mem hd) hr) hxd, ?_⟩
  rw [crd101_mul eD (mul_mem (inv_mem hd) hr) hxd, crd101_mul eD (inv_mem hd) hr,
    crd101_inv eD hd, crd101_conj eD hx hφ hd]
  abel

theorem cocycle101 {uv t u : G} (huv2 : uv * uv = 1) (ht2 : t * t = 1) (hu2 : u * u = 1)
    (huvu : uv * u = u * uv) (htu : t * u = u * uv * t)
    (huvN : uv ∈ Subgroup.normalizer (D : Set G)) (htN : t ∈ Subgroup.normalizer (D : Set G))
    (huN : u ∈ Subgroup.normalizer (D : Set G))
    (huvc : ∀ x : D, eD (Additive.ofMul (conjBy huvN x)) =
      (StrothTypeIndex.t101 s).action.φuv (eD (Additive.ofMul x)))
    (htc : ∀ x : D, eD (Additive.ofMul (conjBy htN x)) =
      (StrothTypeIndex.t101 s).action.φt (eD (Additive.ofMul x)))
    (huc : ∀ x : D, eD (Additive.ofMul (conjBy huN x)) =
      (StrothTypeIndex.t101 s).action.φu (eD (Additive.ofMul x)))
    {e : G} (huv : e⁻¹ * uv * e * uv⁻¹ ∈ D)
    (ht : e⁻¹ * t * e * t⁻¹ ∈ D) (hu : e⁻¹ * u * e * u⁻¹ ∈ D) :
    crd101 eD (e⁻¹ * t * e * t⁻¹) +
        (StrothTypeIndex.t101 s).action.φt (crd101 eD (e⁻¹ * t * e * t⁻¹)) = 0 ∧
      crd101 eD (e⁻¹ * u * e * u⁻¹) +
        (StrothTypeIndex.t101 s).action.φu (crd101 eD (e⁻¹ * u * e * u⁻¹)) = 0 ∧
      crd101 eD (e⁻¹ * uv * e * uv⁻¹) +
          (StrothTypeIndex.t101 s).action.φuv (crd101 eD (e⁻¹ * u * e * u⁻¹)) =
        crd101 eD (e⁻¹ * u * e * u⁻¹) +
          (StrothTypeIndex.t101 s).action.φu (crd101 eD (e⁻¹ * uv * e * uv⁻¹)) ∧
      crd101 eD (e⁻¹ * t * e * t⁻¹) +
          (StrothTypeIndex.t101 s).action.φt (crd101 eD (e⁻¹ * u * e * u⁻¹)) =
        crd101 eD (e⁻¹ * u * e * u⁻¹) +
          (StrothTypeIndex.t101 s).action.φu (crd101 eD (e⁻¹ * uv * e * uv⁻¹)) +
          (StrothTypeIndex.t101 s).action.φu ((StrothTypeIndex.t101 s).action.φuv
            (crd101 eD (e⁻¹ * t * e * t⁻¹))) := by
  have cuv := fun {g : G} (hg : g ∈ D) => crd101_conj eD huvN huvc hg
  have ct := fun {g : G} (hg : g ∈ D) => crd101_conj eD htN htc hg
  have cu := fun {g : G} (hg : g ∈ D) => crd101_conj eD huN huc hg
  have nuv := fun {g : G} (hg : g ∈ D) => (Subgroup.mem_normalizer_iff''.mp huvN g).mp hg
  have nt := fun {g : G} (hg : g ∈ D) => (Subgroup.mem_normalizer_iff''.mp htN g).mp hg
  have nu := fun {g : G} (hg : g ∈ D) => (Subgroup.mem_normalizer_iff''.mp huN g).mp hg
  have iuv : uv⁻¹ = uv := inv_eq_of_mul_eq_one_right huv2
  have it : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have iu : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have suv : ∀ y, uv * (uv * y) = y := fun y => by rw [← mul_assoc, huv2, one_mul]
  have st : ∀ y, t * (t * y) = y := fun y => by rw [← mul_assoc, ht2, one_mul]
  have su : ∀ y, u * (u * y) = y := fun y => by rw [← mul_assoc, hu2, one_mul]
  have c0 : u * uv = uv * u := huvu.symm
  have c1 : ∀ y, u * (uv * y) = uv * (u * y) := fun y => by
    rw [← mul_assoc, c0, mul_assoc]
  have tu : ∀ y, t * (u * y) = uv * (u * (t * y)) := fun y => by
    rw [← mul_assoc, htu, mul_assoc, mul_assoc, c1]
  have ut : u * t = t * (uv * u) := by
    have h := congrArg (·⁻¹) htu
    simpa only [mul_inv_rev, iuv, it, iu, mul_assoc] using h
  have ga : (e⁻¹ * t * e * t⁻¹) * (t⁻¹ * (e⁻¹ * t * e * t⁻¹) * t) = 1 := by
    rw [it]
    simp only [mul_assoc, st, mul_inv_cancel_left, inv_mul_cancel_left, ht2]
  have gb : (e⁻¹ * u * e * u⁻¹) * (u⁻¹ * (e⁻¹ * u * e * u⁻¹) * u) = 1 := by
    rw [iu]
    simp only [mul_assoc, su, mul_inv_cancel_left, inv_mul_cancel_left, hu2]
  have gc : (e⁻¹ * uv * e * uv⁻¹) * (uv⁻¹ * (e⁻¹ * u * e * u⁻¹) * uv) =
      (e⁻¹ * u * e * u⁻¹) * (u⁻¹ * (e⁻¹ * uv * e * uv⁻¹) * u) := by
    rw [iuv, iu]
    simp only [mul_assoc, suv, su, mul_inv_cancel_left, inv_mul_cancel_left, c0, c1]
  have gd : (e⁻¹ * t * e * t⁻¹) * (t⁻¹ * (e⁻¹ * u * e * u⁻¹) * t) =
      (e⁻¹ * u * e * u⁻¹) * (u⁻¹ * (e⁻¹ * uv * e * uv⁻¹) * u) *
        (u⁻¹ * (uv⁻¹ * (e⁻¹ * t * e * t⁻¹) * uv) * u) := by
    rw [iuv, iu, it]
    simp only [mul_assoc, suv, st, su, mul_inv_cancel_left, inv_mul_cancel_left, c0, c1, tu, ut]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := congrArg (crd101 eD) ga
    rwa [crd101_mul eD ht (nt ht), crd101_one, ct ht] at h
  · have h := congrArg (crd101 eD) gb
    rwa [crd101_mul eD hu (nu hu), crd101_one, cu hu] at h
  · have h := congrArg (crd101 eD) gc
    rwa [crd101_mul eD huv (nuv hu), crd101_mul eD hu (nu huv), cuv hu, cu huv] at h
  · have h := congrArg (crd101 eD) gd
    rwa [crd101_mul eD ht (nt hu), crd101_mul eD (mul_mem hu (nu huv)) (nu (nuv ht)),
      crd101_mul eD hu (nu huv), ct hu, cu huv, cu (nuv ht), cuv ht] at h

theorem exists_crd101_eq (δ : Torus (StrothTypeIndex.t101 s).k) : ∃ d ∈ D, crd101 eD d = δ :=
  ⟨_, (Additive.toMul (eD.symm δ)).2, by
    rw [crd101_of_mem eD (Additive.toMul (eD.symm δ)).2]
    simp⟩

theorem mul_comm_of_crd101_eq_zero {g x : G} (hm : g⁻¹ * x * g * x⁻¹ ∈ D)
    (h0 : crd101 eD (g⁻¹ * x * g * x⁻¹) = 0) : g * x = x * g := by
  have h1 := crd101_inj eD hm (one_mem D) (h0.trans (crd101_one eD).symm)
  rw [mul_inv_eq_one] at h1
  calc g * x = g * (g⁻¹ * x * g) := by rw [h1]
    _ = x * g := by group

end Coord

end CFSG.CGT.Stroth77
