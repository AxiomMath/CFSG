module

public import CFSG.ClassicalGroups.Unitary.Generation

public section

namespace CFSG.LieType.SeitzGeneration.Centers

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary

variable {K : Type*} [Field K] {σ : K ≃+* K} {n : ℕ}

@[expose] def IsCenter (H : Subgroup (SUid σ n)) (a : Fin n → K) : Prop :=
  herm σ a a = 0 ∧ ∀ c : K, c + σ c = 0 → ∃ g ∈ H, ∀ v, g • v = v + (c * herm σ a v) • a

variable {H : Subgroup (SUid σ n)} {a b : Fin n → K}

theorem isCenter_zero : IsCenter H (0 : Fin n → K) := by
  refine ⟨by simp, fun c _ => ⟨1, H.one_mem, fun v => ?_⟩⟩
  simp

theorem IsCenter.map (ha : IsCenter H a) {g : SUid σ n} (hg : g ∈ H) : IsCenter H (g • a) := by
  refine ⟨by rw [herm_smul_smul]; exact ha.1, fun c hc => ?_⟩
  obtain ⟨t, ht, hta⟩ := ha.2 c hc
  exact ⟨g * t * g⁻¹, H.mul_mem (H.mul_mem hg ht) (H.inv_mem hg),
    conj_smul_of_tv g t hta⟩

theorem IsCenter.smul (hσ : ∀ c, σ (σ c) = c) (ha : IsCenter H a) (μ : K) :
    IsCenter H (μ • a) := by
  refine ⟨by rw [herm_smul_left, herm_smul_right, ha.1]; ring, fun c hc => ?_⟩
  have hc' : (σ μ * μ * c) + σ (σ μ * μ * c) = 0 := by
    rw [map_mul, map_mul, hσ]
    linear_combination (σ μ * μ) * hc
  obtain ⟨g, hg, hga⟩ := ha.2 (σ μ * μ * c) hc'
  refine ⟨g, hg, fun v => ?_⟩
  rw [hga v, herm_smul_left, smul_smul]
  congr 2
  ring

theorem IsCenter.move (ha : IsCenter H a) (hb : IsCenter H b) {c : K} (hc : c + σ c = 0) :
    IsCenter H (b + (c * herm σ a b) • a) := by
  obtain ⟨g, hg, hga⟩ := ha.2 c hc
  have := hb.map hg
  rwa [hga b] at this

theorem IsCenter.add (hσ : ∀ c, σ (σ c) = c) (ha : IsCenter H a) (hb : IsCenter H b)
    (hab : herm σ (a + b) (a + b) = 0) (hne : herm σ b a ≠ 0) : IsCenter H (a + b) := by
  have hsum : herm σ b a + herm σ a b = 0 := by
    simpa [herm_add_left, herm_add_right, ha.1, hb.1] using hab
  have hw : herm σ b a + σ (herm σ b a) = 0 := by
    rw [← herm_conj σ hσ b a]
    linear_combination hsum
  have hc : (herm σ b a)⁻¹ + σ ((herm σ b a)⁻¹) = 0 := by
    have hσw : σ (herm σ b a) = -herm σ b a := by linear_combination hw
    rw [map_inv₀, hσw, inv_neg]
    ring
  have := (hb.move ha hc)
  rwa [inv_mul_cancel₀ hne, one_smul] at this

theorem eq_top_of_forall_isCenter (hσ : IsUnitaryInvolution σ) (hn : 2 ≤ n)
    (h3 : n = 3 → ∃ s : K, s ≠ 0 ∧ σ s * s ≠ 1)
    (h : ∀ a : Fin n → K, herm σ a a = 0 → IsCenter H a) : H = ⊤ := by
  rw [eq_top_iff, ← T_eq_top hσ hn h3]
  refine (Subgroup.closure_le H).2 ?_
  rintro g ⟨a, c, ha, hc, hg⟩
  obtain ⟨g₁, hg₁, hg₁a⟩ := (h a ha).2 c hc
  have : g = g₁ := ext_smul σ fun v => by rw [hg v, hg₁a v]
  rw [this]
  exact hg₁

theorem exists_mem_of_T {m : ℕ} (φ : (Fin m → K) →ₗ[K] (Fin n → K))
    (hφ : ∀ u v, herm σ (φ u) (φ v) = herm σ u v)
    (hH : ∀ c, herm σ c c = 0 → IsCenter H (φ c)) {t : SUid σ m} (ht : t ∈ T σ m) :
    ∃ g ∈ H, (∀ u, g • φ u = φ (t • u)) ∧
      ∀ v, (∀ u, herm σ (φ u) v = 0) → g • v = v := by
  induction ht using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨a, c, ha, hc, h⟩ := hg
    obtain ⟨g', hg', h'⟩ := (hH a ha).2 c hc
    refine ⟨g', hg', fun u => ?_, fun v hv => ?_⟩
    · rw [h', h, map_add, map_smul, hφ]
    · rw [h', hv, mul_zero, zero_smul, add_zero]
  | one => exact ⟨1, H.one_mem, fun u => by simp, fun v _ => by simp⟩
  | mul g h _ _ ihg ihh =>
    obtain ⟨g', hg', h1, h2⟩ := ihg
    obtain ⟨h', hh', h3, h4⟩ := ihh
    refine ⟨g' * h', H.mul_mem hg' hh', fun u => ?_, fun v hv => ?_⟩
    · rw [mul_smul, h3, h1, mul_smul]
    · rw [mul_smul, h4 v hv, h2 v hv]
  | inv g _ ihg =>
    obtain ⟨g', hg', h1, h2⟩ := ihg
    refine ⟨g'⁻¹, H.inv_mem hg', fun u => ?_, fun v hv => ?_⟩
    · rw [inv_smul_eq_iff, h1, smul_inv_smul]
    · rw [inv_smul_eq_iff, h2 v hv]

section Transitivity

variable {m : ℕ} {φ : (Fin m → K) →ₗ[K] (Fin n → K)}

theorem exists_mem_fix_of_iso (hσ : IsUnitaryInvolution σ) (hm : 3 ≤ m)
    (hφ : ∀ u v, herm σ (φ u) (φ v) = herm σ u v)
    (hH : ∀ c, herm σ c c = 0 → IsCenter H (φ c)) {c c' : Fin m → K} (hc0 : c ≠ 0)
    (hc : herm σ c c = 0) (hc0' : c' ≠ 0) (hc' : herm σ c' c' = 0) :
    ∃ g ∈ H, g • φ c = φ c' ∧ ∀ v, (∀ u, herm σ (φ u) v = 0) → g • v = v := by
  obtain ⟨t, ht, htc⟩ := exists_mem_T_smul_eq_of_iso hσ hm hc0 hc hc0' hc'
  obtain ⟨g, hg, hgφ, hgv⟩ := exists_mem_of_T φ hφ hH ht
  exact ⟨g, hg, by rw [hgφ, htc], hgv⟩

theorem exists_mem_fix_of_norm (hσ : IsUnitaryInvolution σ)
    (hm : 4 ≤ m ∨ (3 ≤ m ∧ ∃ s : K, s ≠ 0 ∧ σ s * s ≠ 1))
    (hφ : ∀ u v, herm σ (φ u) (φ v) = herm σ u v)
    (hH : ∀ c, herm σ c c = 0 → IsCenter H (φ c)) {c c' : Fin m → K} {s : K} (hs : s ≠ 0)
    (hc : herm σ c c = s) (hc' : herm σ c' c' = s) :
    ∃ g ∈ H, g • φ c = φ c' ∧ ∀ v, (∀ u, herm σ (φ u) v = 0) → g • v = v := by
  have hsfix : σ s = s := by rw [← hc]; exact herm_self_fixed σ hσ.invol c
  obtain ⟨l, hl⟩ := hσ.norm_surj s hsfix hs
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_mul] at hl
    exact hs hl.symm
  have hσl : σ l ≠ 0 := (map_ne_zero σ).mpr hl0
  have hu : herm σ (l⁻¹ • c) (l⁻¹ • c) = 1 := by
    rw [herm_smul_left, herm_smul_right, hc, map_inv₀, ← hl]
    field_simp
  have hu' : herm σ (l⁻¹ • c') (l⁻¹ • c') = 1 := by
    rw [herm_smul_left, herm_smul_right, hc', map_inv₀, ← hl]
    field_simp
  obtain ⟨t, ht, htu⟩ := exists_mem_T_smul_eq_of_norm_one hσ hm hu hu'
  obtain ⟨g, hg, hgφ, hgv⟩ := exists_mem_of_T φ hφ hH ht
  refine ⟨g, hg, ?_, hgv⟩
  have h1 : g • φ (l⁻¹ • c) = φ (l⁻¹ • c') := by rw [hgφ, htu]
  have h2 : g • φ c = l • (g • φ (l⁻¹ • c)) := by
    rw [map_smul, smul_comm g l⁻¹, smul_smul, mul_inv_cancel₀ hl0, one_smul]
  rw [h2, h1, ← map_smul, smul_smul, mul_inv_cancel₀ hl0, one_smul]

end Transitivity

section Blocks

theorem herm_sum_left {ι : Type*} (s : Finset ι) (f : ι → Fin n → K) (v : Fin n → K) :
    herm σ (∑ i ∈ s, f i) v = ∑ i ∈ s, herm σ (f i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, herm_add_left, ih]

theorem herm_sum_right {ι : Type*} (s : Finset ι) (v : Fin n → K) (f : ι → Fin n → K) :
    herm σ v (∑ i ∈ s, f i) = ∑ i ∈ s, herm σ v (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, herm_add_right, ih]

variable {m m₁ m₂ : ℕ}

@[expose] def orthoEmb (x : Fin m → Fin n → K) : (Fin m → K) →ₗ[K] (Fin n → K) where
  toFun c := ∑ i, c i • x i
  map_add' c d := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a c := by simp [Finset.smul_sum, smul_smul]

theorem orthoEmb_apply (x : Fin m → Fin n → K) (c : Fin m → K) :
    orthoEmb x c = ∑ i, c i • x i := rfl

theorem herm_orthoEmb_left (x : Fin m → Fin n → K) (c : Fin m → K) (v : Fin n → K) :
    herm σ (orthoEmb x c) v = ∑ i, σ (c i) * herm σ (x i) v := by
  rw [orthoEmb_apply, herm_sum_left]
  simp [herm_smul_left]

theorem herm_orthoEmb_right (x : Fin m → Fin n → K) (d : Fin m → K) (v : Fin n → K) :
    herm σ v (orthoEmb x d) = ∑ i, d i * herm σ v (x i) := by
  rw [orthoEmb_apply, herm_sum_right]
  simp [herm_smul_right]

theorem herm_orthoEmb {x : Fin m → Fin n → K}
    (hx : ∀ i j, herm σ (x i) (x j) = if i = j then 1 else 0) (c d : Fin m → K) :
    herm σ (orthoEmb x c) (orthoEmb x d) = herm σ c d := by
  rw [herm_orthoEmb_left]
  simp only [herm_orthoEmb_right, hx]
  rw [herm_def]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

theorem herm_orthoEmb_orth {x : Fin m₁ → Fin n → K} {y : Fin m₂ → Fin n → K}
    (hxy : ∀ i j, herm σ (x i) (y j) = 0) (c : Fin m₁ → K) (d : Fin m₂ → K) :
    herm σ (orthoEmb x c) (orthoEmb y d) = 0 := by
  rw [herm_orthoEmb_left]
  simp [herm_orthoEmb_right, hxy]

end Blocks

section Existence

variable {m : ℕ}

theorem exists_isotropic_ne_zero (hσ : IsUnitaryInvolution σ) (hm : 2 ≤ m) :
    ∃ a : Fin m → K, a ≠ 0 ∧ herm σ a a = 0 := by
  have hm0 : 0 < m := by omega
  set e : Fin m → K := Pi.single ⟨0, hm0⟩ 1 with he
  have hee : herm σ e e = 1 := by
    rw [he, herm_single_left]
    simp
  obtain ⟨z, hz, hez⟩ := exists_norm_one_perp hσ hm hee
  obtain ⟨μ, hμ⟩ := hσ.exists_norm_neg_one
  have hze : herm σ z e = 0 := herm_eq_zero_comm σ hσ.invol hez
  refine ⟨e + μ • z, ?_, ?_⟩
  · intro h0
    have : herm σ e (e + μ • z) = 1 := by
      rw [herm_add_right, herm_smul_right, hee, hez]
      ring
    rw [h0, herm_zero_right] at this
    exact zero_ne_one this
  · simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hee, hez, hze, hz]
    linear_combination hμ

theorem exists_isotropic_perp (hσ : IsUnitaryInvolution σ) (hm : 3 ≤ m) {z : Fin m → K}
    (hz : herm σ z z ≠ 0) : ∃ u : Fin m → K, u ≠ 0 ∧ herm σ u u = 0 ∧ herm σ z u = 0 := by
  obtain ⟨l, hl⟩ := exists_smul_norm_one hσ hz
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [zero_smul, herm_zero_left] at hl
    exact zero_ne_one hl
  set z' : Fin m → K := l • z with hz'
  obtain ⟨z₁, hz₁, hz'z₁⟩ := exists_norm_one_perp hσ (by omega) hl
  have hz₁z' : herm σ z₁ z' = 0 := herm_eq_zero_comm σ hσ.invol hz'z₁
  set P : (Fin m → K) →ₗ[K] (Fin m → K) :=
    LinearMap.id - (hermL σ z').smulRight z' - (hermL σ z₁).smulRight z₁ with hPdef
  have hPy : ∀ y, P y = y - herm σ z' y • z' - herm σ z₁ y • z₁ := fun y => rfl
  obtain ⟨y₀, hy₀⟩ := exists_aniso_of_lt hσ (k := 2) (by omega) ![z', z₁] P
    (fun y => by
      rw [hPy, show y - (y - herm σ z' y • z' - herm σ z₁ y • z₁) =
        herm σ z' y • z' + herm σ z₁ y • z₁ by abel]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)))
    (fun y j => by
      fin_cases j <;> simp [hPy, hl, hz₁, hz'z₁, hz₁z'])
  obtain ⟨c, hc⟩ := exists_smul_norm_one hσ hy₀
  set z₂ : Fin m → K := c • P y₀ with hz₂
  have hz'z₂ : herm σ z' z₂ = 0 := by simp [hz₂, hPy, hl, hz'z₁]
  have hz₁z₂ : herm σ z₁ z₂ = 0 := by simp [hz₂, hPy, hz₁, hz₁z']
  have hz₂z₁ : herm σ z₂ z₁ = 0 := herm_eq_zero_comm σ hσ.invol hz₁z₂
  obtain ⟨μ, hμ⟩ := hσ.exists_norm_neg_one
  have hz₂z₂ : herm σ z₂ z₂ = 1 := hc
  refine ⟨z₁ + μ • z₂, ?_, ?_, ?_⟩
  · intro h0
    have : herm σ z₁ (z₁ + μ • z₂) = 1 := by
      rw [herm_add_right, herm_smul_right, hz₁, hz₁z₂]
      ring
    rw [h0, herm_zero_right] at this
    exact zero_ne_one this
  · simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hz₁, hz₁z₂,
      hz₂z₁, hz₂z₂]
    linear_combination hμ
  · have h1 : herm σ z' (z₁ + μ • z₂) = 0 := by
      rw [herm_add_right, herm_smul_right, hz'z₁, hz'z₂]
      ring
    have h2 : herm σ z' (z₁ + μ • z₂) = σ l * herm σ z (z₁ + μ • z₂) := by
      rw [hz', herm_smul_left]
    rw [h1] at h2
    have hσl : σ l ≠ 0 := (map_ne_zero σ).mpr hl0
    exact (mul_eq_zero.mp h2.symm).resolve_left hσl

end Existence

section TwoBlocks

variable {m₁ m₂ : ℕ} {x : Fin m₁ → Fin n → K} {y : Fin m₂ → Fin n → K}

structure Blocks (σ : K ≃+* K) (H : Subgroup (SUid σ n)) (x : Fin m₁ → Fin n → K)
    (y : Fin m₂ → Fin n → K) : Prop where
  ortho_x : ∀ i j, herm σ (x i) (x j) = if i = j then 1 else 0
  ortho_y : ∀ i j, herm σ (y i) (y j) = if i = j then 1 else 0
  orth : ∀ i j, herm σ (x i) (y j) = 0
  dim_x : 4 ≤ m₁ ∨ (3 ≤ m₁ ∧ ∃ s : K, s ≠ 0 ∧ σ s * s ≠ 1)
  dim_y : 4 ≤ m₂ ∨ (3 ≤ m₂ ∧ ∃ s : K, s ≠ 0 ∧ σ s * s ≠ 1)
  center_x : ∀ c, herm σ c c = 0 → IsCenter H (orthoEmb x c)
  center_y : ∀ d, herm σ d d = 0 → IsCenter H (orthoEmb y d)

variable {H : Subgroup (SUid σ n)}

theorem herm_blockVec (hσ : IsUnitaryInvolution σ) (B : Blocks σ H x y) (c c' : Fin m₁ → K)
    (d d' : Fin m₂ → K) :
    herm σ (orthoEmb x c + orthoEmb y d) (orthoEmb x c' + orthoEmb y d') =
      herm σ c c' + herm σ d d' := by
  have h1 := herm_orthoEmb B.ortho_x c c'
  have h2 := herm_orthoEmb B.ortho_y d d'
  have h3 := herm_orthoEmb_orth B.orth c d'
  have h4 : herm σ (orthoEmb y d) (orthoEmb x c') = 0 :=
    herm_eq_zero_comm σ hσ.invol (herm_orthoEmb_orth B.orth c' d)
  simp only [herm_add_left, herm_add_right, h1, h2, h3, h4]
  ring

theorem dim_x_ge (B : Blocks σ H x y) : 3 ≤ m₁ := by
  rcases B.dim_x with h | ⟨h, _⟩ <;> omega

theorem dim_y_ge (B : Blocks σ H x y) : 3 ≤ m₂ := by
  rcases B.dim_y with h | ⟨h, _⟩ <;> omega

theorem exists_mem_move_x (hσ : IsUnitaryInvolution σ) (B : Blocks σ H x y)
    {c c' : Fin m₁ → K} (hc0 : c ≠ 0) (hc : herm σ c c = 0) (hc0' : c' ≠ 0)
    (hc' : herm σ c' c' = 0) (d : Fin m₂ → K) :
    ∃ g ∈ H, g • (orthoEmb x c + orthoEmb y d) = orthoEmb x c' + orthoEmb y d := by
  obtain ⟨g, hg, hgc, hgv⟩ := exists_mem_fix_of_iso hσ (dim_x_ge B) (herm_orthoEmb B.ortho_x)
    B.center_x hc0 hc hc0' hc'
  refine ⟨g, hg, ?_⟩
  rw [smul_add, hgc, hgv (orthoEmb y d) fun u => herm_orthoEmb_orth B.orth u d]

theorem exists_mem_move_y (hσ : IsUnitaryInvolution σ) (B : Blocks σ H x y)
    {d d' : Fin m₂ → K} (hd0 : d ≠ 0) (hd : herm σ d d = 0) (hd0' : d' ≠ 0)
    (hd' : herm σ d' d' = 0) (c : Fin m₁ → K) :
    ∃ g ∈ H, g • (orthoEmb x c + orthoEmb y d) = orthoEmb x c + orthoEmb y d' := by
  obtain ⟨g, hg, hgd, hgv⟩ := exists_mem_fix_of_iso hσ (dim_y_ge B) (herm_orthoEmb B.ortho_y)
    B.center_y hd0 hd hd0' hd'
  refine ⟨g, hg, ?_⟩
  rw [smul_add, hgd, hgv (orthoEmb x c) fun u =>
    herm_eq_zero_comm σ hσ.invol (herm_orthoEmb_orth B.orth c u)]

theorem exists_mem_moveN_x (hσ : IsUnitaryInvolution σ) (B : Blocks σ H x y)
    {c c' : Fin m₁ → K} {s : K} (hs : s ≠ 0) (hc : herm σ c c = s) (hc' : herm σ c' c' = s)
    (d : Fin m₂ → K) :
    ∃ g ∈ H, g • (orthoEmb x c + orthoEmb y d) = orthoEmb x c' + orthoEmb y d := by
  obtain ⟨g, hg, hgc, hgv⟩ := exists_mem_fix_of_norm hσ B.dim_x (herm_orthoEmb B.ortho_x)
    B.center_x hs hc hc'
  refine ⟨g, hg, ?_⟩
  rw [smul_add, hgc, hgv (orthoEmb y d) fun u => herm_orthoEmb_orth B.orth u d]

theorem exists_mem_moveN_y (hσ : IsUnitaryInvolution σ) (B : Blocks σ H x y)
    {d d' : Fin m₂ → K} {s : K} (hs : s ≠ 0) (hd : herm σ d d = s) (hd' : herm σ d' d' = s)
    (c : Fin m₁ → K) :
    ∃ g ∈ H, g • (orthoEmb x c + orthoEmb y d) = orthoEmb x c + orthoEmb y d' := by
  obtain ⟨g, hg, hgd, hgv⟩ := exists_mem_fix_of_norm hσ B.dim_y (herm_orthoEmb B.ortho_y)
    B.center_y hs hd hd'
  refine ⟨g, hg, ?_⟩
  rw [smul_add, hgd, hgv (orthoEmb x c) fun u =>
    herm_eq_zero_comm σ hσ.invol (herm_orthoEmb_orth B.orth c u)]

theorem isCenter_blockVec_type0 (hσ : IsUnitaryInvolution σ) (B : Blocks σ H x y)
    {c₀ : Fin m₁ → K} {d₀ : Fin m₂ → K} (hc₀ : c₀ ≠ 0) (hc₀i : herm σ c₀ c₀ = 0) (hd₀ : d₀ ≠ 0)
    (hd₀i : herm σ d₀ d₀ = 0) (hC : IsCenter H (orthoEmb x c₀ + orthoEmb y d₀))
    {c : Fin m₁ → K} {d : Fin m₂ → K} (hc : c ≠ 0) (hci : herm σ c c = 0) (hd : d ≠ 0)
    (hdi : herm σ d d = 0) : IsCenter H (orthoEmb x c + orthoEmb y d) := by
  obtain ⟨g₁, hg₁, h₁⟩ := exists_mem_move_x hσ B hc₀ hc₀i hc hci d₀
  obtain ⟨g₂, hg₂, h₂⟩ := exists_mem_move_y hσ B hd₀ hd₀i hd hdi c
  have h := (hC.map hg₁).map hg₂
  rwa [h₁, h₂] at h

theorem isCenter_blockVec_typeN (hσ : IsUnitaryInvolution σ) (B : Blocks σ H x y)
    {c₀ : Fin m₁ → K} {d₀ : Fin m₂ → K} (hs₀ : herm σ c₀ c₀ ≠ 0)
    (hC : IsCenter H (orthoEmb x c₀ + orthoEmb y d₀)) {c : Fin m₁ → K} {d : Fin m₂ → K}
    (hs : herm σ c c ≠ 0) (hd : herm σ d d = -herm σ c c) :
    IsCenter H (orthoEmb x c + orthoEmb y d) := by
  set s₀ := herm σ c₀ c₀ with hs₀def
  set s := herm σ c c with hsdef
  have hd₀ : herm σ d₀ d₀ = -s₀ := by
    have := hC.1
    rw [herm_blockVec hσ B] at this
    linear_combination this
  have hs₀fix : σ s₀ = s₀ := herm_self_fixed σ hσ.invol c₀
  have hsfix : σ s = s := herm_self_fixed σ hσ.invol c
  have hq : σ (s / s₀) = s / s₀ := by rw [map_div₀, hs₀fix, hsfix]
  obtain ⟨l, hl⟩ := hσ.norm_surj (s / s₀) hq (div_ne_zero hs hs₀)
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_mul] at hl
    exact div_ne_zero hs hs₀ hl.symm
  have hlC := hC.smul hσ.invol l
  have e1 : l • (orthoEmb x c₀ + orthoEmb y d₀) = orthoEmb x (l • c₀) + orthoEmb y (l • d₀) := by
    rw [smul_add, map_smul, map_smul]
  rw [e1] at hlC
  have hn1 : herm σ (l • c₀) (l • c₀) = s := by
    rw [herm_smul_left, herm_smul_right, ← mul_assoc, hl, ← hs₀def]
    field_simp
  have hn2 : herm σ (l • d₀) (l • d₀) = -s := by
    rw [herm_smul_left, herm_smul_right, ← mul_assoc, hl, hd₀]
    field_simp
  obtain ⟨g₁, hg₁, h₁⟩ := exists_mem_moveN_x hσ B hs hn1 rfl (l • d₀)
  have hd' : herm σ d d = -s := hd
  obtain ⟨g₂, hg₂, h₂⟩ := exists_mem_moveN_y hσ B (neg_ne_zero.mpr hs) hn2 hd' c
  have h := (hlC.map hg₁).map hg₂
  rwa [h₁, h₂] at h

theorem exists_typeN_of_type0 (hσ : IsUnitaryInvolution σ) (B : Blocks σ H x y)
    {c₀ : Fin m₁ → K} {d₀ : Fin m₂ → K} (hc₀ : c₀ ≠ 0) (hc₀i : herm σ c₀ c₀ = 0) (hd₀ : d₀ ≠ 0)
    (hd₀i : herm σ d₀ d₀ = 0) (hC : IsCenter H (orthoEmb x c₀ + orthoEmb y d₀)) :
    ∃ (c : Fin m₁ → K) (d : Fin m₂ → K), herm σ c c ≠ 0 ∧
      IsCenter H (orthoEmb x c + orthoEmb y d) := by
  obtain ⟨f₁, hf₁i, hf₁⟩ := exists_partner hσ hc₀ hc₀i
  obtain ⟨f₂, hf₂i, hf₂⟩ := exists_partner hσ hd₀ hd₀i
  obtain ⟨ρ, hρ⟩ := hσ.exists_ne
  obtain ⟨τ, hτ0, hτ⟩ := hσ.exists_traceZero
  have hρ0 : ρ ≠ 0 := fun h => hρ (by rw [h, map_zero])
  have hf₁0 : f₁ ≠ 0 := by
    intro h0
    rw [h0, herm_zero_right] at hf₁
    exact zero_ne_one hf₁
  have hf₂0 : f₂ ≠ 0 := by
    intro h0
    rw [h0, herm_zero_right] at hf₂
    exact zero_ne_one hf₂
  have hρf₂i : herm σ (ρ • f₂) (ρ • f₂) = 0 := by
    rw [herm_smul_left, herm_smul_right, hf₂i]
    ring
  have hρf₂0 : ρ • f₂ ≠ 0 := smul_ne_zero hρ0 hf₂0
  have hb : IsCenter H (orthoEmb x f₁ + orthoEmb y (ρ • f₂)) :=
    isCenter_blockVec_type0 hσ B hc₀ hc₀i hd₀ hd₀i hC hf₁0 hf₁i hρf₂0 hρf₂i
  have hmv := hb.move hC hτ
  have hf₁c : herm σ f₁ c₀ = 1 := by rw [herm_conj σ hσ.invol, hf₁, map_one]
  have hf₂d : herm σ f₂ d₀ = 1 := by rw [herm_conj σ hσ.invol, hf₂, map_one]
  have hw : herm σ (orthoEmb x f₁ + orthoEmb y (ρ • f₂)) (orthoEmb x c₀ + orthoEmb y d₀) =
      1 + σ ρ := by
    rw [herm_blockVec hσ B, hf₁c, herm_smul_left, hf₂d]
    ring
  rw [hw] at hmv
  set z : K := τ * (1 + σ ρ) with hz
  have hV : orthoEmb x c₀ + orthoEmb y d₀ + z • (orthoEmb x f₁ + orthoEmb y (ρ • f₂)) =
      orthoEmb x (c₀ + z • f₁) + orthoEmb y (d₀ + z • (ρ • f₂)) := by
    simp only [map_add, map_smul, smul_add]
    abel
  rw [hV] at hmv
  refine ⟨c₀ + z • f₁, d₀ + z • (ρ • f₂), ?_, hmv⟩
  have hn : herm σ (c₀ + z • f₁) (c₀ + z • f₁) = z + σ z := by
    simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hc₀i, hf₁i,
      hf₁, hf₁c]
    ring
  have hστ : σ τ = -τ := by linear_combination hτ
  have hz2 : z + σ z = τ * (σ ρ - ρ) := by
    rw [hz, map_mul, map_add, map_one, hσ.invol, hστ]
    ring
  rw [hn, hz2]
  exact mul_ne_zero hτ0 (sub_ne_zero.mpr hρ)

theorem exists_type0_of_typeN (hσ : IsUnitaryInvolution σ) (B : Blocks σ H x y)
    {c₀ : Fin m₁ → K} {d₀ : Fin m₂ → K} (hs : herm σ c₀ c₀ ≠ 0)
    (hC : IsCenter H (orthoEmb x c₀ + orthoEmb y d₀)) :
    ∃ (u₁ : Fin m₁ → K) (u₂ : Fin m₂ → K), u₁ ≠ 0 ∧ herm σ u₁ u₁ = 0 ∧ u₂ ≠ 0 ∧
      herm σ u₂ u₂ = 0 ∧ IsCenter H (orthoEmb x u₁ + orthoEmb y u₂) := by
  have hc₀0 : c₀ ≠ 0 := fun h0 => hs (by rw [h0]; simp)
  set s := herm σ c₀ c₀ with hsdef
  have hd₀ : herm σ d₀ d₀ = -s := by
    have := hC.1
    rw [herm_blockVec hσ B] at this
    linear_combination this
  have hd₀s : herm σ d₀ d₀ ≠ 0 := by rw [hd₀]; exact neg_ne_zero.mpr hs
  obtain ⟨τ, hτ0, hτ⟩ := hσ.exists_traceZero
  have hστ : σ τ = -τ := by linear_combination hτ
  obtain ⟨a₀, ha₀0, ha₀⟩ := exists_isotropic_ne_zero hσ (by have := dim_x_ge B; omega :
    2 ≤ m₁)
  obtain ⟨w, hwi, -, hcw⟩ := exists_cno hσ ha₀0 ha₀ hc₀0
  set l : K := τ / herm σ c₀ w with hl
  have hl0 : l ≠ 0 := div_ne_zero hτ0 hcw
  set u₁ : Fin m₁ → K := l • w with hu₁
  have hu₁i : herm σ u₁ u₁ = 0 := by
    rw [hu₁, herm_smul_left, herm_smul_right, hwi]
    ring
  have hcu₁ : herm σ c₀ u₁ = τ := by
    rw [hu₁, herm_smul_right, hl]
    field_simp
  have hu₁0 : u₁ ≠ 0 := by
    intro h0
    rw [h0, herm_zero_right] at hcu₁
    exact hτ0 hcu₁.symm
  obtain ⟨u₂, hu₂0, hu₂i, hdu₂⟩ := exists_isotropic_perp hσ (dim_y_ge B) hd₀s
  have hu₁c : herm σ u₁ c₀ = σ τ := by rw [herm_conj σ hσ.invol, hcu₁]
  have hu₂d : herm σ u₂ d₀ = 0 := herm_eq_zero_comm σ hσ.invol hdu₂
  have hn₁ : herm σ (c₀ + u₁) (c₀ + u₁) = s := by
    simp only [herm_add_left, herm_add_right, hu₁i, hcu₁, hu₁c, hστ, ← hsdef]
    ring
  have hn₂ : herm σ (d₀ + u₂) (d₀ + u₂) = -s := by
    simp only [herm_add_left, herm_add_right, hu₂i, hdu₂, hu₂d, hd₀]
    ring
  obtain ⟨g₁, hg₁, h₁⟩ := exists_mem_moveN_x hσ B hs rfl hn₁ d₀
  obtain ⟨g₂, hg₂, h₂⟩ := exists_mem_moveN_y hσ B (neg_ne_zero.mpr hs) hd₀ hn₂ (c₀ + u₁)
  have hyC := (hC.map hg₁).map hg₂
  rw [h₁, h₂] at hyC
  set y' : Fin n → K := orthoEmb x (c₀ + u₁) + orthoEmb y (d₀ + u₂) with hy'
  have hnyC := hyC.smul hσ.invol (-1)
  set a : Fin n → K := orthoEmb x c₀ + orthoEmb y d₀ with ha
  have hsub : a + (-1 : K) • y' = (-1 : K) • (orthoEmb x u₁ + orthoEmb y u₂) := by
    simp only [ha, hy', map_add, neg_smul, one_smul]
    abel
  have hab : herm σ (a + (-1 : K) • y') (a + (-1 : K) • y') = 0 := by
    rw [hsub, herm_smul_left, herm_smul_right, herm_blockVec hσ B, hu₁i, hu₂i]
    ring
  have hne : herm σ ((-1 : K) • y') a ≠ 0 := by
    have h1 : herm σ y' a = -τ := by
      rw [hy', ha, herm_blockVec hσ B]
      simp only [herm_add_left, hu₁c, hu₂d, hd₀, ← hsdef, hστ]
      ring
    rw [herm_smul_left, h1, map_neg, map_one]
    simpa using hτ0
  have hsum := IsCenter.add hσ.invol hC hnyC hab hne
  rw [hsub] at hsum
  have := hsum.smul hσ.invol (-1)
  rw [smul_smul, show ((-1 : K) * -1) = 1 by ring, one_smul] at this
  exact ⟨u₁, u₂, hu₁0, hu₁i, hu₂0, hu₂i, this⟩

theorem isCenter_blockVec_of_mixed (hσ : IsUnitaryInvolution σ) (B : Blocks σ H x y)
    (hmix : ∃ (c : Fin m₁ → K) (d : Fin m₂ → K), c ≠ 0 ∧ d ≠ 0 ∧
      IsCenter H (orthoEmb x c + orthoEmb y d))
    (c : Fin m₁ → K) (d : Fin m₂ → K)
    (hiso : herm σ (orthoEmb x c + orthoEmb y d) (orthoEmb x c + orthoEmb y d) = 0) :
    IsCenter H (orthoEmb x c + orthoEmb y d) := by
  obtain ⟨c₀, d₀, hc₀, hd₀, hC⟩ := hmix
  have key : (∃ (u₁ : Fin m₁ → K) (u₂ : Fin m₂ → K), u₁ ≠ 0 ∧ herm σ u₁ u₁ = 0 ∧ u₂ ≠ 0 ∧
      herm σ u₂ u₂ = 0 ∧ IsCenter H (orthoEmb x u₁ + orthoEmb y u₂)) ∧
      (∃ (c₁ : Fin m₁ → K) (d₁ : Fin m₂ → K), herm σ c₁ c₁ ≠ 0 ∧
        IsCenter H (orthoEmb x c₁ + orthoEmb y d₁)) := by
    by_cases h0 : herm σ c₀ c₀ = 0
    · have hd0 : herm σ d₀ d₀ = 0 := by
        have := hC.1
        rw [herm_blockVec hσ B, h0, zero_add] at this
        exact this
      exact ⟨⟨c₀, d₀, hc₀, h0, hd₀, hd0, hC⟩, exists_typeN_of_type0 hσ B hc₀ h0 hd₀ hd0 hC⟩
    · exact ⟨exists_type0_of_typeN hσ B h0 hC, ⟨c₀, d₀, h0, hC⟩⟩
  obtain ⟨⟨u₁, u₂, hu₁, hu₁i, hu₂, hu₂i, hU⟩, ⟨c₁, d₁, hc₁, hD⟩⟩ := key
  have hcd : herm σ c c + herm σ d d = 0 := by
    rw [herm_blockVec hσ B] at hiso
    exact hiso
  by_cases hc : c = 0
  · subst hc
    have hd : herm σ d d = 0 := by simpa using hcd
    simpa using B.center_y d hd
  by_cases hd : d = 0
  · subst hd
    have hc' : herm σ c c = 0 := by simpa using hcd
    simpa using B.center_x c hc'
  by_cases hs : herm σ c c = 0
  · have hd' : herm σ d d = 0 := by
      rw [hs, zero_add] at hcd
      exact hcd
    exact isCenter_blockVec_type0 hσ B hu₁ hu₁i hu₂ hu₂i hU hc hs hd hd'
  · exact isCenter_blockVec_typeN hσ B hc₁ hD hs (by linear_combination hcd)

end TwoBlocks

section Subspaces

variable {H : Subgroup (SUid σ n)}

@[expose] def HasONBasis (σ : K ≃+* K) (W : Submodule K (Fin n → K)) : Prop :=
  ∃ (m : ℕ) (x : Fin m → Fin n → K), (∀ i j, herm σ (x i) (x j) = if i = j then 1 else 0) ∧
    Submodule.span K (Set.range x) = W ∧
      (4 ≤ m ∨ (3 ≤ m ∧ ∃ s : K, s ≠ 0 ∧ σ s * s ≠ 1))

@[expose] def AllCenters (H : Subgroup (SUid σ n)) (W : Submodule K (Fin n → K)) : Prop :=
  ∀ v ∈ W, herm σ v v = 0 → IsCenter H v

theorem mem_span_range_iff {m : ℕ} (x : Fin m → Fin n → K) (v : Fin n → K) :
    v ∈ Submodule.span K (Set.range x) ↔ ∃ c : Fin m → K, orthoEmb x c = v := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  rfl

theorem orthoEmb_mem_span {m : ℕ} (x : Fin m → Fin n → K) (c : Fin m → K) :
    orthoEmb x c ∈ Submodule.span K (Set.range x) :=
  (mem_span_range_iff x _).2 ⟨c, rfl⟩

theorem castAdd_ne_natAdd' {m₁ m₂ : ℕ} (a : Fin m₁) (b : Fin m₂) :
    Fin.castAdd m₂ a ≠ Fin.natAdd m₁ b := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at this
  have := a.isLt
  omega

theorem HasONBasis.sup (hσ : ∀ c, σ (σ c) = c) {W₁ W₂ : Submodule K (Fin n → K)}
    (h₁ : HasONBasis σ W₁) (h₂ : HasONBasis σ W₂)
    (horth : ∀ u ∈ W₁, ∀ v ∈ W₂, herm σ u v = 0) : HasONBasis σ (W₁ ⊔ W₂) := by
  obtain ⟨m₁, x, hx, hxW, hm₁⟩ := h₁
  obtain ⟨m₂, y, hy, hyW, -⟩ := h₂
  have hxy : ∀ i j, herm σ (x i) (y j) = 0 := fun i j =>
    horth _ (hxW ▸ Submodule.subset_span ⟨i, rfl⟩) _ (hyW ▸ Submodule.subset_span ⟨j, rfl⟩)
  have hyx : ∀ i j, herm σ (y i) (x j) = 0 := fun i j => herm_eq_zero_comm σ hσ (hxy j i)
  refine ⟨m₁ + m₂, Fin.append x y, ?_, ?_, ?_⟩
  · intro i j
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i <;>
      refine Fin.addCases (fun a' => ?_) (fun b' => ?_) j
    · simp [Fin.append_left, hx, Fin.castAdd_inj]
    · simp [Fin.append_left, Fin.append_right, hxy, castAdd_ne_natAdd' a b']
    · simp [Fin.append_left, Fin.append_right, hyx, (castAdd_ne_natAdd' a' b).symm]
    · simp [Fin.append_right, hy, Fin.natAdd_inj]
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      refine Fin.addCases (fun a => ?_) (fun b => ?_) i
      · rw [Fin.append_left]
        exact Submodule.mem_sup_left (hxW ▸ Submodule.subset_span ⟨a, rfl⟩)
      · rw [Fin.append_right]
        exact Submodule.mem_sup_right (hyW ▸ Submodule.subset_span ⟨b, rfl⟩)
    · refine sup_le ?_ ?_
      · rw [← hxW, Submodule.span_le]
        rintro _ ⟨a, rfl⟩
        exact Submodule.subset_span ⟨Fin.castAdd m₂ a, Fin.append_left x y a⟩
      · rw [← hyW, Submodule.span_le]
        rintro _ ⟨b, rfl⟩
        exact Submodule.subset_span ⟨Fin.natAdd m₁ b, Fin.append_right x y b⟩
  · rcases hm₁ with h | ⟨h, hs⟩
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by omega, hs⟩

theorem AllCenters.sup (hσ : IsUnitaryInvolution σ) {W₁ W₂ : Submodule K (Fin n → K)}
    (h₁ : HasONBasis σ W₁) (h₂ : HasONBasis σ W₂)
    (horth : ∀ u ∈ W₁, ∀ v ∈ W₂, herm σ u v = 0) (hA₁ : AllCenters H W₁)
    (hA₂ : AllCenters H W₂)
    (hmix : ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, w₁ ≠ 0 ∧ w₂ ≠ 0 ∧ IsCenter H (w₁ + w₂)) :
    AllCenters H (W₁ ⊔ W₂) := by
  obtain ⟨m₁, x, hx, hxW, hm₁⟩ := h₁
  obtain ⟨m₂, y, hy, hyW, hm₂⟩ := h₂
  have hxy : ∀ i j, herm σ (x i) (y j) = 0 := fun i j =>
    horth _ (hxW ▸ Submodule.subset_span ⟨i, rfl⟩) _ (hyW ▸ Submodule.subset_span ⟨j, rfl⟩)
  have hB : Blocks σ H x y :=
    { ortho_x := hx
      ortho_y := hy
      orth := hxy
      dim_x := hm₁
      dim_y := hm₂
      center_x := fun c hc => hA₁ _ (hxW ▸ orthoEmb_mem_span x c)
        (by rw [herm_orthoEmb hx]; exact hc)
      center_y := fun d hd => hA₂ _ (hyW ▸ orthoEmb_mem_span y d)
        (by rw [herm_orthoEmb hy]; exact hd) }
  obtain ⟨w₁, hw₁, w₂, hw₂, hw₁0, hw₂0, hC⟩ := hmix
  obtain ⟨c₀, rfl⟩ := (mem_span_range_iff x w₁).1 (hxW ▸ hw₁)
  obtain ⟨d₀, rfl⟩ := (mem_span_range_iff y w₂).1 (hyW ▸ hw₂)
  have hmix' : ∃ (c : Fin m₁ → K) (d : Fin m₂ → K), c ≠ 0 ∧ d ≠ 0 ∧
      IsCenter H (orthoEmb x c + orthoEmb y d) :=
    ⟨c₀, d₀, fun h0 => hw₁0 (by rw [h0, map_zero]), fun h0 => hw₂0 (by rw [h0, map_zero]), hC⟩
  intro v hv hvi
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.1 hv
  obtain ⟨c, rfl⟩ := (mem_span_range_iff x u₁).1 (hxW ▸ hu₁)
  obtain ⟨d, rfl⟩ := (mem_span_range_iff y u₂).1 (hyW ▸ hu₂)
  exact isCenter_blockVec_of_mixed hσ hB hmix' c d hvi

theorem allCenters_iSup (hσ : IsUnitaryInvolution σ) {ι : Type*} [DecidableEq ι]
    (W : ι → Submodule K (Fin n → K)) (hON : ∀ i, HasONBasis σ (W i))
    (horth : ∀ i j, i ≠ j → ∀ u ∈ W i, ∀ v ∈ W j, herm σ u v = 0)
    (hA : ∀ i, AllCenters H (W i))
    (hmix : ∀ i j, i ≠ j → ∃ w₁ ∈ W i, ∃ w₂ ∈ W j, w₁ ≠ 0 ∧ w₂ ≠ 0 ∧ IsCenter H (w₁ + w₂))
    (S : Finset ι) (hS : S.Nonempty) :
    HasONBasis σ (⨆ i ∈ S, W i) ∧ AllCenters H (⨆ i ∈ S, W i) := by
  induction S using Finset.induction_on with
  | empty => exact absurd hS (by simp)
  | insert j S hj ih =>
    rw [Finset.iSup_insert]
    by_cases hSe : S = ∅
    · subst hSe
      simp only [Finset.notMem_empty, iSup_false, iSup_bot, sup_bot_eq]
      exact ⟨hON j, hA j⟩
    · obtain ⟨hON', hA'⟩ := ih (Finset.nonempty_iff_ne_empty.mpr hSe)
      obtain ⟨i₀, hi₀⟩ := Finset.nonempty_iff_ne_empty.mpr hSe
      have horth' : ∀ u ∈ ⨆ i ∈ S, W i, ∀ v ∈ W j, herm σ u v = 0 := by
        intro u hu v hv
        have hle : (⨆ i ∈ S, W i) ≤ LinearMap.ker (hermL σ v) :=
          iSup₂_le fun i hi u' hu' => by
            have hij : j ≠ i := fun h => hj (h ▸ hi)
            simpa using horth j i hij v hv u' hu'
        have := hle hu
        rw [LinearMap.mem_ker, hermL_apply] at this
        exact herm_eq_zero_comm σ hσ.invol this
      have hmixX : ∃ w₁ ∈ ⨆ i ∈ S, W i, ∃ w₂ ∈ W j, w₁ ≠ 0 ∧ w₂ ≠ 0 ∧
          IsCenter H (w₁ + w₂) := by
        obtain ⟨w₁, hw₁, w₂, hw₂, h1, h2, hC⟩ := hmix i₀ j (fun h => hj (h ▸ hi₀))
        exact ⟨w₁, Submodule.mem_iSup_of_mem i₀ (Submodule.mem_iSup_of_mem hi₀ hw₁), w₂, hw₂,
          h1, h2, hC⟩
      rw [sup_comm]
      exact ⟨hON'.sup hσ.invol (hON j) horth',
        AllCenters.sup hσ hON' (hON j) horth' hA' (hA j) hmixX⟩

theorem eq_top_of_blocks (hσ : IsUnitaryInvolution σ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (hn : 4 ≤ n) (W : ι → Submodule K (Fin n → K)) (hON : ∀ i, HasONBasis σ (W i))
    (horth : ∀ i j, i ≠ j → ∀ u ∈ W i, ∀ v ∈ W j, herm σ u v = 0)
    (hA : ∀ i, AllCenters H (W i))
    (hmix : ∀ i j, i ≠ j → ∃ w₁ ∈ W i, ∃ w₂ ∈ W j, w₁ ≠ 0 ∧ w₂ ≠ 0 ∧ IsCenter H (w₁ + w₂))
    (htop : ⨆ i, W i = ⊤) : H = ⊤ := by
  have hall := (allCenters_iSup hσ W hON horth hA hmix Finset.univ Finset.univ_nonempty).2
  simp only [Finset.mem_univ, iSup_pos] at hall
  rw [htop] at hall
  exact eq_top_of_forall_isCenter hσ (by omega) (fun h => by omega)
    fun a ha => hall a Submodule.mem_top ha

end Subspaces

end CFSG.LieType.SeitzGeneration.Centers
