module

public import CFSG.ClassicalGroups.Unitary.Base
public import CFSG.ClassicalGroups.Unitary.Transport

public section

namespace CFSG.ClassicalGroups.Unitary

open Matrix CFSG.LieType.Universal.Unitary

variable {K : Type*} [Field K] {σ : K ≃+* K} {n : ℕ}

theorem exists_mem_T_smul_of_traceZero (hσ : ∀ c, σ (σ c) = c) {a a' : Fin n → K}
    (ha : herm σ a a = 0) (ha' : herm σ a' a' = 0) (hs0 : herm σ a a' ≠ 0)
    (hs : herm σ a a' + σ (herm σ a a') = 0) : ∃ t ∈ T σ n, t • a = a' := by
  have hσs : σ (herm σ a a') = -herm σ a a' := by linear_combination hs
  have hc : -(herm σ a a')⁻¹ + σ (-(herm σ a a')⁻¹) = 0 := by
    rw [map_neg, map_inv₀, hσs, inv_neg]
    ring
  refine ⟨tv hσ ha hc * tv hσ ha' hc,
    (T σ n).mul_mem (tv_mem_T hσ ha hc) (tv_mem_T hσ ha' hc), ?_⟩
  have hsa : herm σ a' a = σ (herm σ a a') := herm_conj σ hσ a a'
  rw [mul_smul, tv_smul, tv_smul]
  simp only [herm_add_right, herm_smul_right, ha, hsa, hσs]
  match_scalars
  all_goals field_simp
  all_goals ring

theorem exists_mem_T_smul_eq_smul (hσ : IsUnitaryInvolution σ) (hn : 3 ≤ n) {a : Fin n → K}
    (ha0 : a ≠ 0) (ha : herm σ a a = 0) {l : K} (hl : l ≠ 0) :
    ∃ t ∈ T σ n, t • a = l • a := by
  obtain ⟨f, hf, haf⟩ := exists_partner hσ ha0 ha
  obtain ⟨z, hz, haz, hfz⟩ := exists_norm_one_perp_pair hσ hn ha hf haf
  obtain ⟨τ, hτ0, hτ⟩ := hσ.exists_traceZero
  have hστ : σ τ = -τ := by linear_combination hτ
  have hfa : herm σ f a = 1 := by rw [herm_conj σ hσ.invol, haf, map_one]
  have hza : herm σ z a = 0 := herm_eq_zero_comm σ hσ.invol haz
  have hzf : herm σ z f = 0 := herm_eq_zero_comm σ hσ.invol hfz
  set γ := τ / σ l with hγ
  obtain ⟨μ, hμ⟩ := hσ.exists_norm (d := -(γ + σ γ)) (by rw [map_neg, hσ.trace_fixed])
  set c := a + γ • f + μ • z with hc
  have hcc : herm σ c c = 0 := by
    rw [hc]
    simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, ha, hf, haf,
      hfa, hz, haz, hfz, hza, hzf]
    linear_combination hμ
  have hac : herm σ a c = γ := by
    rw [hc]
    simp only [herm_add_right, herm_smul_right, ha, haf, haz]
    ring
  have hfc : herm σ f c = 1 := by
    rw [hc]
    simp only [herm_add_right, herm_smul_right, hfa, hf, hfz]
    ring
  have hl' : σ l ≠ 0 := (map_ne_zero σ).mpr hl
  have hτf : herm σ (τ • f) (τ • f) = 0 := by
    rw [herm_smul_left, herm_smul_right, hf]; ring
  have hla : herm σ (l • a) (l • a) = 0 := by
    rw [herm_smul_left, herm_smul_right, ha]; ring
  have h1 : herm σ a (τ • f) = τ := by rw [herm_smul_right, haf, mul_one]
  have h2 : herm σ (τ • f) c = -τ := by rw [herm_smul_left, hfc, hστ, mul_one]
  have h3 : herm σ c (l • a) = -τ := by
    rw [herm_smul_right, herm_conj σ hσ.invol, hac, hγ, map_div₀, hστ, hσ.invol]
    field_simp
  have hnτ : -τ + σ (-τ) = 0 := by rw [map_neg]; linear_combination -hτ
  obtain ⟨t1, ht1, ht1a⟩ := exists_mem_T_smul_of_traceZero hσ.invol ha hτf
    (by rw [h1]; exact hτ0) (by rw [h1]; exact hτ)
  obtain ⟨t2, ht2, ht2a⟩ := exists_mem_T_smul_of_traceZero hσ.invol hτf hcc
    (by rw [h2]; exact neg_ne_zero.mpr hτ0) (by rw [h2]; exact hnτ)
  obtain ⟨t3, ht3, ht3a⟩ := exists_mem_T_smul_of_traceZero hσ.invol hcc hla
    (by rw [h3]; exact neg_ne_zero.mpr hτ0) (by rw [h3]; exact hnτ)
  refine ⟨t3 * t2 * t1, (T σ n).mul_mem ((T σ n).mul_mem ht3 ht2) ht1, ?_⟩
  rw [mul_smul, mul_smul, ht1a, ht2a, ht3a]

theorem exists_mem_T_smul_eq_of_herm_ne_zero (hσ : IsUnitaryInvolution σ) (hn : 3 ≤ n)
    {a a' : Fin n → K} (ha : herm σ a a = 0) (ha0' : a' ≠ 0) (ha' : herm σ a' a' = 0)
    (hs : herm σ a a' ≠ 0) : ∃ t ∈ T σ n, t • a = a' := by
  obtain ⟨τ, hτ0, hτ⟩ := hσ.exists_traceZero
  set s := herm σ a a' with hsdef
  have hb : herm σ ((τ / s) • a') ((τ / s) • a') = 0 := by
    rw [herm_smul_left, herm_smul_right, ha']; ring
  have hab : herm σ a ((τ / s) • a') = τ := by
    rw [herm_smul_right, ← hsdef]; field_simp
  obtain ⟨t1, ht1, ht1a⟩ := exists_mem_T_smul_of_traceZero hσ.invol ha hb
    (by rw [hab]; exact hτ0) (by rw [hab]; exact hτ)
  have hb0 : (τ / s) • a' ≠ 0 := smul_ne_zero (div_ne_zero hτ0 hs) ha0'
  obtain ⟨t2, ht2, ht2a⟩ := exists_mem_T_smul_eq_smul hσ hn hb0 hb
    (l := s / τ) (div_ne_zero hs hτ0)
  refine ⟨t2 * t1, (T σ n).mul_mem ht2 ht1, ?_⟩
  rw [mul_smul, ht1a, ht2a, smul_smul, div_mul_div_cancel₀ hτ0, div_self hs, one_smul]

theorem exists_mem_T_smul_eq_of_iso (hσ : IsUnitaryInvolution σ) (hn : 3 ≤ n)
    {a a' : Fin n → K} (ha0 : a ≠ 0) (ha : herm σ a a = 0) (ha0' : a' ≠ 0)
    (ha' : herm σ a' a' = 0) : ∃ t ∈ T σ n, t • a = a' := by
  by_cases hs : herm σ a a' = 0
  · obtain ⟨d, hd, had, ha'd⟩ := exists_cno hσ ha0 ha ha0'
    have hd0 : d ≠ 0 := by
      rintro rfl
      exact had (herm_zero_right σ a)
    obtain ⟨t1, ht1, ht1a⟩ := exists_mem_T_smul_eq_of_herm_ne_zero hσ hn ha hd0 hd had
    obtain ⟨t2, ht2, ht2a⟩ := exists_mem_T_smul_eq_of_herm_ne_zero hσ hn ha' hd0 hd ha'd
    refine ⟨t2⁻¹ * t1, (T σ n).mul_mem ((T σ n).inv_mem ht2) ht1, ?_⟩
    rw [mul_smul, ht1a, inv_smul_eq_iff, ht2a]
  · exact exists_mem_T_smul_eq_of_herm_ne_zero hσ hn ha ha0' ha' hs

@[expose] def pairL (x z : Fin n → K) : (Fin 2 → K) →ₗ[K] (Fin n → K) where
  toFun c := c 0 • x + c 1 • z
  map_add' c d := by simp only [Pi.add_apply, add_smul]; abel
  map_smul' c d := by simp only [Pi.smul_apply, smul_eq_mul, mul_smul, smul_add]; rfl

theorem herm_fin_two (x y : Fin 2 → K) : herm σ x y = σ (x 0) * y 0 + σ (x 1) * y 1 := by
  simp [herm, Fin.sum_univ_two]

@[expose] noncomputable def su2 (hσ : ∀ c, σ (σ c) = c) {α β : K}
    (h : σ α * α + σ β * β = 1) : SUid σ 2 :=
  mkSU σ !![α, -σ β; β, σ α] (by rw [det_fin_two_of]; linear_combination h) (fun x y => by
    simp only [herm_fin_two, mulVec, dotProduct, Fin.sum_univ_two, cons_val_zero, cons_val_one,
      of_apply, cons_val', empty_val', cons_val_fin_one, map_add, map_mul, map_neg, hσ]
    linear_combination (σ (x 0) * y 0 + σ (x 1) * y 1) * h)

theorem su2_smul_single (hσ : ∀ c, σ (σ c) = c) {α β : K} (h : σ α * α + σ β * β = 1) :
    su2 hσ h • (Pi.single 0 1 : Fin 2 → K) = ![α, β] := by
  rw [su2, mkSU_smul]
  funext i
  fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two]

theorem exists_mem_T_of_orthonormal (hσ : IsUnitaryInvolution σ) {x z : Fin n → K}
    (hx : herm σ x x = 1) (hz : herm σ z z = 1) (hxz : herm σ x z = 0) (α β : K)
    (hy : herm σ (α • x + β • z) (α • x + β • z) = 1) :
    ∃ t ∈ T σ n, t • x = α • x + β • z := by
  have hzx : herm σ z x = 0 := herm_eq_zero_comm σ hσ.invol hxz
  have hN : σ α * α + σ β * β = 1 := by
    simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hx, hz, hxz,
      hzx] at hy
    linear_combination hy
  have hφ : ∀ c d : Fin 2 → K, herm σ (pairL x z c) (pairL x z d) = herm σ c d := by
    intro c d
    simp only [pairL, LinearMap.coe_mk, AddHom.coe_mk, herm_add_left, herm_add_right,
      herm_smul_left, herm_smul_right, hx, hz, hxz, hzx, herm_fin_two]
    ring
  have hA : su2 hσ.invol hN ∈ T σ 2 := by
    rw [T_two_eq_top hσ]
    exact Subgroup.mem_top _
  obtain ⟨g, hg, hgφ, -⟩ := transport hσ.invol (pairL x z) hφ hA
  refine ⟨g, hg, ?_⟩
  have hx' : pairL x z (Pi.single 0 1) = x := by simp [pairL]
  rw [← hx', hgφ, su2_smul_single]
  simp [pairL]

theorem herm_sub_proj (hσ : ∀ c, σ (σ c) = c) {z : Fin n → K} (hz : herm σ z z = 1)
    (y : Fin n → K) :
    herm σ (y - herm σ z y • z) (y - herm σ z y • z) =
      herm σ y y - σ (herm σ z y) * herm σ z y := by
  simp only [herm_sub_left, herm_sub_right, herm_smul_left, herm_smul_right, hz]
  rw [herm_conj σ hσ z y]
  ring

theorem exists_mem_T_of_aniso_diff (hσ : IsUnitaryInvolution σ) {x y : Fin n → K}
    (hx : herm σ x x = 1) (hy : herm σ y y = 1)
    (hr : herm σ (y - herm σ x y • x) (y - herm σ x y • x) ≠ 0) :
    ∃ t ∈ T σ n, t • x = y := by
  obtain ⟨c, hc⟩ := exists_smul_norm_one hσ hr
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul, herm_zero_left] at hc
    exact zero_ne_one hc
  have hxr : herm σ x (c • (y - herm σ x y • x)) = 0 := by
    simp [hx]
  have heq : herm σ x y • x + c⁻¹ • (c • (y - herm σ x y • x)) = y := by
    rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
    abel
  obtain ⟨t, ht, htx⟩ := exists_mem_T_of_orthonormal hσ hx hc hxr (herm σ x y) c⁻¹
    (by rw [heq]; exact hy)
  exact ⟨t, ht, by rw [htx, heq]⟩

theorem exists_mem_T_smul_eq_of_norm_one (hσ : IsUnitaryInvolution σ)
    (hn : 4 ≤ n ∨ (3 ≤ n ∧ ∃ s : K, s ≠ 0 ∧ σ s * s ≠ 1)) {x y : Fin n → K}
    (hx : herm σ x x = 1) (hy : herm σ y y = 1) : ∃ t ∈ T σ n, t • x = y := by
  have hn2 : 2 ≤ n := by omega
  set r := y - herm σ x y • x with hrdef
  have hxr : herm σ x r = 0 := by simp [hrdef, hx]
  have hyr : y = herm σ x y • x + r := by rw [hrdef]; abel
  by_cases hrr : herm σ r r ≠ 0
  · exact exists_mem_T_of_aniso_diff hσ hx hy hrr
  push Not at hrr
  by_cases hr0 : r = 0
  · obtain ⟨z, hz, hxz⟩ := exists_norm_one_perp hσ hn2 hx
    have hy' : y = herm σ x y • x + (0 : K) • z := by
      rw [zero_smul, add_zero]
      nth_rewrite 1 [hyr]
      rw [hr0, add_zero]
    obtain ⟨t, ht, htx⟩ := exists_mem_T_of_orthonormal hσ hx hz hxz (herm σ x y) 0
      (by rw [← hy']; exact hy)
    exact ⟨t, ht, by rw [htx, ← hy']⟩
  obtain ⟨v, hxv, hvv, hrv⟩ := exists_partner_perp hσ hx hr0 hrr hxr
  have hvr : herm σ v r = 1 := by rw [herm_conj σ hσ.invol, hrv, map_one]
  have hrx : herm σ r x = 0 := herm_eq_zero_comm σ hσ.invol hxr
  have hvx : herm σ v x = 0 := herm_eq_zero_comm σ hσ.invol hxv
  have step : ∀ z : Fin n → K, herm σ z z = 1 → herm σ x z = 0 →
      (∃ t ∈ T σ n, t • z = y) → ∃ t ∈ T σ n, t • x = y := by
    intro z hz hxz ⟨t2, ht2, ht2z⟩
    obtain ⟨t1, ht1, ht1x⟩ := exists_mem_T_of_orthonormal hσ hx hz hxz 0 1
      (by rw [zero_smul, zero_add, one_smul]; exact hz)
    refine ⟨t2 * t1, (T σ n).mul_mem ht2 ht1, ?_⟩
    rw [mul_smul, ht1x, zero_smul, zero_add, one_smul, ht2z]
  rcases hn with hn4 | ⟨hn3, s, hs0, hs1⟩
  · obtain ⟨z, hz, hxz, hrz, hvz⟩ := exists_norm_one_perp_three hσ hn4 hx hrr hvv hrv hxr hxv
    refine step z hz hxz ?_
    have hzy : herm σ z y = 0 := by
      rw [hyr, herm_add_right, herm_smul_right, herm_eq_zero_comm σ hσ.invol hxz,
        herm_eq_zero_comm σ hσ.invol hrz]
      ring
    obtain ⟨t, ht, htz⟩ := exists_mem_T_of_orthonormal hσ hz hy hzy 0 1
      (by rw [zero_smul, zero_add, one_smul]; exact hy)
    exact ⟨t, ht, by rw [htz, zero_smul, zero_add, one_smul]⟩
  · obtain ⟨c₁, hc₁⟩ := hσ.trace_surj 1 (map_one σ)
    obtain ⟨ρ, hσρ⟩ : ∃ ρ, σ ρ = c₁ / s := ⟨σ (c₁ / s), hσ.invol _⟩
    have hρ : ρ = σ (c₁ / s) := by rw [← hσρ, hσ.invol]
    obtain ⟨z, hz⟩ : ∃ z, z = ρ • r + s • v := ⟨_, rfl⟩
    have hzz : herm σ z z = 1 := by
      rw [hz]
      simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hrr, hvv, hrv,
        hvr]
      have h1 : σ ρ * s = c₁ := by rw [hσρ]; field_simp
      have h2 : σ s * ρ = σ c₁ := by
        rw [hρ, ← map_mul]
        congr 1
        field_simp
      linear_combination h1 + h2 + hc₁
    have hxz : herm σ x z = 0 := by
      rw [hz]; simp only [herm_add_right, herm_smul_right, hxr, hxv]; ring
    refine step z hzz hxz ?_
    have hzy : herm σ z y = σ s := by
      rw [hyr, hz]
      simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hrx, hrr, hvx,
        hvr]
      ring
    refine exists_mem_T_of_aniso_diff hσ hzz hy ?_
    rw [herm_sub_proj hσ.invol hzz, hy, hzy, hσ.invol]
    intro h
    apply hs1
    linear_combination -h

theorem exists_mem_T_fix_hyp (hσ : IsUnitaryInvolution σ) (W : WittData σ) (g : SUid σ 4) :
    ∃ t ∈ T σ 4, (t * g) • W.hypA 2 = W.hypA 2 ∧ (t * g) • W.hypB 2 = W.hypB 2 := by
  set a := W.hypA 2 with ha_def
  set b := W.hypB 2 with hb_def
  have ha : herm σ a a = 0 := W.herm_hypA_hypA
  have hb : herm σ b b = 0 := W.herm_hypB_hypB
  have hab : herm σ a b = 1 := W.herm_hypA_hypB
  have hba : herm σ b a = 1 := W.herm_hypB_hypA hσ.invol
  have ha0 : a ≠ 0 := W.hypA_ne_zero
  have hga0 : g • a ≠ 0 := fun h => ha0 ((smul_eq_zero_iff_eq g).mp h)
  obtain ⟨t1, ht1, ht1a⟩ := exists_mem_T_smul_eq_of_iso hσ (by norm_num) hga0
    (by rw [herm_smul_smul, ha]) ha0 ha
  obtain ⟨f', hf'⟩ : ∃ f', f' = t1 • g • b := ⟨_, rfl⟩
  have haf' : herm σ a f' = 1 := by
    rw [hf', ← ht1a, herm_smul_smul, herm_smul_smul, hab]
  have hf'f' : herm σ f' f' = 0 := by rw [hf', herm_smul_smul, herm_smul_smul, hb]
  have hf'a : herm σ f' a = 1 := by rw [herm_conj σ hσ.invol, haf', map_one]
  set y := f' - b - herm σ b f' • a with hy
  have hay : herm σ a y = 0 := by rw [hy]; simp [haf', hab, ha]
  have hby : herm σ b y = 0 := by rw [hy]; simp [hb, hba]
  obtain ⟨y0, y1⟩ := W.coord_eq_zero_of_perp hay hby
  set w₁ : Fin 4 → K := Pi.single 2 1 + Pi.single 3 W.u with hw₁
  set w₂ : Fin 4 → K := Pi.single 2 1 + Pi.single 3 (W.u * W.ω) with hw₂
  have h23 : (2 : Fin 4) ≠ 3 := by decide
  have hw₁₁ : herm σ w₁ w₁ = 0 := by
    rw [hw₁, herm_single_add_single h23, W.hu]; ring
  have hw₂₂ : herm σ w₂ w₂ = 0 := by
    rw [hw₂, herm_single_add_single h23, map_mul,
      show σ W.u * σ W.ω * (W.u * W.ω) = (σ W.u * W.u) * (σ W.ω * W.ω) by ring, W.hu, W.hω]
    ring
  have haw : ∀ w : Fin 4 → K, w 0 = 0 → w 1 = 0 → herm σ a w = 0 ∧ herm σ b w = 0 := by
    intro w h0 h1
    rw [ha_def, hb_def, W.herm_hypA_left, W.herm_hypB_left, h0, h1]
    simp
  obtain ⟨haw₁, hbw₁⟩ := haw w₁ (by simp [hw₁]) (by simp [hw₁])
  obtain ⟨haw₂, hbw₂⟩ := haw w₂ (by simp [hw₂]) (by simp [hw₂])
  have hw₁b : herm σ w₁ b = 0 := herm_eq_zero_comm σ hσ.invol hbw₁
  have hw₂b : herm σ w₂ b = 0 := herm_eq_zero_comm σ hσ.invol hbw₂
  have hw₁a : herm σ w₁ a = 0 := herm_eq_zero_comm σ hσ.invol haw₁
  have hw₂a : herm σ w₂ a = 0 := herm_eq_zero_comm σ hσ.invol haw₂
  set β₂ := (y 3 - W.u * y 2) / (W.u * (W.ω - 1)) with hβ₂
  set β₁ := y 2 - β₂ with hβ₁
  have hyw : y = β₁ • w₁ + β₂ • w₂ := by
    have hu0 := W.u_ne_zero
    have hω1 : W.ω - 1 ≠ 0 := sub_ne_zero.mpr W.hω1
    funext i
    fin_cases i
    · simp [hw₁, hw₂, y0]
    · simp [hw₁, hw₂, y1]
    · simp [hw₁, hw₂, hβ₁]
    · simp [hw₁, hw₂, hβ₁, hβ₂]
      field_simp
      ring
  obtain ⟨S₁, hS₁, hS₁s⟩ := exists_mem_T_siegel hσ ha hw₁₁ haw₁ β₁
  obtain ⟨S₂, hS₂, hS₂s⟩ := exists_mem_T_siegel hσ ha hw₂₂ haw₂ β₂
  obtain ⟨κ, hκ⟩ : ∃ κ, κ = -(σ β₂ * β₁ * herm σ w₂ w₁) - herm σ b f' := ⟨_, rfl⟩
  have hXf : (S₂ * S₁) • b = f' + κ • a := by
    rw [mul_smul, hS₁s, hS₂s]
    have hf'eq : f' = b + (β₁ • w₁ + β₂ • w₂) + herm σ b f' • a := by
      rw [← hyw, hy]; abel
    conv_rhs => rw [hf'eq]
    simp only [herm_add_right, herm_sub_right, herm_smul_right, hab, haw₁, hw₂b, hw₁b, hw₂a, ha]
    rw [hκ]
    module
  have hXX : herm σ ((S₂ * S₁) • b) ((S₂ * S₁) • b) = 0 := by rw [herm_smul_smul, hb]
  have hκE : κ + σ κ = 0 := by
    rw [hXf] at hXX
    simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hf'f', ha, haf',
      hf'a] at hXX
    linear_combination hXX
  have hε : -κ + σ (-κ) = 0 := by rw [map_neg]; linear_combination -hκE
  set t₂ := tv hσ.invol ha hε * (S₂ * S₁) with ht₂
  have ht₂T : t₂ ∈ T σ 4 :=
    (T σ 4).mul_mem (tv_mem_T _ _ _) ((T σ 4).mul_mem hS₂ hS₁)
  have ht₂a : t₂ • a = a := by
    rw [ht₂, mul_smul, mul_smul, hS₁s, hS₂s, tv_smul]
    simp [ha, hw₁a, hw₂a]
  have ht₂b : t₂ • b = f' := by
    rw [ht₂, mul_smul, hXf, tv_smul]
    simp only [herm_add_right, herm_smul_right, haf', ha]
    module
  refine ⟨t₂⁻¹ * t1, (T σ 4).mul_mem ((T σ 4).inv_mem ht₂T) ht1, ?_, ?_⟩
  · rw [mul_smul, mul_smul, ht1a, inv_smul_eq_iff, ht₂a]
  · rw [mul_smul, mul_smul, ← hf', inv_smul_eq_iff, ht₂b]

end CFSG.ClassicalGroups.Unitary
