module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiUBasic
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiYDelta

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {K : Type*} [Field K] [Fintype K] [CharP K 2]
  {T₁ R₂ : Subgroup G} {t d : G} {a : ℕ} {u v : G → K} {κ : K} {φ : G → K × K × K} {γ c : K}

namespace SzRCoords2

theorem exists_mul_of_mem_sup (hS : SzR2 T₁ R₂ t d) {x : G} (hx : x ∈ T₁ ⊔ R₂) :
    ∃ y ∈ T₁, ∃ r ∈ R₂, y * r = x := by
  have h1 : ((T₁ ⊔ R₂ : Subgroup G) : Set G) = (T₁ : Set G) * (R₂ : Set G) :=
    coe_mul_of_left_le_normalizer_right T₁ R₂ hS.le_normalizer_R₂
  have hx' : x ∈ ((T₁ ⊔ R₂ : Subgroup G) : Set G) := hx
  rw [h1] at hx'
  obtain ⟨y, hy, r, hr, hyr⟩ := hx'
  exact ⟨y, hy, r, hr, hyr⟩

theorem map_mul_T₁_R₂ (h : SzRCoords2 T₁ R₂ t a u v φ γ c) {y r : G} (hy : y ∈ T₁)
    (hr : r ∈ R₂) : φ (y * r) = (u y, (φ r).2.1, 0) := by
  rw [h.mul _ (le_szR_left T₁ R₂ t hy) _ (le_szR_mid T₁ R₂ t hr), h.of_T₁ y hy, h.of_R₂ r hr]
  simp

theorem fst_eq_zero_iff (hS : SzR2 T₁ R₂ t d) (h : SzRCoords2 T₁ R₂ t a u v φ γ c)
    (hc : SzRootCoords T₁ a d u v κ) (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1))
    {x : G} (hx : x ∈ T₁ ⊔ R₂) : (φ x).1 = 0 ↔ x ∈ R₂ := by
  constructor
  · intro h0
    obtain ⟨y, hy, r, hr, rfl⟩ := exists_mul_of_mem_sup hS hx
    rw [h.map_mul_T₁_R₂ hy hr] at h0
    have hyA : y ∈ szA₁ T₁ := (hc.mem_szA₁_iff ha hK hy).mpr h0
    exact mul_mem (hS.le_R₂ hyA) hr
  · intro hxR
    rw [h.of_R₂ x hxR]

theorem snd_eq_zero_iff (h : SzRCoords2 T₁ R₂ t a u v φ γ c) {r : G} (hr : r ∈ R₂) :
    (φ r).2.1 = 0 ↔ r ∈ szA₁ T₁ := by
  rw [← h.ker r (le_szR_mid T₁ R₂ t hr), h.of_R₂ r hr]
  simp [Prod.ext_iff]

theorem v_inv (h : SzRCoords2 T₁ R₂ t a u v φ γ c) {b : G} (hb : b ∈ szA₁ T₁) :
    v b⁻¹ = v b := by
  have h1 := h.v_mul b⁻¹ (inv_mem hb) b hb
  rw [inv_mul_cancel, h.v_one] at h1
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  linear_combination -h1 - v b * h2

theorem layerA_heq (h : SzRCoords2 T₁ R₂ t a u v φ γ c) :
    ∀ x ∈ szA₁ T₁, ∀ x' ∈ szA₁ T₁, v x = v x' ↔ x⁻¹ * x' ∈ (⊥ : Subgroup G) := by
  intro x hx x' hx'
  rw [mem_bot, inv_mul_eq_one]
  constructor
  · intro he
    have h1 := h.v_mul x⁻¹ (inv_mem hx) x' hx'
    rw [h.v_inv hx, he, CharTwo.add_self_eq_zero] at h1
    have h2 := h.v_inj _ (mul_mem (inv_mem hx) hx') h1
    rwa [inv_mul_eq_one] at h2
  · rintro rfl
    rfl

theorem layerOne_heq (hS : SzR2 T₁ R₂ t d) (h : SzRCoords2 T₁ R₂ t a u v φ γ c)
    (hc : SzRootCoords T₁ a d u v κ) (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1)) :
    ∀ x ∈ T₁ ⊔ R₂, ∀ x' ∈ T₁ ⊔ R₂, (φ x).1 = (φ x').1 ↔ x⁻¹ * x' ∈ R₂ := by
  intro x hx x' hx'
  have hxx := mul_mem (inv_mem hx) hx'
  rw [← h.fst_eq_zero_iff hS hc ha hK hxx,
    h.map_inv_mul (sup_le_szR T₁ R₂ t hx) (sup_le_szR T₁ R₂ t hx')]
  simp only [Prod.fst_sub]
  constructor
  · intro he
    rw [he, sub_self]
  · intro h0
    exact (sub_eq_zero.mp h0).symm

theorem layerTwo_heq (h : SzRCoords2 T₁ R₂ t a u v φ γ c) :
    ∀ x ∈ R₂, ∀ x' ∈ R₂, (φ x).2.1 = (φ x').2.1 ↔ x⁻¹ * x' ∈ szA₁ T₁ := by
  intro x hx x' hx'
  have hxx := mul_mem (inv_mem hx) hx'
  rw [← h.snd_eq_zero_iff hxx,
    h.map_inv_mul (le_szR_mid T₁ R₂ t hx) (le_szR_mid T₁ R₂ t hx')]
  simp only [Prod.snd_sub, Prod.fst_sub]
  constructor
  · intro he
    rw [he, sub_self]
  · intro h0
    exact (sub_eq_zero.mp h0).symm

theorem layerOne_surj (h : SzRCoords2 T₁ R₂ t a u v φ γ c) (hc : SzRootCoords T₁ a d u v κ) :
    ∀ w, ∃ x ∈ T₁ ⊔ R₂, (φ x).1 = w := by
  intro w
  obtain ⟨y, hy, hyu, -⟩ := hc.surj w 0
  exact ⟨y, mem_sup_left hy, by rw [h.of_T₁ y hy, hyu]⟩

theorem layerTwo_surj (hS : SzR2 T₁ R₂ t d) (h : SzRCoords2 T₁ R₂ t a u v φ γ c) :
    ∀ w, ∃ x ∈ R₂, (φ x).2.1 = w := by
  intro w
  obtain ⟨b, hb, hbw⟩ := h.v_surj w
  obtain ⟨r, hr, hrb⟩ := hS.rho_surj b hb
  exact ⟨r, hr, by rw [h.snd_eq r (le_szR_mid T₁ R₂ t hr), hrb, hbw]⟩

theorem _root_.CFSG.SeitzReduction.RankOne.SzRootCoords.v_conj_pow_szA₁
    (hc : SzRootCoords T₁ a d u v κ) (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1))
    (m : ℕ) {b : G} (hb : b ∈ szA₁ T₁) :
    (d ^ m)⁻¹ * b * d ^ m ∈ szA₁ T₁ ∧
      v ((d ^ m)⁻¹ * b * d ^ m) = (κ ^ (2 ^ (a + 1) + 1)) ^ m * v b := by
  induction m with
  | zero => simpa using hb
  | succ m ih =>
    have e : (d ^ (m + 1))⁻¹ * b * d ^ (m + 1) = d⁻¹ * ((d ^ m)⁻¹ * b * d ^ m) * d := by
      rw [pow_succ]
      group
    rw [e]
    refine ⟨hc.conj_mem_szA₁ ha hK ih.1, ?_⟩
    rw [hc.v_conj_szA₁ ha hK ih.1, ih.2, pow_succ]
    ring

theorem le_normalizer_bot (X : Subgroup G) : X ≤ normalizer ((⊥ : Subgroup G) : Set G) := by
  intro g _
  refine mem_normalizer_iff.mpr fun y => ?_
  simp only [mem_bot]
  constructor
  · rintro rfl
    group
  · intro h1
    calc y = g⁻¹ * (g * y * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group

theorem fixed_of_isPGroup (hS : SzR2 T₁ R₂ t d) (h : SzRCoords2 T₁ R₂ t a u v φ γ c)
    (hc : SzRootCoords T₁ a d u v κ) (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1))
    (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, (κ ^ (2 ^ (a + 1) + 1)) ^ m = w) (hγ : γ = 0)
    {P : Subgroup G} (hP : IsPGroup 2 P) (hPY : P ≤ normalizer (szR T₁ R₂ t : Set G))
    (hdP : d ∈ normalizer (P : Set G)) :
    (∀ n ∈ P, ∀ b ∈ szA₁ T₁, n * b * n⁻¹ = b) ∧
      (∀ n ∈ P, ∀ x ∈ T₁ ⊔ R₂, (φ (n * x * n⁻¹)).1 = (φ x).1) ∧
      ∀ n ∈ P, ∀ r ∈ R₂, (φ (n * r * n⁻¹)).2.1 = (φ r).2.1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := normalizer (szR T₁ R₂ t : Set G)
  have hYA : Y ≤ normalizer (szA₁ T₁ : Set G) := h.normalizer_szR_le_normalizer_szA₁ ha hK
  have hY1 : Y ≤ normalizer ((T₁ ⊔ R₂ : Subgroup G) : Set G) :=
    h.normalizer_le_normalizer_sup ha hK hγ
  have hY2 : Y ≤ normalizer (R₂ : Set G) := h.normalizer_le_normalizer_R₂ hS ha hK hγ
  have hdY : d ∈ Y := hS.d_mem_normalizer_szR hc
  have hdvd : 2 ∣ Nat.card K := by
    rw [Nat.card_eq_fintype_card, hK]
    exact dvd_pow_self 2 (by omega)
  have hκ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, κ ^ m = w := fun w hw => by
    obtain ⟨m, hm⟩ := hμ w hw
    exact ⟨(2 ^ (a + 1) + 1) * m, by rw [pow_mul]; exact hm⟩
  refine ⟨fun n hn b hb => ?_, fun n hn x hx => ?_, fun n hn r hr => ?_⟩
  · have key := secPerm_fixed_of_isPGroup hYA (le_normalizer_bot Y) h.v_surj h.layerA_heq hP hPY
      hdY hdP (fun x hx x' hx' h0 h0' => by
        rw [h.v_one] at h0 h0'
        obtain ⟨m, hm⟩ := hμ (v x' / v x) (div_ne_zero h0' h0)
        refine ⟨m, ?_⟩
        rw [(hc.v_conj_pow_szA₁ ha hK m hx).2, hm, div_mul_cancel₀ _ h0]) hdvd n hn b hb
    have hnb : n * b * n⁻¹ ∈ szA₁ T₁ := (mem_normalizer_iff.mp (hYA (hPY hn)) b).mp hb
    have h1 := (h.layerA_heq _ hnb _ hb).mp key
    rw [mem_bot, inv_mul_eq_one] at h1
    exact h1
  · refine secPerm_fixed_of_isPGroup hY1 hY2 (h.layerOne_surj hc) (h.layerOne_heq hS hc ha hK) hP
      hPY hdY hdP (fun x hx x' hx' h0 h0' => ?_) hdvd n hn x hx
    rw [h.map_one] at h0 h0'
    obtain ⟨m, hm⟩ := hκ ((φ x').1 / (φ x).1) (div_ne_zero h0' h0)
    refine ⟨m, ?_⟩
    rw [h.map_conj_d_pow hS hc ha hK m (sup_le_szR T₁ R₂ t hx)]
    simp only [szTorusSmul]
    rw [hm, div_mul_cancel₀ _ h0]
  · refine secPerm_fixed_of_isPGroup hY2 hYA (h.layerTwo_surj hS) h.layerTwo_heq hP
      hPY hdY hdP (fun x hx x' hx' h0 h0' => ?_) hdvd n hn r hr
    rw [h.map_one] at h0 h0'
    obtain ⟨m, hm⟩ := hμ ((φ x').2.1 / (φ x).2.1) (div_ne_zero h0' h0)
    refine ⟨m, ?_⟩
    rw [h.map_conj_d_pow hS hc ha hK m (le_szR_mid T₁ R₂ t hx)]
    simp only [szTorusSmul]
    rw [← pow_mul, mul_comm m, pow_mul, hm, div_mul_cancel₀ _ h0]

theorem thd_conj_t (h : SzRCoords2 T₁ R₂ t a u v φ γ c) (ha : 1 ≤ a)
    (hK : Fintype.card K = 2 ^ (2 * a + 1)) {y : G} (hy : y ∈ normalizer (szR T₁ R₂ t : Set G)) :
    y * t * y⁻¹ ∈ szR T₁ R₂ t ∧ (φ (y * t * y⁻¹)).2.2 = 1 := by
  have hy' : y⁻¹ ∈ normalizer (szR T₁ R₂ t : Set G) := inv_mem hy
  have hmem := (mem_normalizer_iff''.mp hy' t).mp (mem_szR_right T₁ R₂ t)
  rw [inv_inv] at hmem
  refine ⟨hmem, ?_⟩
  have hnot := (h.conj_t_not_mem_sup ha hK hy').1
  rw [inv_inv] at hnot
  rcases h.mem _ hmem with h0 | h1
  · exact absurd ((h.thd_eq_zero_iff _ hmem).mp h0) hnot
  · exact h1

theorem snd_conj_R₂ (hS : SzR2 T₁ R₂ t d) (h : SzRCoords2 T₁ R₂ t a u v φ γ c) (ha : 1 ≤ a)
    (hK : Fintype.card K = 2 ^ (2 * a + 1)) (hγ : γ = 0) {y : G}
    (hy : y ∈ normalizer (szR T₁ R₂ t : Set G)) {r : G} (hr : r ∈ R₂) :
    (φ (y * r * y⁻¹)).2.1 = v (y * (r * t * r⁻¹ * t⁻¹) * y⁻¹) := by
  have hyr : y * r * y⁻¹ ∈ R₂ :=
    (mem_normalizer_iff.mp (h.normalizer_le_normalizer_R₂ hS ha hK hγ hy) r).mp hr
  obtain ⟨hyt, hyt3⟩ := h.thd_conj_t ha hK hy
  have hc1 := h.comm _ (le_szR_mid T₁ R₂ t hyr) _ hyt
  rw [show y * r * y⁻¹ * (y * t * y⁻¹) * (y * r * y⁻¹)⁻¹ * (y * t * y⁻¹)⁻¹ =
    y * (r * t * r⁻¹ * t⁻¹) * y⁻¹ by group] at hc1
  rw [hc1, h.of_R₂ _ hyr, hγ]
  simp [szCommMap, hyt3, zero_pow (SzRadical.two_pow_ne_zero _)]

theorem snd_conj_T₁ (hS : SzR2 T₁ R₂ t d) (h : SzRCoords2 T₁ R₂ t a u v φ γ c) (ha : 1 ≤ a)
    (hK : Fintype.card K = 2 ^ (2 * a + 1)) (hγ : γ = 0) {y : G}
    (hy : y ∈ normalizer (szR T₁ R₂ t : Set G)) {x : G} (hx : x ∈ T₁) :
    (φ (y * x * y⁻¹)).2.1 = (φ (y * x * y⁻¹)).1 * (φ (y * t * y⁻¹)).1 ^ 2 ^ (a + 1) +
      (φ (y * x * y⁻¹)).1 ^ 2 ^ (a + 1) * (φ (y * t * y⁻¹)).1 := by
  have hyx : y * x * y⁻¹ ∈ T₁ ⊔ R₂ :=
    (mem_normalizer_iff.mp (h.normalizer_le_normalizer_sup ha hK hγ hy) x).mp (mem_sup_left hx)
  have hyxR := sup_le_szR T₁ R₂ t hyx
  have hyx3 : (φ (y * x * y⁻¹)).2.2 = 0 := (h.thd_eq_zero_iff _ hyxR).mpr hyx
  obtain ⟨hyt, hyt3⟩ := h.thd_conj_t ha hK hy
  have hc1 := h.comm _ hyxR _ hyt
  rw [show y * x * y⁻¹ * (y * t * y⁻¹) * (y * x * y⁻¹)⁻¹ * (y * t * y⁻¹)⁻¹ =
    y * (x * t * x⁻¹ * t⁻¹) * y⁻¹ by group, hS.t_comm x hx,
    show y * (t * x * x⁻¹ * t⁻¹) * y⁻¹ = 1 by group, h.v_one, hγ] at hc1
  simp only [szCommMap, hyx3, hyt3, zero_mul, add_zero, one_mul] at hc1
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  linear_combination hc1 + (φ (y * x * y⁻¹)).2.1 * h2

theorem v_conj_sq_T₁ (h : SzRCoords2 T₁ R₂ t a u v φ γ c) (ha : 1 ≤ a)
    (hK : Fintype.card K = 2 ^ (2 * a + 1)) (hγ : γ = 0) {y : G}
    (hy : y ∈ normalizer (szR T₁ R₂ t : Set G)) {x : G} (hx : x ∈ T₁) :
    v (y * x ^ 2 * y⁻¹) = (φ (y * x * y⁻¹)).1 ^ (2 ^ (a + 1) + 1) + c * (φ (y * x * y⁻¹)).2.1 := by
  have hyx : y * x * y⁻¹ ∈ T₁ ⊔ R₂ :=
    (mem_normalizer_iff.mp (h.normalizer_le_normalizer_sup ha hK hγ hy) x).mp (mem_sup_left hx)
  have hyxR := sup_le_szR T₁ R₂ t hyx
  have hyx3 : (φ (y * x * y⁻¹)).2.2 = 0 := (h.thd_eq_zero_iff _ hyxR).mpr hyx
  have h1 := h.sq _ hyxR
  rw [show (y * x * y⁻¹) ^ 2 = y * x ^ 2 * y⁻¹ by simp only [_root_.sq]; group] at h1
  rw [h1, szSqMap, hyx3, hγ]
  ring

theorem v_conj_sq_R₂ (hS : SzR2 T₁ R₂ t d) (h : SzRCoords2 T₁ R₂ t a u v φ γ c) (ha : 1 ≤ a)
    (hK : Fintype.card K = 2 ^ (2 * a + 1)) (hγ : γ = 0) {y : G}
    (hy : y ∈ normalizer (szR T₁ R₂ t : Set G)) {r : G} (hr : r ∈ R₂) :
    v (y * r ^ 2 * y⁻¹) = c * (φ (y * r * y⁻¹)).2.1 := by
  have hyr : y * r * y⁻¹ ∈ R₂ :=
    (mem_normalizer_iff.mp (h.normalizer_le_normalizer_R₂ hS ha hK hγ hy) r).mp hr
  have h1 := h.sq _ (le_szR_mid T₁ R₂ t hyr)
  rw [show (y * r * y⁻¹) ^ 2 = y * r ^ 2 * y⁻¹ by simp only [_root_.sq]; group] at h1
  rw [h1, h.of_R₂ _ hyr, szSqMap, hγ]
  simp [zero_pow (Nat.succ_ne_zero _)]

end SzRCoords2

end CFSG.SeitzReduction.RankOne
