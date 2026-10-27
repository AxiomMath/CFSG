module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiUSylow

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {K : Type*} [Field K] [Fintype K] [CharP K 2]
  {T₁ R₂ : Subgroup G} {t d : G} {a : ℕ} {u v : G → K} {κ : K} {φ : G → K × K × K} {γ c : K}
  {U U₁ : Subgroup G} {q : ℕ}

@[expose] def szLam (φ : G → K × K × K) (t x : G) : K := (φ (x * t * x⁻¹ * t⁻¹)).1

theorem SzRootCoords.exists_not_commute (hc : SzRootCoords T₁ a d u v κ) (ha : 1 ≤ a)
    (hK : Fintype.card K = 2 ^ (2 * a + 1)) : ∃ y ∈ T₁, ∃ y' ∈ T₁, y * y' ≠ y' * y := by
  obtain ⟨l, hl⟩ := SzStartField.exists_pow_theta_add_ne_zero ha hK
  obtain ⟨y, hy, hyu, -⟩ := hc.surj 1 0
  obtain ⟨y', hy', hyu', -⟩ := hc.surj l 0
  refine ⟨y, hy, y', hy', fun he => hl ?_⟩
  have h1 := (hc.comm hy hy').2
  rw [he, mul_inv_cancel_right, mul_inv_cancel, hc.v_one, hyu, hyu', one_pow, one_mul,
    mul_one] at h1
  exact h1.symm

namespace SzRCoords2

theorem exists_not_inverts_of_sq_eq_one (hS : SzR2 T₁ R₂ t d)
    (h : SzRCoords2 T₁ R₂ t a u v φ γ c) (hc0 : ∀ r ∈ R₂, r ^ 2 = 1) :
    ∃ r ∈ R₂, t * r * t⁻¹ ≠ r⁻¹ := by
  obtain ⟨r, hr, hr1⟩ := h.layerTwo_surj hS 1
  refine ⟨r, hr, fun he => ?_⟩
  have hrr : r⁻¹ = r := inv_eq_of_mul_eq_one_right (by rw [← _root_.sq]; exact hc0 r hr)
  rw [hrr] at he
  have hrt : t * r = r * t := by
    calc t * r = t * r * t⁻¹ * t := by group
      _ = r * t := by rw [he]
  have h1 : r * t * r⁻¹ * t⁻¹ = 1 := by
    rw [← hrt]
    group
  rw [h.snd_eq r (le_szR_mid T₁ R₂ t hr), h1, h.v_one] at hr1
  exact zero_ne_one hr1

theorem sup_le_normalizer_R₂ (hS : SzR2 T₁ R₂ t d) :
    T₁ ⊔ R₂ ≤ normalizer (R₂ : Set G) :=
  sup_le hS.le_normalizer_R₂ le_normalizer

theorem sup_le_U₁ (hU : SzU T₁ R₂ t d q U U₁) : T₁ ⊔ R₂ ≤ U₁ :=
  hU.inf_eq ▸ inf_le_left

theorem fst_conj_eq (hS : SzR2 T₁ R₂ t d) (h : SzRCoords2 T₁ R₂ t a u v φ γ c)
    (hc : SzRootCoords T₁ a d u v κ) (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1))
    (hU : SzU T₁ R₂ t d q U U₁) {x z : G} (hx : x ∈ U) (hz : z ∈ T₁ ⊔ R₂) :
    x * z * x⁻¹ ∈ T₁ ⊔ R₂ ∧ (φ (x * z * x⁻¹)).1 = (φ z).1 := by
  have h1 := hU.conj_sup x hx z hz
  have hmem : x * z * x⁻¹ ∈ T₁ ⊔ R₂ := by
    have e : x * z * x⁻¹ = z * (z⁻¹ * (x * z * x⁻¹)) := by group
    rw [e]
    exact mul_mem hz (mem_sup_right h1)
  exact ⟨hmem, ((h.layerOne_heq hS hc ha hK z hz _ hmem).mpr h1).symm⟩

theorem comm_mem_R₂_of_mem_sup (hS : SzR2 T₁ R₂ t d) (hU : SzU T₁ R₂ t d q U U₁) {x y : G}
    (hx : x ∈ T₁ ⊔ R₂) (hy : y ∈ U) : x * y * x⁻¹ * y⁻¹ ∈ R₂ := by
  have h1 := hU.conj_sup y hy x hx
  have hxN := sup_le_normalizer_R₂ hS hx
  have e : x * y * x⁻¹ * y⁻¹ = x * (x⁻¹ * (y * x * y⁻¹))⁻¹ * x⁻¹ := by group
  rw [e]
  exact (mem_normalizer_iff.mp hxN _).mp (inv_mem h1)

theorem comm_mem_R₂_of_mem_sup' (hS : SzR2 T₁ R₂ t d) (hU : SzU T₁ R₂ t d q U U₁) {x y : G}
    (hx : x ∈ U) (hy : y ∈ T₁ ⊔ R₂) : x * y * x⁻¹ * y⁻¹ ∈ R₂ := by
  have h1 := comm_mem_R₂_of_mem_sup hS hU hy hx
  have e : x * y * x⁻¹ * y⁻¹ = (y * x * y⁻¹ * x⁻¹)⁻¹ := by group
  rw [e]
  exact inv_mem h1

theorem comm_t_mem (hU : SzU T₁ R₂ t d q U U₁) {x : G} (hx : x ∈ U) :
    x * t * x⁻¹ * t⁻¹ ∈ T₁ ⊔ R₂ :=
  hU.comm_mem x hx t (hU.szR_le (mem_szR_right T₁ R₂ t))

theorem szLam_mul (hS : SzR2 T₁ R₂ t d) (h : SzRCoords2 T₁ R₂ t a u v φ γ c)
    (hc : SzRootCoords T₁ a d u v κ) (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1))
    (hU : SzU T₁ R₂ t d q U U₁) {x y : G} (hx : x ∈ U) (hy : y ∈ U) :
    szLam φ t (x * y) = szLam φ t x + szLam φ t y := by
  obtain ⟨hm1, he1⟩ := fst_conj_eq hS h hc ha hK hU hx (comm_t_mem hU hy)
  have hm2 := comm_t_mem hU hx
  have e : x * y * t * (x * y)⁻¹ * t⁻¹ =
      (x * (y * t * y⁻¹ * t⁻¹) * x⁻¹) * (x * t * x⁻¹ * t⁻¹) := by group
  simp only [szLam]
  rw [e, h.mul _ (sup_le_szR T₁ R₂ t hm1) _ (sup_le_szR T₁ R₂ t hm2), Prod.fst_add, he1,
    add_comm]

theorem szLam_eq_zero_of_mem_szR (h : SzRCoords2 T₁ R₂ t a u v φ γ c) {x : G}
    (hx : x ∈ szR T₁ R₂ t) : szLam φ t x = 0 := by
  have h1 := h.comm_mem x hx t (mem_szR_right T₁ R₂ t)
  have h2 := (h.ker _ (mul_mem (mul_mem (mul_mem hx (mem_szR_right T₁ R₂ t)) (inv_mem hx))
    (inv_mem (mem_szR_right T₁ R₂ t)))).mpr h1
  simp only [szLam]
  rw [h2]
  rfl

theorem mem_sup_of_szLam_eq_zero (hS : SzR2 T₁ R₂ t d) (h : SzRCoords2 T₁ R₂ t a u v φ γ c)
    (hc : SzRootCoords T₁ a d u v κ) (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1))
    (hU : SzU T₁ R₂ t d q U U₁) (hinv : ∃ r ∈ R₂, t * r * t⁻¹ ≠ r⁻¹) {x : G} (hx : x ∈ U₁)
    (h0 : szLam φ t x = 0) : x ∈ T₁ ⊔ R₂ := by
  have hxU := hU.U₁_le hx
  have h1 : x * t * x⁻¹ * t⁻¹ ∈ R₂ := (h.fst_eq_zero_iff hS hc ha hK (comm_t_mem hU hxU)).mp h0
  have hxR : x ∈ szR T₁ R₂ t := by
    by_contra hxR
    apply hU.conj_t_not_mem hinv x hxU hxR
    have e : x * t * x⁻¹ = (x * t * x⁻¹ * t⁻¹) * t := by group
    rw [e]
    exact mul_mem (mem_sup_left h1) (mem_sup_right (mem_zpowers t))
  rw [← hU.inf_eq]
  exact mem_inf.mpr ⟨hx, hxR⟩

theorem szLam_conj_d (hS : SzR2 T₁ R₂ t d) (h : SzRCoords2 T₁ R₂ t a u v φ γ c)
    (hc : SzRootCoords T₁ a d u v κ) (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1))
    (hU : SzU T₁ R₂ t d q U U₁) {x : G} (hx : x ∈ U) :
    szLam φ t (d⁻¹ * x * d) = κ * szLam φ t x := by
  simp only [szLam]
  rw [hS.conj_rho x, h.map_conj_d hS hc ha hK (sup_le_szR T₁ R₂ t (comm_t_mem hU hx))]
  rfl

theorem conj_d_mem_U₁ (hU : SzU T₁ R₂ t d q U U₁) {x : G} (hx : x ∈ U₁) : d⁻¹ * x * d ∈ U₁ :=
  (mem_normalizer_iff''.mp hU.d_mem x).mp hx

theorem szLam_conj_d_pow (hS : SzR2 T₁ R₂ t d) (h : SzRCoords2 T₁ R₂ t a u v φ γ c)
    (hc : SzRootCoords T₁ a d u v κ) (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1))
    (hU : SzU T₁ R₂ t d q U U₁) (m : ℕ) {x : G} (hx : x ∈ U₁) :
    (d ^ m)⁻¹ * x * d ^ m ∈ U₁ ∧ szLam φ t ((d ^ m)⁻¹ * x * d ^ m) = κ ^ m * szLam φ t x := by
  induction m with
  | zero => simpa using hx
  | succ m ih =>
    have e : (d ^ (m + 1))⁻¹ * x * d ^ (m + 1) = d⁻¹ * ((d ^ m)⁻¹ * x * d ^ m) * d := by
      rw [pow_succ]
      group
    rw [e]
    refine ⟨conj_d_mem_U₁ hU ih.1, ?_⟩
    rw [szLam_conj_d hS h hc ha hK hU (hU.U₁_le ih.1), ih.2, pow_succ]
    ring

theorem exists_mem_U₁_not_mem (h : SzRCoords2 T₁ R₂ t a u v φ γ c)
    (hc : SzRootCoords T₁ a d u v κ) (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1))
    (hU : SzU T₁ R₂ t d (Fintype.card K) U U₁) : ∃ x ∈ U₁, x ∉ szR T₁ R₂ t := by
  by_contra hcon
  push Not at hcon
  have h1 := Subgroup.card_le_of_le (show U₁ ≤ szR T₁ R₂ t from hcon)
  rw [hU.card_U₁, h.card_szR_eq hc ha hK] at h1
  have hq : 8 ≤ Fintype.card K := by
    rw [hK]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 * Fintype.card K ^ 2 * Fintype.card K < Fintype.card K ^ 4 := by
    have h3 : 0 < Fintype.card K ^ 3 := by positivity
    calc 2 * Fintype.card K ^ 2 * Fintype.card K = 2 * Fintype.card K ^ 3 := by ring
      _ < 8 * Fintype.card K ^ 3 := by omega
      _ ≤ Fintype.card K * Fintype.card K ^ 3 := Nat.mul_le_mul_right _ hq
      _ = Fintype.card K ^ 4 := by ring
  omega

theorem szLam_surj (hS : SzR2 T₁ R₂ t d) (h : SzRCoords2 T₁ R₂ t a u v φ γ c)
    (hc : SzRootCoords T₁ a d u v κ) (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1))
    (hκ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, κ ^ m = w) (hU : SzU T₁ R₂ t d (Fintype.card K) U U₁)
    (hinv : ∃ r ∈ R₂, t * r * t⁻¹ ≠ r⁻¹) : ∀ w : K, ∃ x ∈ U₁, szLam φ t x = w := by
  intro w
  by_cases hw : w = 0
  · exact ⟨1, one_mem _, by rw [hw]; exact h.szLam_eq_zero_of_mem_szR (one_mem _)⟩
  obtain ⟨x₀, hx₀, hx₀R⟩ := h.exists_mem_U₁_not_mem hc ha hK hU
  have hl0 : szLam φ t x₀ ≠ 0 := fun h0 =>
    hx₀R (sup_le_szR T₁ R₂ t (h.mem_sup_of_szLam_eq_zero hS hc ha hK hU hinv hx₀ h0))
  obtain ⟨m, hm⟩ := hκ (w / szLam φ t x₀) (div_ne_zero hw hl0)
  obtain ⟨hmem, hval⟩ := h.szLam_conj_d_pow hS hc ha hK hU m hx₀
  exact ⟨_, hmem, by rw [hval, hm, div_mul_cancel₀ _ hl0]⟩

theorem exists_mem_T₁_conj_not_mem (hS : SzR2 T₁ R₂ t d) (h : SzRCoords2 T₁ R₂ t a u v φ γ c)
    (hc : SzRootCoords T₁ a d u v κ) (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1))
    (hγ : γ = 0) (hU : SzU T₁ R₂ t d q U U₁) (hinv : ∃ r ∈ R₂, t * r * t⁻¹ ≠ r⁻¹) {w : G}
    (hwU : w ∈ U) (hwR : w ∉ szR T₁ R₂ t) :
    ∃ t₂ ∈ T₁, t₂⁻¹ * (w⁻¹ * t₂ * w) ∈ R₂ ∧ t₂⁻¹ * (w⁻¹ * t₂ * w) ∉ szA₁ T₁ := by
  have htR := mem_szR_right T₁ R₂ t
  have hwY := hU.le_normalizer hwU
  obtain ⟨hxR, hx3⟩ := h.thd_conj_t ha hK hwY
  have hx1 : (φ (w * t * w⁻¹)).1 ≠ 0 := by
    intro h0
    apply hU.conj_t_not_mem hinv w hwU hwR
    have hz : w * t * w⁻¹ * t⁻¹ ∈ T₁ ⊔ R₂ := by
      refine (h.thd_eq_zero_iff _ (mul_mem hxR (inv_mem htR))).mp ?_
      rw [h.mul _ hxR _ (inv_mem htR), show t⁻¹ = t from hS.t_inv, h.of_t]
      simp [hx3, CharTwo.add_self_eq_zero]
    have hzR₂ : w * t * w⁻¹ * t⁻¹ ∈ R₂ := by
      refine (h.fst_eq_zero_iff hS hc ha hK hz).mp ?_
      rw [h.mul _ hxR _ (inv_mem htR), show t⁻¹ = t from hS.t_inv, h.of_t]
      simp [h0]
    have e : w * t * w⁻¹ = (w * t * w⁻¹ * t⁻¹) * t := by group
    rw [e]
    exact mul_mem (mem_sup_left hzR₂) (mem_sup_right (mem_zpowers t))
  obtain ⟨l, hl⟩ := SzStartField.exists_pow_theta_add_ne_zero ha hK
  set s₀ := (φ (w * t * w⁻¹)).1 with hs₀
  obtain ⟨t₂, ht₂, ht₂u, -⟩ := hc.surj (l * s₀) 0
  have ht₂R := le_szR_left T₁ R₂ t ht₂
  have hcomm2 : v (t₂ * (w * t * w⁻¹) * t₂⁻¹ * (w * t * w⁻¹)⁻¹) ≠ 0 := by
    rw [h.comm _ ht₂R _ hxR, h.of_T₁ _ ht₂, hγ, ht₂u]
    simp only [szCommMap, hx3, zero_mul, add_zero, mul_zero]
    rw [← hs₀]
    have e : l * s₀ * s₀ ^ 2 ^ (a + 1) + (l * s₀) ^ 2 ^ (a + 1) * s₀ =
        s₀ ^ (2 ^ (a + 1) + 1) * (l ^ 2 ^ (a + 1) + l) := by ring
    rw [e]
    exact mul_ne_zero (pow_ne_zero _ hx1) hl
  refine ⟨t₂, ht₂, ?_, fun hDA => ?_⟩
  · have h1 := hU.conj_sup _ (inv_mem hwU) _ (mem_sup_left ht₂)
    rwa [inv_inv] at h1
  · have hconj : w⁻¹ * t₂ * w ∈ T₁ := by
      have e : w⁻¹ * t₂ * w = t₂ * (t₂⁻¹ * (w⁻¹ * t₂ * w)) := by group
      rw [e]
      exact mul_mem ht₂ (szA₁_le T₁ hDA)
    have h1 := hS.t_comm _ hconj
    apply hcomm2
    have h2 : t₂ * (w * t * w⁻¹) = (w * t * w⁻¹) * t₂ := by
      calc t₂ * (w * t * w⁻¹) = w * ((w⁻¹ * t₂ * w) * t) * w⁻¹ := by group
        _ = w * (t * (w⁻¹ * t₂ * w)) * w⁻¹ := by rw [h1]
        _ = (w * t * w⁻¹) * t₂ := by group
    rw [h2, mul_inv_cancel_right, mul_inv_cancel, h.v_one]

end SzRCoords2

end CFSG.SeitzReduction.RankOne
