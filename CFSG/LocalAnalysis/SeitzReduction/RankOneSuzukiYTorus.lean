module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiNotSylow

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {K : Type*} [Field K] [Fintype K] [CharP K 2]
  {T₁ R₂ : Subgroup G} {t d : G} {a : ℕ} {u v : G → K} {κ : K} {φ : G → K × K × K} {γ c : K}

theorem SzR2.d_mem_normalizer_szR (hS : SzR2 T₁ R₂ t d) (hc : SzRootCoords T₁ a d u v κ) :
    d ∈ normalizer (szR T₁ R₂ t : Set G) := by
  have hT : d ∈ normalizer (T₁ : Set G) := mem_normalizer_of_forall_inv_mul_mul_mem hc.conj_mem
  have ht : d ∈ normalizer (zpowers t : Set G) :=
    mem_normalizer_of_forall_inv_mul_mul_mem fun s hs => by
      have e := commute_of_mem_zpowers hs hS.d_comm
      rw [mul_assoc, ← e, inv_mul_cancel_left]
      exact hs
  exact mem_normalizer_sup (mem_normalizer_sup hT hS.d_mem) ht

namespace SzRCoords2

theorem map_conj_d (hS : SzR2 T₁ R₂ t d) (h : SzRCoords2 T₁ R₂ t a u v φ γ c)
    (hc : SzRootCoords T₁ a d u v κ) (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1)) {x : G}
    (hx : x ∈ szR T₁ R₂ t) : φ (d⁻¹ * x * d) = szTorusSmul a κ (φ x) := by
  obtain ⟨y, hy, r, hr, s, hs, rfl⟩ := hS.exists_decomp' hx
  have hyR := le_szR_left T₁ R₂ t hy
  have hrR := le_szR_mid T₁ R₂ t hr
  have hsR : s ∈ szR T₁ R₂ t := mem_sup_right hs
  have hdy := hc.conj_mem y hy
  have hdr := hS.conj_d_mem hr
  have hds : d⁻¹ * s * d = s := by
    have e := commute_of_mem_zpowers hs hS.d_comm
    rw [mul_assoc, ← e, inv_mul_cancel_left]
  have e : d⁻¹ * (y * r * s) * d = (d⁻¹ * y * d) * (d⁻¹ * r * d) * (d⁻¹ * s * d) := by group
  rw [e, hds, h.mul _ (mul_mem (le_szR_left T₁ R₂ t hdy) (le_szR_mid T₁ R₂ t hdr)) _ hsR,
    h.mul _ (le_szR_left T₁ R₂ t hdy) _ (le_szR_mid T₁ R₂ t hdr), h.of_T₁ _ hdy, h.of_R₂ _ hdr,
    h.mul _ (mul_mem hyR hrR) _ hsR, h.mul _ hyR _ hrR, h.of_T₁ _ hy, h.of_R₂ _ hr,
    hc.conj_u y hy, hS.rho_conj hc ha hK hr]
  have hφs : (φ s).1 = 0 ∧ (φ s).2.1 = 0 := by
    rcases hS.eq_one_or_eq_t hs with rfl | rfl
    · rw [h.map_one]
      exact ⟨rfl, rfl⟩
    · rw [h.of_t]
      exact ⟨rfl, rfl⟩
  simp only [szTorusSmul]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [hφs.1, hφs.2]

theorem map_conj_d_pow (hS : SzR2 T₁ R₂ t d) (h : SzRCoords2 T₁ R₂ t a u v φ γ c)
    (hc : SzRootCoords T₁ a d u v κ) (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1))
    (m : ℕ) {x : G} (hx : x ∈ szR T₁ R₂ t) :
    φ ((d ^ m)⁻¹ * x * d ^ m) = szTorusSmul a (κ ^ m) (φ x) := by
  induction m with
  | zero => simp [szTorusSmul]
  | succ m ih =>
    have hxm : (d ^ m)⁻¹ * x * d ^ m ∈ szR T₁ R₂ t :=
      (mem_normalizer_iff''.mp (pow_mem (hS.d_mem_normalizer_szR hc) m) x).mp hx
    have e : (d ^ (m + 1))⁻¹ * x * d ^ (m + 1) = d⁻¹ * ((d ^ m)⁻¹ * x * d ^ m) * d := by
      rw [pow_succ]
      group
    rw [e, h.map_conj_d hS hc ha hK hxm, ih, SzRadical.szTorusSmul_szTorusSmul, pow_succ,
      mul_comm]

theorem exists_mem_normalizer_conj_t_not_mem (hG : ¬ ∃ N : Subgroup G, N.Normal ∧ N.index = 2)
    (hS : SzR2 T₁ R₂ t d) (h : SzRCoords2 T₁ R₂ t a u v φ γ c) (hc : SzRootCoords T₁ a d u v κ)
    (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1))
    (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, (κ ^ (2 ^ (a + 1) + 1)) ^ m = w)
    (hCt : ∀ P : Sylow 2 (centralizer ({t} : Set G)), Nat.card P = 2 * Nat.card T₁) :
    ∃ n ∈ normalizer (szR T₁ R₂ t : Set G), t⁻¹ * (n⁻¹ * t * n) ∉ szA₁ T₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨z, hzN, hzR, hz2⟩ := hS.exists_mem_normalizer_not_mem hG hc ha hK hμ hCt
  have hb := hcon z hzN
  obtain ⟨r, hr, hrb⟩ := hS.rho_surj _ hb
  have htR := mem_szR_right T₁ R₂ t
  have hbt := h.central t htR _ hb
  have hrt : r * t * r⁻¹ = z⁻¹ * t * z := by
    calc r * t * r⁻¹ = r * t * r⁻¹ * t⁻¹ * t := by group
      _ = t⁻¹ * (z⁻¹ * t * z) * t := by rw [hrb]
      _ = t * (t⁻¹ * (z⁻¹ * t * z)) := by rw [← hbt]
      _ = z⁻¹ * t * z := by group
  have hwC : z * r ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc z * r * t = z * (r * t * r⁻¹) * r := by group
      _ = z * (z⁻¹ * t * z) * r := by rw [hrt]
      _ = t * (z * r) := by group
  have hsyl := h.isSylowOf_sup_zpowers hS hCt
  have hTR : T₁ ⊔ zpowers t ≤ szR T₁ R₂ t :=
    sup_le (le_szR_left T₁ R₂ t) (zpowers_le.mpr htR)
  have hwR : z * r ∈ szR T₁ R₂ t ⊔ zpowers z :=
    mul_mem (mem_sup_right (mem_zpowers z)) (mem_sup_left (le_szR_mid T₁ R₂ t hr))
  have heq := hsyl.eq_of_le (le_sup_left : T₁ ⊔ zpowers t ≤ T₁ ⊔ zpowers t ⊔ zpowers (z * r))
    (sup_le hsyl.le (zpowers_le.mpr hwC))
    (hz2.to_le (sup_le (hTR.trans le_sup_left) (zpowers_le.mpr hwR)))
  have hw : z * r ∈ T₁ ⊔ zpowers t := heq ▸ mem_sup_right (mem_zpowers (z * r))
  apply hzR
  have e : z = z * r * r⁻¹ := by group
  rw [e]
  exact mul_mem (hTR hw) (inv_mem (le_szR_mid T₁ R₂ t hr))

theorem gamma_eq_zero (hG : ¬ ∃ N : Subgroup G, N.Normal ∧ N.index = 2)
    (hS : SzR2 T₁ R₂ t d) (h : SzRCoords2 T₁ R₂ t a u v φ γ c) (hc : SzRootCoords T₁ a d u v κ)
    (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1))
    (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, (κ ^ (2 ^ (a + 1) + 1)) ^ m = w)
    (hCt : ∀ P : Sylow 2 (centralizer ({t} : Set G)), Nat.card P = 2 * Nat.card T₁) : γ = 0 := by
  by_contra hγ
  obtain ⟨n, hn, hnt⟩ := h.exists_mem_normalizer_conj_t_not_mem hG hS hc ha hK hμ hCt
  exact hnt ((h.conj_t_not_mem_sup ha hK hn).2 hγ)

theorem commute_of_gamma_eq_zero (h : SzRCoords2 T₁ R₂ t a u v φ γ c) (hγ : γ = 0) :
    ∀ x ∈ T₁, ∀ r ∈ R₂, x * r = r * x := by
  intro x hx r hr
  have hxR := le_szR_left T₁ R₂ t hx
  have hrR := le_szR_mid T₁ R₂ t hr
  have h0 : v (x * r * x⁻¹ * r⁻¹) = 0 := by
    rw [h.comm x hxR r hrR, h.of_T₁ x hx, h.of_R₂ r hr, hγ]
    simp [szCommMap, zero_pow (SzRadical.two_pow_ne_zero _)]
  have h1 := h.v_inj _ (h.comm_mem x hxR r hrR) h0
  calc x * r = x * r * x⁻¹ * r⁻¹ * (r * x) := by group
    _ = r * x := by rw [h1, one_mul]

theorem normalizer_le_normalizer_sup (h : SzRCoords2 T₁ R₂ t a u v φ γ c) (ha : 1 ≤ a)
    (hK : Fintype.card K = 2 ^ (2 * a + 1)) (hγ : γ = 0) :
    normalizer (szR T₁ R₂ t : Set G) ≤ normalizer ((T₁ ⊔ R₂ : Subgroup G) : Set G) := by
  subst hγ
  intro n hn
  obtain ⟨α, β, hα, -, hB⟩ := h.exists_addEquiv_of_mem_normalizer ha hK hn
  refine mem_normalizer_of_forall_inv_mul_mul_mem fun x hx => ?_
  have hxR : x ∈ szR T₁ R₂ t := sup_le_szR T₁ R₂ t hx
  have hnx : n⁻¹ * x * n ∈ szR T₁ R₂ t := (mem_normalizer_iff''.mp hn x).mp hxR
  rw [← h.thd_eq_zero_iff _ hnx, ← hα x hxR]
  exact SzRadical.thd_map_eq_zero ha hK α β hB _ ((h.thd_eq_zero_iff x hxR).mpr hx)

end SzRCoords2

theorem SzR2.inf_centralizer_sup_eq (hS : SzR2 T₁ R₂ t d)
    (hcomm : ∀ x ∈ T₁, ∀ r ∈ R₂, x * r = r * x) :
    (T₁ ⊔ R₂) ⊓ centralizer ((T₁ ⊔ R₂ : Subgroup G) : Set G) = R₂ := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxH, hxC⟩ := mem_inf.mp hx
    have h1 : ((T₁ ⊔ R₂ : Subgroup G) : Set G) = (T₁ : Set G) * (R₂ : Set G) :=
      coe_mul_of_left_le_normalizer_right T₁ R₂ hS.le_normalizer_R₂
    rw [← SetLike.mem_coe, h1] at hxH
    obtain ⟨y, hy, r, hr, rfl⟩ := hxH
    have hyA : y ∈ szA₁ T₁ := by
      refine mem_szA₁.mpr ⟨hy, mem_centralizer_iff.mpr fun w hw => ?_⟩
      have e1 := mem_centralizer_iff.mp hxC w (mem_sup_left hw)
      have e2 := hcomm w hw r hr
      have e3 : w * y * r = y * w * r := by
        calc w * y * r = w * (y * r) := by group
          _ = y * r * w := e1
          _ = y * (r * w) := by group
          _ = y * (w * r) := by rw [e2]
          _ = y * w * r := by group
      exact mul_right_cancel e3
    exact mul_mem (hS.le_R₂ hyA) hr
  · refine le_inf le_sup_right ?_
    rw [le_centralizer_iff]
    exact sup_le (fun x hx => mem_centralizer_iff.mpr fun r hr => (hcomm x hx r hr).symm)
      (fun x hx => mem_centralizer_iff.mpr fun r hr => hS.R₂_comm r hr x hx)

theorem SzRCoords2.normalizer_le_normalizer_R₂ (hS : SzR2 T₁ R₂ t d)
    (h : SzRCoords2 T₁ R₂ t a u v φ γ c) (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1))
    (hγ : γ = 0) : normalizer (szR T₁ R₂ t : Set G) ≤ normalizer (R₂ : Set G) := by
  have h1 := normalizer_le_normalizer_inf_centralizer (T₁ ⊔ R₂)
  rw [hS.inf_centralizer_sup_eq (h.commute_of_gamma_eq_zero hγ)] at h1
  exact (h.normalizer_le_normalizer_sup ha hK hγ).trans h1

end CFSG.SeitzReduction.RankOne
