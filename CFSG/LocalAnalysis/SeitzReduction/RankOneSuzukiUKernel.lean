module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiUCoords
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiY

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {K : Type*} [Field K] [Fintype K] [CharP K 2]
  {T₁ R₂ : Subgroup G} {t d : G} {a : ℕ} {u v : G → K} {κ : K} {φ : G → K × K × K} {γ c : K}

namespace SzRCoords2

theorem mem_gmsRootConjugates_of_mem_szCand (hG : ¬ ∃ N : Subgroup G, N.Normal ∧ N.index = 2)
    (hS : SzR2 T₁ R₂ t d) (h : SzRCoords2 T₁ R₂ t a u v φ γ c) (hc : SzRootCoords T₁ a d u v κ)
    (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1))
    (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, (κ ^ (2 ^ (a + 1) + 1)) ^ m = w)
    (hCt : ∀ P : Sylow 2 (centralizer ({t} : Set G)), Nat.card P = 2 * Nat.card T₁)
    {x : G} (hx : x ∈ szR T₁ R₂ t) (hxC : φ x ∈ szCand a c) :
    szA₁ T₁ ⊔ zpowers x ∈ gmsRootConjugates (szR T₁ R₂ t) (szA₁ T₁ ⊔ zpowers t) := by
  have hγ := h.gamma_eq_zero hG hS hc ha hK hμ hCt
  have hNA := h.normalizer_szR_le_normalizer_szA₁ ha hK
  obtain ⟨y, hy, hyx⟩ := h.exists_mem_normalizer_map_conj_t_eq hG hS hc ha hK hμ hCt hγ hxC
  have hyR : y⁻¹ * t * y ∈ szR T₁ R₂ t := (mem_normalizer_iff''.mp hy t).mp (mem_szR_right T₁ R₂ t)
  have heq : szA₁ T₁ ⊔ zpowers x = (szA₁ T₁ ⊔ zpowers t).map (MulAut.conj y⁻¹).toMonoidHom := by
    rw [map_conj_szA₁_sup_zpowers (hNA hy) t]
    exact h.szA₁_sup_zpowers_eq_of_map_eq hx hyR hyx.symm
  exact ⟨y, heq, heq ▸ map_conj_szA_le_szR hy⟩

theorem map_eq_of_map_conj_eq (h : SzRCoords2 T₁ R₂ t a u v φ γ c) (ha : 1 ≤ a)
    (hK : Fintype.card K = 2 ^ (2 * a + 1)) {n : G} (hn : n ∈ normalizer (szR T₁ R₂ t : Set G))
    {x : G} (hx : x ∈ szR T₁ R₂ t) (h0 : φ x ≠ 0)
    (hfix : (szA₁ T₁ ⊔ zpowers x).map (MulAut.conj n).toMonoidHom = szA₁ T₁ ⊔ zpowers x) :
    φ (n * x * n⁻¹) = φ x := by
  have hn' : n⁻¹ ∈ normalizer (szA₁ T₁ : Set G) :=
    h.normalizer_szR_le_normalizer_szA₁ ha hK (inv_mem hn)
  have h1 := map_conj_szA₁_sup_zpowers hn' x
  simp only [inv_inv] at h1
  rw [h1] at hfix
  have hnx : n * x * n⁻¹ ∈ szR T₁ R₂ t := by
    have := (mem_normalizer_iff''.mp (inv_mem hn) x).mp hx
    rwa [inv_inv] at this
  exact h.map_eq_of_szA₁_sup_zpowers_eq hx (by
    intro h00
    have h4 := (h.ker _ hnx).mp h00
    have h5 : x ∈ szA₁ T₁ := by
      have h6 := (mem_normalizer_iff.mp hn' _).mp h4
      simpa [mul_assoc] using h6
    exact h0 ((h.ker x hx).mpr h5)) hfix.symm

theorem map_ne_zero_of_thd_eq_one {x : G} (hx : (φ x).2.2 = 1) : φ x ≠ 0 := by
  intro h0
  rw [h0] at hx
  exact zero_ne_one hx

theorem map_mul_t (h : SzRCoords2 T₁ R₂ t a u v φ γ c) {z : G} (hz : z ∈ szR T₁ R₂ t) :
    φ (z * t) = φ z + (0, 0, 1) := by
  rw [h.mul _ hz _ (mem_szR_right T₁ R₂ t), h.of_t]

theorem mem_szR_of_forall_map_conj_eq (hG : ¬ ∃ N : Subgroup G, N.Normal ∧ N.index = 2)
    (hS : SzR2 T₁ R₂ t d) (h : SzRCoords2 T₁ R₂ t a u v φ γ c) (hc : SzRootCoords T₁ a d u v κ)
    (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1))
    (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, (κ ^ (2 ^ (a + 1) + 1)) ^ m = w)
    (hCt : ∀ P : Sylow 2 (centralizer ({t} : Set G)), Nat.card P = 2 * Nat.card T₁)
    (hCA : centralizer ((szA₁ T₁ ⊔ zpowers t : Subgroup G) : Set G) ≤ T₁ ⊔ zpowers t)
    {n : G} (hn : n ∈ normalizer (szR T₁ R₂ t : Set G))
    (hfix : ∀ S ∈ gmsRootConjugates (szR T₁ R₂ t) (szA₁ T₁ ⊔ zpowers t),
      S.map (MulAut.conj n).toMonoidHom = S) : n ∈ szR T₁ R₂ t := by
  have hγ := h.gamma_eq_zero hG hS hc ha hK hμ hCt
  have hNA := h.normalizer_szR_le_normalizer_szA₁ ha hK
  have htR := mem_szR_right T₁ R₂ t
  have htA₁ : t ∈ centralizer (szA₁ T₁ : Set G) :=
    mem_centralizer_iff.mpr fun b hb => hS.t_comm b (szA₁_le T₁ hb)
  have hAΔ := szA_mem_gmsRootConjugates T₁ R₂ t
  have hnA : n ∈ normalizer ((szA₁ T₁ ⊔ zpowers t : Subgroup G) : Set G) :=
    mem_normalizer_of_map_conj_eq (hfix _ hAΔ)
  have htA : n * t * n⁻¹ ∈ szA₁ T₁ ⊔ zpowers t :=
    (mem_normalizer_iff.mp hnA t).mp (mem_sup_right (mem_zpowers t))
  obtain ⟨b, hb, z, hz, hbz⟩ := exists_mul_eq_of_mem_sup_zpowers htA₁ htA
  rcases mem_zpowers_involution_eq_one_or_eq hS.t_sq hz with hz1 | hz1
  · exfalso
    apply h.conj_t_not_mem_szA₁ hc ha hK hCt n⁻¹
    rw [inv_inv, ← hbz, hz1, mul_one]
    exact hb
  rw [hz1] at hbz
  obtain ⟨r, hr, hrb⟩ := hS.rho_surj b hb
  have hrR : r ∈ szR T₁ R₂ t := le_szR_mid T₁ R₂ t hr
  have hrY : r ∈ normalizer (szR T₁ R₂ t : Set G) := le_normalizer hrR
  set m := r⁻¹ * n with hm
  have hmY : m ∈ normalizer (szR T₁ R₂ t : Set G) := mul_mem (inv_mem hrY) hn
  have hmt : m * t * m⁻¹ = t := by
    have e1 : r * t * r⁻¹ = n * t * n⁻¹ := by
      rw [← hbz]
      calc r * t * r⁻¹ = r * t * r⁻¹ * t⁻¹ * t := by group
        _ = b * t := by rw [hrb]
    calc m * t * m⁻¹ = r⁻¹ * (n * t * n⁻¹) * r := by rw [hm]; group
      _ = r⁻¹ * (r * t * r⁻¹) * r := by rw [e1]
      _ = t := by group
  have hmfix : ∀ S ∈ gmsRootConjugates (szR T₁ R₂ t) (szA₁ T₁ ⊔ zpowers t),
      S.map (MulAut.conj m).toMonoidHom = S := by
    intro S hS'
    have hr' : S.map (MulAut.conj r⁻¹).toMonoidHom = S :=
      h.map_conj_eq_of_mem_szR hG hS hc ha hK hμ hCt hS' (inv_mem hrR)
    rw [hm, map_mul, show (MulAut.conj r⁻¹ * MulAut.conj n).toMonoidHom =
      (MulAut.conj r⁻¹).toMonoidHom.comp (MulAut.conj n).toMonoidHom from rfl, ← Subgroup.map_map,
      hfix S hS', hr']
  have hmA₁ : m ∈ normalizer (szA₁ T₁ : Set G) := hNA hmY
  have hfixφ : ∀ x ∈ szR T₁ R₂ t, φ x ∈ szCand a c → φ (m * x * m⁻¹) = φ x := fun x hx hxC =>
    h.map_eq_of_map_conj_eq ha hK hmY hx (map_ne_zero_of_thd_eq_one hxC.1)
      (hmfix _ (h.mem_gmsRootConjugates_of_mem_szCand hG hS hc ha hK hμ hCt hx hxC))
  have hcomm : ∀ b ∈ szA₁ T₁, m * b * m⁻¹ = b := by
    by_cases hc1 : c + 1 = 0
    ·
      intro b hb
      obtain ⟨r₀, hr₀, hr₀b⟩ := hS.rho_surj b hb
      have hr₀R := le_szR_mid T₁ R₂ t hr₀
      have hxR : r₀ * t ∈ szR T₁ R₂ t := mul_mem hr₀R htR
      have hxC : φ (r₀ * t) ∈ szCand a c := by
        refine ⟨by rw [h.map_mul_t hr₀R, h.of_R₂ r₀ hr₀]; simp, ?_⟩
        rw [h.map_mul_t hr₀R, h.of_R₂ r₀ hr₀, hc1]
        simp
      have h1 := hfixφ _ hxR hxC
      have hmr : m * r₀ * m⁻¹ ∈ R₂ :=
        (mem_normalizer_iff.mp (h.normalizer_le_normalizer_R₂ hS ha hK hγ hmY) r₀).mp hr₀
      rw [show m * (r₀ * t) * m⁻¹ = (m * r₀ * m⁻¹) * (m * t * m⁻¹) by group, hmt,
        h.map_mul_t (le_szR_mid T₁ R₂ t hmr), h.map_mul_t hr₀R, add_left_inj] at h1
      have h2 := congrArg (fun z : K × K × K => z.2.1) h1
      rw [h.snd_conj_R₂ hS ha hK hγ hmY hr₀, h.snd_eq r₀ hr₀R, hr₀b] at h2
      have hmb : m * b * m⁻¹ ∈ szA₁ T₁ := (mem_normalizer_iff.mp hmA₁ b).mp hb
      have h3 := (h.layerA_heq _ hmb _ hb).mp h2
      rw [mem_bot, inv_mul_eq_one] at h3
      exact h3
    ·
      have hT : ∀ y ∈ T₁, (φ (m * y * m⁻¹)).1 = u y := by
        intro y hy
        obtain ⟨r₀, hr₀, hr₀w⟩ := h.layerTwo_surj hS (u y ^ (2 ^ (a + 1) + 1) / (c + 1))
        have hyR := le_szR_left T₁ R₂ t hy
        have hr₀R := le_szR_mid T₁ R₂ t hr₀
        have hxR : y * r₀ * t ∈ szR T₁ R₂ t := mul_mem (mul_mem hyR hr₀R) htR
        have hφx : φ (y * r₀ * t) = (u y, u y ^ (2 ^ (a + 1) + 1) / (c + 1), 1) := by
          rw [h.map_mul_t (mul_mem hyR hr₀R), h.map_mul_T₁_R₂ hy hr₀, hr₀w]
          simp
        have hxC : φ (y * r₀ * t) ∈ szCand a c := by
          rw [hφx]
          refine ⟨rfl, ?_⟩
          simp only
          rw [mul_div_cancel₀ _ hc1, CharTwo.add_self_eq_zero]
        have h1 := hfixφ _ hxR hxC
        have hmy : m * y * m⁻¹ ∈ T₁ ⊔ R₂ :=
          (mem_normalizer_iff.mp (h.normalizer_le_normalizer_sup ha hK hγ hmY) y).mp
            (mem_sup_left hy)
        have hmr : m * r₀ * m⁻¹ ∈ R₂ :=
          (mem_normalizer_iff.mp (h.normalizer_le_normalizer_R₂ hS ha hK hγ hmY) r₀).mp hr₀
        rw [show m * (y * r₀ * t) * m⁻¹ = (m * y * m⁻¹) * (m * r₀ * m⁻¹) * (m * t * m⁻¹) by group,
          hmt, h.map_mul_t (mul_mem (sup_le_szR T₁ R₂ t hmy) (le_szR_mid T₁ R₂ t hmr)),
          h.mul _ (sup_le_szR T₁ R₂ t hmy) _ (le_szR_mid T₁ R₂ t hmr), h.of_R₂ _ hmr, hφx] at h1
        have h2 := congrArg Prod.fst h1
        simpa using h2
      intro b hb
      obtain ⟨l, hl⟩ := SzStartField.exists_pow_theta_succ_eq hK (v b)
      obtain ⟨y, hy, hyu, -⟩ := hc.surj l 0
      have hy2 : y ^ 2 = b := by
        have h3 := (h.layerA_heq _ (hc.sq_mem_szA₁ ha hK hy) _ hb).mp
          (by rw [(hc.sq hy).2, hyu, hl])
        rw [mem_bot, inv_mul_eq_one] at h3
        exact h3
      have hsnd : (φ (m * y * m⁻¹)).2.1 = 0 := by
        rw [h.snd_conj_T₁ hS ha hK hγ hmY hy, hmt, h.of_t]
        simp [zero_pow (SzRadical.two_pow_ne_zero _)]
      have hv := h.v_conj_sq_T₁ ha hK hγ hmY hy
      rw [hsnd, mul_zero, add_zero, hT y hy, hy2] at hv
      have hmb : m * b * m⁻¹ ∈ szA₁ T₁ := (mem_normalizer_iff.mp hmA₁ b).mp hb
      have h3 := (h.layerA_heq _ hmb _ hb).mp (by rw [hv, ← hy2, (hc.sq hy).2])
      rw [mem_bot, inv_mul_eq_one] at h3
      exact h3
  have hmt' : m * t = t * m := by
    calc m * t = m * t * m⁻¹ * m := by group
      _ = t * m := by rw [hmt]
  have hmC : m ∈ centralizer ((szA₁ T₁ ⊔ zpowers t : Subgroup G) : Set G) := by
    refine mem_centralizer_iff.mpr fun w hw => ?_
    obtain ⟨b, hb, z, hz, rfl⟩ := exists_mul_eq_of_mem_sup_zpowers htA₁ hw
    have e1 : m * b = b * m := by
      calc m * b = m * b * m⁻¹ * m := by group
        _ = b * m := by rw [hcomm b hb]
    have e2 : m * z = z * m := commute_of_mem_zpowers hz hmt'
    calc b * z * m = b * (z * m) := by group
      _ = b * (m * z) := by rw [e2]
      _ = (b * m) * z := by group
      _ = (m * b) * z := by rw [e1]
      _ = m * (b * z) := by group
  have hmR : m ∈ szR T₁ R₂ t :=
    sup_le (le_szR_left T₁ R₂ t) (zpowers_le.mpr htR) (hCA hmC)
  have e : n = r * m := by rw [hm]; group
  rw [e]
  exact mul_mem hrR hmR

end SzRCoords2

end CFSG.SeitzReduction.RankOne
