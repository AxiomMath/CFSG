module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryNotSylowBasic
public import CFSG.GH74.GLS.Bg.Local.Transfer1515
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryChar

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools CFSG.LocalAnalysis

theorem mem_normalizer_sup_of_mem_inf {G : Type*} [Group G] {H K : Subgroup G} {g : G}
    (hH : g ∈ normalizer (H : Set G)) (hK : g ∈ normalizer (K : Set G)) :
    g ∈ normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  have key : ∀ g' ∈ normalizer (H : Set G) ⊓ normalizer (K : Set G), ∀ x ∈ H ⊔ K,
      g' * x * g'⁻¹ ∈ H ⊔ K := by
    intro g' hg' x hx
    have hle : H ⊔ K ≤ (H ⊔ K).comap (MulAut.conj g').toMonoidHom := by
      refine sup_le (fun y hy => mem_comap.mpr ?_) (fun y hy => mem_comap.mpr ?_)
      · have h1 : g' * y * g'⁻¹ ∈ H := (mem_normalizer_iff.mp (mem_inf.mp hg').1 y).mp hy
        simpa [MulAut.conj_apply] using (le_sup_left : H ≤ H ⊔ K) h1
      · have h1 : g' * y * g'⁻¹ ∈ K := (mem_normalizer_iff.mp (mem_inf.mp hg').2 y).mp hy
        simpa [MulAut.conj_apply] using (le_sup_right : K ≤ H ⊔ K) h1
    simpa [MulAut.conj_apply] using hle hx
  have hg : g ∈ normalizer (H : Set G) ⊓ normalizer (K : Set G) := mem_inf.mpr ⟨hH, hK⟩
  refine mem_normalizer_iff.mpr fun x => ⟨key g hg x, fun hx => ?_⟩
  have h1 := key g⁻¹ (inv_mem hg) _ hx
  simpa [mul_assoc] using h1

@[expose] def U3NotSylowNcycInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ : Subgroup G),
    U3Start G L f t T → (∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) →
    U3R2 G L (szT₁ L T) R₂ t f → (¬ ∃ b ∈ T, ∀ s ∈ T, ∃ k : ℤ, (b ^ k)⁻¹ * s ∈ szT₁ L T) →
    ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = T ⊔ R₂

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem mem_sup_zpowers_of_sq_mem_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hcyc : ∃ b ∈ T, ∀ s ∈ T, ∃ k : ℤ, (b ^ k)⁻¹ * s ∈ szT₁ L T) {s : G} (hs : s ∈ T)
    (hs2 : s ^ 2 ∈ szT₁ L T) : s ∈ szT₁ L T ⊔ zpowers t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨htT, -, -, hTN₁, hdisj, -, -⟩ := h.start_of_card_sylow hS2
  set N₁ := (szT₁ L T).subgroupOf T with hN₁def
  have hN₁ : N₁.Normal := (normal_subgroupOf_iff_le_normalizer (szT₁_le_left L T)).mpr hTN₁
  obtain ⟨b, hbT, hb⟩ := hcyc
  have hQcyc : IsCyclic (T ⧸ N₁) := ⟨⟨QuotientGroup.mk ⟨b, hbT⟩, fun q => by
    obtain ⟨⟨s', hs'⟩, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := hb s' hs'
    refine ⟨k, ?_⟩
    show (QuotientGroup.mk ⟨b, hbT⟩ : T ⧸ N₁) ^ k = QuotientGroup.mk ⟨s', hs'⟩
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq, hN₁def, mem_subgroupOf]
    simpa using hk⟩⟩
  have hone : ∀ y : T, (QuotientGroup.mk y : T ⧸ N₁) = 1 ↔ (y : G) ∈ szT₁ L T := fun y => by
    rw [QuotientGroup.eq_one_iff, hN₁def, mem_subgroupOf]
  have ht1 : t ≠ 1 := by
    intro h1
    have := h.inv
    rw [h1, orderOf_one] at this
    exact absurd this (by norm_num)
  have htQ : (QuotientGroup.mk ⟨t, htT⟩ : T ⧸ N₁) ≠ 1 := by
    rw [Ne, hone]
    intro htT₁
    have h1 : t ∈ szT₁ L T ⊓ zpowers t := mem_inf.mpr ⟨htT₁, mem_zpowers t⟩
    rw [hdisj, mem_bot] at h1
    exact ht1 h1
  have ht2 : orderOf (QuotientGroup.mk ⟨t, htT⟩ : T ⧸ N₁) = 2 := by
    refine orderOf_eq_prime ?_ htQ
    rw [← QuotientGroup.mk_pow, hone]
    simp only [SubgroupClass.coe_pow]
    rw [h.sq_eq_one]
    exact one_mem _
  by_cases hs1 : (QuotientGroup.mk ⟨s, hs⟩ : T ⧸ N₁) = 1
  · exact mem_sup_left ((hone _).mp hs1)
  have hs2' : orderOf (QuotientGroup.mk ⟨s, hs⟩ : T ⧸ N₁) = 2 := by
    refine orderOf_eq_prime ?_ hs1
    rw [← QuotientGroup.mk_pow, hone]
    simpa using hs2
  have hcyc' : IsCyclic (⊤ : Subgroup (T ⧸ N₁)) := Subgroup.topEquiv.isCyclic.mpr hQcyc
  have heq := eq_of_orderOf_eq_two_of_isCyclic_subgroup hcyc' (mem_top _) (mem_top _) hs2' ht2
  rw [QuotientGroup.eq, hN₁def, mem_subgroupOf] at heq
  have h1 : s⁻¹ * t ∈ szT₁ L T := by simpa using heq
  rw [show s = t * (s⁻¹ * t)⁻¹ by group]
  exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left (inv_mem h1))

theorem mem_sup_zpowers_of_involution_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hcyc : ∃ b ∈ T, ∀ s ∈ T, ∃ k : ℤ, (b ^ k)⁻¹ * s ∈ szT₁ L T) {w : G}
    (hw : w ∈ centralizer ({t} : Set G)) (hw2 : w ^ 2 = 1) : w ∈ L ⊔ zpowers t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTsyl : IsSylowOf 2 T (centralizer ({t} : Set G)) := by
    obtain ⟨P, hP⟩ := h.sylow
    exact ⟨P, by rw [hP, subgroupOf_map_subtype, inf_eq_left.mpr h.le]⟩
  have hP : IsPGroup 2 (zpowers w) :=
    CFSG.GH74.Uniqueness.Bender.isPGroup_two_zpowers_of_mul_self_eq_one (by rw [← sq, hw2])
  obtain ⟨c, hcC, hc⟩ := exists_conj_mem_of_isSylowOf hTsyl (zpowers_le.mpr hw) hP
  have hcw : c⁻¹ * w * c ∈ T := hc w (mem_zpowers w)
  have hcw2 : (c⁻¹ * w * c) ^ 2 ∈ szT₁ L T := by
    rw [show (c⁻¹ * w * c) ^ 2 = c⁻¹ * w ^ 2 * c by rw [sq, sq]; group, hw2, mul_one,
      inv_mul_cancel]
    exact one_mem _
  have h1 := h.mem_sup_zpowers_of_sq_mem_of_card_sylow hS2 hcyc hcw hcw2
  obtain ⟨y, hy, z, hz, hyz⟩ := exists_mul_eq_of_mem_sup_zpowers h.mem_centralizer_szT₁ h1
  have hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G) :=
    (CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality
      h.setting.standardSetting.standard h.mem h.inv).1
  have hcz : c * z = z * c := commute_of_mem_zpowers hz (mem_centralizer_singleton_iff.mp hcC)
  have e : w = (c * y * c⁻¹) * z := by
    calc w = c * (c⁻¹ * w * c) * c⁻¹ := by group
      _ = c * (y * z) * c⁻¹ := by rw [hyz]
      _ = c * y * c⁻¹ * (c * z * c⁻¹) := by group
      _ = c * y * c⁻¹ * z := by rw [hcz, mul_inv_cancel_right]
  rw [e]
  exact mul_mem (mem_sup_left ((mem_normalizer_iff.mp (hCN hcC) y).mp (szT₁_le_right L T hy)))
    (mem_sup_right hz)

theorem exists_mul_of_mem_szR {R₂ : Subgroup G} (hR : U3R2 G L (szT₁ L T) R₂ t f) {r : G}
    (hr : r ∈ szR (szT₁ L T) R₂ t) : ∃ w ∈ szT₁ L T ⊔ R₂, ∃ z ∈ zpowers t, w * z = r := by
  have hzN : zpowers t ≤ normalizer ((szT₁ L T ⊔ R₂ : Subgroup G) : Set G) :=
    zpowers_le.mpr hR.t_mem_normalizer_sup
  have hr' : r ∈ (((szT₁ L T ⊔ R₂) ⊔ zpowers t : Subgroup G) : Set G) := hr
  rw [coe_mul_of_right_le_normalizer_left _ _ hzN] at hr'
  exact hr'

section Certificates

theorem s₁_facts_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) :
    szR (szT₁ L T) R₂ t = u3R₁ L T t ∧
      T ⊔ R₂ ≤ normalizer (szR (szT₁ L T) R₂ t : Set G) ∧
      T ⊔ R₂ ≤ normalizer (szA₁ (szT₁ L T) : Set G) ∧
      szR (szT₁ L T) R₂ t ≤ T ⊔ R₂ ∧
      T ⊔ R₂ ≤ normalizer ((szT₁ L T ⊔ R₂ : Subgroup G) : Set G) ∧
      T ⊓ (szT₁ L T ⊔ R₂) ≤ szT₁ L T := by
  obtain ⟨hR₁, -, -, hNR₁, hNR₂, -⟩ := h.u3R2_canonical_of_card_sylow hS2 hR
  obtain ⟨htT, -, -, hTN₁, -, -, -⟩ := h.start_of_card_sylow hS2
  have hTA : T ≤ normalizer (szA L T t : Set G) :=
    Subgroup.le_normalizer.trans (h.normalizer_le_normalizer_szA_of_card_sylow hS2)
  have hR₂A₁ : R₂ ≤ normalizer (szA₁ (szT₁ L T) : Set G) :=
    le_trans (fun r hr => mem_centralizer_iff.mpr fun a ha => hR.comm a (hR.le ha) r hr)
      (centralizer_le_normalizer _)
  refine ⟨hR₁, sup_le (hTA.trans hNR₁) ((le_szR_mid _ _ _).trans Subgroup.le_normalizer),
    sup_le (hTA.trans (h.normalizer_szA_le_normalizer_szA₁_of_card_sylow hS2)) hR₂A₁,
    sup_le (sup_le ((szT₁_le_left L T).trans le_sup_left) le_sup_right)
      (zpowers_le.mpr (mem_sup_left htT)),
    sup_le (fun s hs => mem_normalizer_sup_of_mem_inf (hTN₁ hs) (hNR₂ (hTA hs)))
      ((le_sup_right : R₂ ≤ szT₁ L T ⊔ R₂).trans Subgroup.le_normalizer), ?_⟩
  rintro x ⟨hxT, hxH⟩
  obtain ⟨y, hy, r, hr, rfl⟩ := hR.mem_sup_iff.mp hxH
  have hrT : r ∈ T := by
    have := mul_mem (inv_mem (szT₁_le_left L T hy)) hxT
    rwa [inv_mul_cancel_left] at this
  have hrA := hR.rho_ker r hr (mem_centralizer_singleton_iff.mp (h.le hrT))
  exact mul_mem hy (szA₁_le _ hrA)

theorem exists_mul_of_mem_s₁_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) {x : G} (hx : x ∈ T ⊔ R₂) :
    ∃ s ∈ T, ∃ r ∈ szR (szT₁ L T) R₂ t, s * r = x := by
  obtain ⟨-, hS₁N, -, hR₁S₁, -, -⟩ := h.s₁_facts_of_card_sylow hS2 hR
  have hTN : T ≤ normalizer (szR (szT₁ L T) R₂ t : Set G) := le_sup_left.trans hS₁N
  have hsup : T ⊔ R₂ = T ⊔ szR (szT₁ L T) R₂ t :=
    le_antisymm (sup_le_sup_left (le_szR_mid _ _ _) _) (sup_le le_sup_left hR₁S₁)
  rw [hsup, ← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right T _ hTN] at hx
  exact hx

theorem mem_szR_of_sq_mem_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f)
    (hcyc : ∃ b ∈ T, ∀ s ∈ T, ∃ k : ℤ, (b ^ k)⁻¹ * s ∈ szT₁ L T) {x : G} (hx : x ∈ T ⊔ R₂)
    (hx2 : x ^ 2 ∈ szT₁ L T ⊔ R₂) : x ∈ szR (szT₁ L T) R₂ t := by
  obtain ⟨-, -, -, -, hS₁H, hTH⟩ := h.s₁_facts_of_card_sylow hS2 hR
  obtain ⟨s, hs, r, hr, rfl⟩ := h.exists_mul_of_mem_s₁_of_card_sylow hS2 hR hx
  obtain ⟨w, hw, z, hz, rfl⟩ := exists_mul_of_mem_szR hR hr
  have hsz : s * z = z * s := commute_of_mem_zpowers hz (mem_centralizer_singleton_iff.mp (h.le hs))
  have hzz : z * z = 1 := by
    rcases mem_zpowers_involution_eq_one_or_eq hR.t_sq hz with hz1 | hz1
    · rw [hz1, mul_one]
    · rw [hz1, ← sq, hR.t_sq]
  have hw1 : s⁻¹ * w * s ∈ szT₁ L T ⊔ R₂ :=
    (mem_normalizer_iff''.mp (hS₁H (mem_sup_left hs)) w).mp hw
  have hw2 : z * w * z⁻¹ ∈ szT₁ L T ⊔ R₂ :=
    (mem_normalizer_iff.mp (zpowers_le.mpr hR.t_mem_normalizer_sup hz) w).mp hw
  have e : (s * (w * z)) ^ 2 = s ^ 2 * ((s⁻¹ * w * s) * (z * w * z⁻¹)) := by
    calc (s * (w * z)) ^ 2 = s * w * (z * s) * w * z := by rw [sq]; group
      _ = s * w * (s * z) * w * z := by rw [hsz]
      _ = s ^ 2 * ((s⁻¹ * w * s) * (z * w * z⁻¹)) * (z * z) := by rw [sq]; group
      _ = s ^ 2 * ((s⁻¹ * w * s) * (z * w * z⁻¹)) := by rw [hzz, mul_one]
  have hs2 : s ^ 2 ∈ szT₁ L T := by
    refine hTH ⟨pow_mem hs 2, ?_⟩
    have := mul_mem hx2 (inv_mem (mul_mem hw1 hw2))
    rwa [e, mul_inv_cancel_right] at this
  have hsR : s ∈ szR (szT₁ L T) R₂ t :=
    sup_le ((le_szR_left _ _ _)) (zpowers_le.mpr (mem_szR_right _ _ _))
      (h.mem_sup_zpowers_of_sq_mem_of_card_sylow hS2 hcyc hs hs2)
  exact mul_mem hsR hr

theorem conj_not_mem_sup_of_isCyclic_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f)
    (hcyc : ∃ b ∈ T, ∀ s ∈ T, ∃ k : ℤ, (b ^ k)⁻¹ * s ∈ szT₁ L T)
    (hS : ∃ S : Sylow 2 G, (S : Subgroup G) = T ⊔ R₂) (g : G) :
    g⁻¹ * t * g ∉ szT₁ L T ⊔ R₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hxH
  obtain ⟨hR₁, -, hS₁A₁, hR₁S₁, -, hTH⟩ := h.s₁_facts_of_card_sylow hS2 hR
  obtain ⟨htT, -, -, -, hdisj, -, -⟩ := h.start_of_card_sylow hS2
  obtain ⟨S, hSeq⟩ := hS
  have hSsyl : IsSylowOf 2 (T ⊔ R₂) ⊤ := by
    refine isSylowOf_iff.mpr ⟨le_top, hSeq ▸ S.isPGroup', ?_⟩
    rw [relIndex_top_right, ← hSeq]
    exact S.not_dvd_index
  have hA : ∀ a ∈ szA₁ (szT₁ L T), a * (g⁻¹ * t * g) = g⁻¹ * t * g * a := fun a ha =>
    hR.comm_of_mem_sup (hR.le ha) hxH
  obtain ⟨g', hg'N, hg't⟩ := h.exists_normalizer_szA₁_conj_of_inner_of_card_sylow hS2
    (fun w hw hw2 => h.mem_sup_zpowers_of_involution_of_card_sylow hS2 hcyc hw hw2) hA
  have hcomm : ∀ r ∈ szR (szT₁ L T) R₂ t, ∀ r' ∈ szR (szT₁ L T) R₂ t,
      r * r' * r⁻¹ * r'⁻¹ ∈ szA₁ (szT₁ L T) := by
    rw [hR₁]
    intro r hr r' hr'
    exact h.comm_mem_szA₁_of_mem_u3R₁_of_card_sylow hS2 hr hr'
  have hwc : ∀ k ∈ normalizer (szA₁ (szT₁ L T) : Set G),
      (∀ r ∈ szR (szT₁ L T) R₂ t, k⁻¹ * r * k ∈ T ⊔ R₂) →
        ∀ r ∈ szR (szT₁ L T) R₂ t, k⁻¹ * r * k ∈ szR (szT₁ L T) R₂ t := by
    intro k hk hkS r hr
    refine h.mem_szR_of_sq_mem_of_card_sylow hS2 hR hcyc (hkS r hr) ?_
    have hr2 : r ^ 2 ∈ szA₁ (szT₁ L T) := by
      rw [hR₁] at hr
      exact h.sq_mem_szA₁_of_mem_u3R₁_of_card_sylow hS2 hr
    rw [show (k⁻¹ * r * k) ^ 2 = k⁻¹ * r ^ 2 * k by rw [sq, sq]; group]
    exact mem_sup_left (szA₁_le _ ((mem_normalizer_iff''.mp hk _).mp hr2))
  have hxR : g'⁻¹ * t * g' ∈ szR (szT₁ L T) R₂ t := by
    rw [hg't]
    exact sup_le_szR _ _ _ hxH
  obtain ⟨n, hnN, hnx⟩ := exists_mem_normalizer_inv_mul_mem_of_weakClosed hSsyl hS₁A₁ hR₁S₁
    hcomm hwc (mem_szR_right _ _ _) hg'N hxR
  have hnt : n⁻¹ * t * n ∈ szT₁ L T ⊔ R₂ := by
    have e : n⁻¹ * t * n = (g⁻¹ * t * g) * ((g'⁻¹ * t * g')⁻¹ * (n⁻¹ * t * n)) := by
      rw [hg't]; group
    rw [e]
    exact mul_mem hxH (mem_sup_left (szA₁_le _ hnx))
  have hnH := (mem_inf.mp ((h.char_of_card_sylow hS2 hR).2.2.2 hnN)).1
  have htH : t ∈ szT₁ L T ⊔ R₂ := (mem_normalizer_iff''.mp hnH t).mpr hnt
  have h1 : t ∈ szT₁ L T ⊓ zpowers t := mem_inf.mpr ⟨hTH ⟨htT, htH⟩, mem_zpowers t⟩
  rw [hdisj, mem_bot] at h1
  have h2 := h.inv
  rw [h1, orderOf_one] at h2
  exact absurd h2 (by norm_num)

theorem not_isSylow_S₁_of_isCyclic_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f)
    (hcyc : ∃ b ∈ T, ∀ s ∈ T, ∃ k : ℤ, (b ^ k)⁻¹ * s ∈ szT₁ L T) :
    ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = T ⊔ R₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hS
  have hconj := h.conj_not_mem_sup_of_isCyclic_of_card_sylow hS2 hR hcyc hS
  obtain ⟨S, hSeq⟩ := hS
  obtain ⟨-, -, -, -, hS₁H, -⟩ := h.s₁_facts_of_card_sylow hS2 hR
  obtain ⟨htT, -⟩ := h.start_of_card_sylow hS2
  have hG : IsSimpleGroup G := h.setting.1
  obtain ⟨a₀, b₀, hab⟩ : ∃ a b : G, a * b ≠ b * a := h.setting.2.1
  have htH : t ∉ szT₁ L T ⊔ R₂ := fun ht => hconj 1 (by simpa using ht)
  have hzN : zpowers t ≤ normalizer ((szT₁ L T ⊔ R₂ : Subgroup G) : Set G) :=
    zpowers_le.mpr hR.t_mem_normalizer_sup
  have hP : IsPGroup 2 (T ⊔ R₂ : Subgroup G) := hSeq ▸ S.isPGroup'
  have hPidx : ¬ 2 ∣ (T ⊔ R₂).index := hSeq ▸ S.not_dvd_index
  have hcycP : ∃ b ∈ T ⊔ R₂, ∀ s ∈ T ⊔ R₂, ∃ k : ℤ, (b ^ k)⁻¹ * s ∈ szT₁ L T ⊔ R₂ := by
    obtain ⟨b, hbT, hb⟩ := hcyc
    refine ⟨b, mem_sup_left hbT, fun x hx => ?_⟩
    obtain ⟨s, hs, r, hr, rfl⟩ := h.exists_mul_of_mem_s₁_of_card_sylow hS2 hR hx
    obtain ⟨w, hw, z, hz, rfl⟩ := exists_mul_of_mem_szR hR hr
    have hzT : z ∈ T := zpowers_le.mpr htT hz
    obtain ⟨k, hk⟩ := hb (s * z) (mul_mem hs hzT)
    refine ⟨k, ?_⟩
    have hw' : z⁻¹ * w * z ∈ szT₁ L T ⊔ R₂ :=
      (mem_normalizer_iff''.mp (hzN hz) w).mp hw
    rw [show (b ^ k)⁻¹ * (s * (w * z)) = (b ^ k)⁻¹ * (s * z) * (z⁻¹ * w * z) by group]
    exact mul_mem (mem_sup_left hk) hw'
  rcases CFSG.GH74.GLS.Bg.Thompson.thompson_transfer_1515 (p := 2) (P := T ⊔ R₂)
      (Q := szT₁ L T ⊔ R₂) (u := t) hP hPidx
      (fun s hs q hq => (mem_normalizer_iff.mp (hS₁H hs) q).mp hq) hcycP (mem_sup_left htT) htH
      (fun g k _ => by
        rw [pow_mul, h.sq_eq_one, one_pow, mul_one, inv_mul_cancel]
        exact one_mem _)
      (fun g hgP _ => by
        have hy2 : (g⁻¹ * t * g) ^ 2 ∈ szT₁ L T ⊔ R₂ := by
          rw [show (g⁻¹ * t * g) ^ 2 = g⁻¹ * t ^ 2 * g by rw [sq, sq]; group, h.sq_eq_one,
            mul_one, inv_mul_cancel]
          exact one_mem _
        obtain ⟨w, hw, z, hz, hwz⟩ := exists_mul_of_mem_szR hR
          (h.mem_szR_of_sq_mem_of_card_sylow hS2 hR hcyc hgP hy2)
        rcases mem_zpowers_involution_eq_one_or_eq hR.t_sq hz with hz1 | hz1
        · left
          rw [← hwz, hz1, mul_one]
          exact hw
        · right
          rw [← hwz, hz1]
          have := (mem_normalizer_iff''.mp (hzN (mem_zpowers t)) w).mp hw
          rwa [show t⁻¹ * w * t = t⁻¹ * (w * t) by group] at this)
    with ⟨N, hN, hNcyc, -, htN⟩ | ⟨g, hgQ, -⟩
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (H := N) with hN1 | hN1
    · apply hab
      have : IsCyclic (G ⧸ N) := hNcyc
      have hcomm := (QuotientGroup.mk' N).isMulCommutative_of_isCyclic_of_ker_le_center (by
        rw [QuotientGroup.ker_mk', hN1]
        exact bot_le)
      exact hcomm.is_comm.comm a₀ b₀
    · exact htN (hN1 ▸ mem_top t)
  · exact hconj g hgQ

end Certificates

end U3Start

end CFSG.SeitzReduction.RankOne
