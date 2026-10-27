module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmsExt

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools

theorem gmf_mem_sup_zpowers {G : Type} [Group G] [Finite G] {F : Subgroup G} {v : G}
    (hF : F ≤ centralizer ({v} : Set G)) {b : G} (hb : b ∈ F ⊔ zpowers v) :
    ∃ e ∈ zpowers v, ∃ c ∈ F, e * c = b := by
  have hvN : v ∈ normalizer (F : Set G) :=
    mem_normalizer_of_forall_inv_mul_mul_mem fun e he => by
      have hec := mem_centralizer_singleton_iff.mp (hF he)
      rw [show v⁻¹ * e * v = e by
        calc v⁻¹ * e * v = v⁻¹ * (e * v) := by group
          _ = v⁻¹ * (v * e) := by rw [hec]
          _ = e := by group]
      exact he
  rw [sup_comm] at hb
  exact ncyc_exists_mul_of_mem_sup (zpowers_le.mpr hvN) hb

namespace U3C1OuterSwapHigh

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
  {T R₂ D : Subgroup G} {d : G} {V U U₁ : Subgroup G} {w s : G} {P : Subgroup G}
  (hW : U3C1OuterSwapHigh G L f t T R₂ D d V U U₁ w s P)
include hW

theorem gmf_F_le_S₀ : U₁ ⊓ centralizer ({t * w} : Set G) ≤
    swapS₂ P U T ⊓ centralizer ({t * w} : Set G) := fun _ hx =>
  mem_inf.mpr ⟨hW.le_S₂ (mem_sup_left (hW.level.U₁_le (mem_inf.mp hx).1)), (mem_inf.mp hx).2⟩

theorem gmf_tw_mem_S₀ : t * w ∈ swapS₂ P U T ⊓ centralizer ({t * w} : Set G) :=
  mem_inf.mpr ⟨hW.le_S₂ (mem_sup_right hW.tw_mem), mem_centralizer_singleton_iff.mpr rfl⟩

theorem gmf_A_le_S₀ : (U₁ ⊓ centralizer ({t * w} : Set G)) ⊔ zpowers (t * w) ≤
    swapS₂ P U T ⊓ centralizer ({t * w} : Set G) :=
  sup_le hW.gmf_F_le_S₀ (zpowers_le.mpr hW.gmf_tw_mem_S₀)

theorem gmf_A_comm {a b : G} (ha : a ∈ (U₁ ⊓ centralizer ({t * w} : Set G)) ⊔ zpowers (t * w))
    (hb : b ∈ (U₁ ⊓ centralizer ({t * w} : Set G)) ⊔ zpowers (t * w)) : a * b = b * a := by
  set F := U₁ ⊓ centralizer ({t * w} : Set G) with hFdef
  have hFC : F ≤ centralizer ({t * w} : Set G) := inf_le_right
  have hcommF : ∀ e ∈ zpowers (t * w), ∀ c ∈ F, e * c = c * e := fun e he c hc =>
    (commute_of_mem_zpowers he (mem_centralizer_singleton_iff.mp (mem_inf.mp hc).2)).symm
  obtain ⟨e₁, he₁, c₁, hc₁, rfl⟩ := gmf_mem_sup_zpowers hFC ha
  obtain ⟨e₂, he₂, c₂, hc₂, rfl⟩ := gmf_mem_sup_zpowers hFC hb
  have h1 : e₁ * e₂ = e₂ * e₁ := by
    obtain ⟨k₁, rfl⟩ := mem_zpowers_iff.mp he₁
    obtain ⟨k₂, rfl⟩ := mem_zpowers_iff.mp he₂
    rw [← zpow_add, ← zpow_add, add_comm]
  calc e₁ * c₁ * (e₂ * c₂) = e₁ * (c₁ * e₂) * c₂ := by group
    _ = e₁ * (e₂ * c₁) * c₂ := by rw [hcommF e₂ he₂ c₁ hc₁]
    _ = (e₁ * e₂) * (c₁ * c₂) := by group
    _ = (e₂ * e₁) * (c₂ * c₁) := by rw [h1, hW.F_comm hc₁ hc₂]
    _ = e₂ * (e₁ * c₂) * c₁ := by group
    _ = e₂ * (c₂ * e₁) * c₁ := by rw [hcommF e₁ he₁ c₂ hc₂]
    _ = e₂ * c₂ * (e₁ * c₁) := by group

theorem gmf_A_sq {b : G} (hb : b ∈ (U₁ ⊓ centralizer ({t * w} : Set G)) ⊔ zpowers (t * w)) :
    b ^ 2 = 1 := by
  set F := U₁ ⊓ centralizer ({t * w} : Set G) with hFdef
  obtain ⟨e, he, c, hc, rfl⟩ := gmf_mem_sup_zpowers (inf_le_right : F ≤ _) hb
  have hec : Commute e c :=
    (commute_of_mem_zpowers he (mem_centralizer_singleton_iff.mp (mem_inf.mp hc).2)).symm
  rw [hec.mul_pow, hW.F_sq hc, mul_one]
  rcases mem_zpowers_involution_eq_one_or_eq hW.tw_sq he with h1 | h1
  · rw [h1, one_pow]
  · rw [h1, hW.tw_sq]

theorem gmf_szA₁_le_F : szA₁ (szT₁ L T) ≤ U₁ ⊓ centralizer ({t * w} : Set G) := fun a ha =>
  mem_inf.mpr ⟨hW.T₁_le_U₁ (szA₁_le _ ha), mem_centralizer_singleton_iff.mpr
    ((hW.step.start.outer_facts_of_card_sylow hW.step.card_sylow hW.tw_mem hW.tw_sq
      hW.tw_not_mem).2.1 a ha).symm⟩

theorem gmf_conj_F {g : G} (hg : g ∈ swapS₂ P U T ⊓ centralizer ({t * w} : Set G)) {x : G}
    (hx : x ∈ U₁ ⊓ centralizer ({t * w} : Set G)) :
    g * x * g⁻¹ ∈ U₁ ⊓ centralizer ({t * w} : Set G) := by
  obtain ⟨hgS, hgC⟩ := mem_inf.mp hg
  obtain ⟨hxU, hxC⟩ := mem_inf.mp hx
  have hg' := mem_centralizer_singleton_iff.mp hgC
  have hx' := mem_centralizer_singleton_iff.mp hxC
  refine mem_inf.mpr ⟨hW.conj_U₁ hgS hxU, mem_centralizer_singleton_iff.mpr ?_⟩
  have hgi : g⁻¹ * (t * w) = (t * w) * g⁻¹ := (Commute.inv_left hg').eq
  calc g * x * g⁻¹ * (t * w) = g * x * ((t * w) * g⁻¹) := by rw [mul_assoc, hgi, ← mul_assoc]
    _ = g * (x * (t * w)) * g⁻¹ := by group
    _ = g * ((t * w) * x) * g⁻¹ := by rw [hx']
    _ = (g * (t * w)) * x * g⁻¹ := by group
    _ = (t * w) * g * x * g⁻¹ := by rw [hg']
    _ = (t * w) * (g * x * g⁻¹) := by group

theorem gmf_inv_cases {x : G} (hxS : x ∈ U ⊔ T) (hxv : x * (t * w) = (t * w) * x)
    (hx2 : x ^ 2 = 1) :
    x ∈ (U₁ ⊓ centralizer ({t * w} : Set G)) ⊔ zpowers (t * w) ∨
      x * t⁻¹ ∈ szA₁ (szT₁ L T) ∨ x * w⁻¹ ∈ szA₁ (szT₁ L T) := by
  have hS := hW.step
  have hL := hW.level
  have h := hS.start
  obtain ⟨K, _, _, _, v, μ, hK, hc, hμ⟩ := hS.exists_coords
  have hcF : ∀ u ∈ U₁, u * (t * w) = (t * w) * u → u ∈ U₁ ⊓ centralizer ({t * w} : Set G) :=
    fun u hu hcomm => mem_inf.mpr ⟨hu, mem_centralizer_singleton_iff.mpr hcomm⟩
  have hwt := hW.wt_comm
  have htv : t * (t * w) = (t * w) * t := by rw [mul_assoc t w t, hwt]
  have hwv : w * (t * w) = (t * w) * w := by rw [← mul_assoc, hwt]
  rcases hW.mem_cases hxS with h1 | h1 | h1 | ⟨n, h1⟩
  · exact Or.inl (mem_sup_left (hcF x h1 hxv))
  · right; left
    have hu2 : (x * t⁻¹ * t) ^ 2 = 1 := by rw [inv_mul_cancel_right]; exact hx2
    have huV : x * t⁻¹ ∈ V := hL.muOne_mem_V_of_sq_eq_one hS hc hW.mu hK hμ h1 hu2
    have hucomm : x * t⁻¹ * (t * w) = (t * w) * (x * t⁻¹) := by
      have htv' : t⁻¹ * (t * w) = (t * w) * t⁻¹ := (Commute.inv_left htv).eq
      calc x * t⁻¹ * (t * w) = x * (t⁻¹ * (t * w)) := by group
        _ = x * ((t * w) * t⁻¹) := by rw [htv']
        _ = (x * (t * w)) * t⁻¹ := by group
        _ = (t * w) * x * t⁻¹ := by rw [hxv]
        _ = (t * w) * (x * t⁻¹) := by group
    have hinv := hW.tw_inv huV
    have huu : (x * t⁻¹)⁻¹ = x * t⁻¹ := by
      rw [← hinv, ← hucomm, mul_inv_cancel_right]
    refine hS.conf.omega _ huV ?_
    rw [sq]
    nth_rewrite 2 [← huu]
    exact mul_inv_cancel _
  · right; right
    have hucomm : x * w⁻¹ * (t * w) = (t * w) * (x * w⁻¹) := by
      have hwv' : w⁻¹ * (t * w) = (t * w) * w⁻¹ := (Commute.inv_left hwv).eq
      calc x * w⁻¹ * (t * w) = x * (w⁻¹ * (t * w)) := by group
        _ = x * ((t * w) * w⁻¹) := by rw [hwv']
        _ = (x * (t * w)) * w⁻¹ := by group
        _ = (t * w) * x * w⁻¹ := by rw [hxv]
        _ = (t * w) * (x * w⁻¹) := by group
    have huF := hcF _ h1 hucomm
    have hu2 := hW.F_sq huF
    have hww : w * w = 1 := by rw [← sq, hW.w_sq]
    have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
    have huw : (x * w⁻¹) * w = w * (x * w⁻¹) := by
      have huu : (x * w⁻¹)⁻¹ = x * w⁻¹ := by
        rw [inv_eq_iff_mul_eq_one, ← sq, hu2]
      have hxx : x * x = 1 := by rw [← sq, hx2]
      have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
      calc (x * w⁻¹) * w = x := by group
        _ = w * (w⁻¹ * x) := by group
        _ = w * (x * w⁻¹)⁻¹ := by rw [mul_inv_rev, inv_inv, hxinv, hwinv]
        _ = w * (x * w⁻¹) := by rw [huu]
    have hut : (x * w⁻¹) * t = t * (x * w⁻¹) := by
      have e1 : t = (t * w) * w⁻¹ := by group
      have huw' : (x * w⁻¹) * w⁻¹ = w⁻¹ * (x * w⁻¹) := (Commute.inv_right huw).eq
      calc (x * w⁻¹) * t = (x * w⁻¹) * ((t * w) * w⁻¹) := by rw [← e1]
        _ = ((x * w⁻¹) * (t * w)) * w⁻¹ := by group
        _ = (t * w) * ((x * w⁻¹) * w⁻¹) := by rw [hucomm]; group
        _ = (t * w) * (w⁻¹ * (x * w⁻¹)) := by rw [huw']
        _ = t * (x * w⁻¹) := by group
    have hU := (mem_inf.mp huF).1
    have huT₁t : x * w⁻¹ ∈ U ⊓ centralizer ({t} : Set G) :=
      mem_inf.mpr ⟨hL.U₁_le hU, mem_centralizer_singleton_iff.mpr hut⟩
    rw [hL.inf_centralizer] at huT₁t
    have huT₁ : x * w⁻¹ ∈ szT₁ L T := hL.muOne_mem_T₁_of_mem_T hS hU
      ((sup_le (szT₁_le_left L T) (zpowers_le.mpr hW.t_mem)) huT₁t)
    exact (h.outer_facts_of_card_sylow hS.card_sylow hW.tw_mem hW.tw_sq hW.tw_not_mem).2.2.1 _
      huT₁ hucomm.symm
  · left
    have hxv' : x * (t * w)⁻¹ ∈ U₁ := by
      rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · exfalso
        rw [← two_mul, pow_mul, hx2, one_pow, one_mul] at h1
        have h1' : t * w ∈ U₁ := by simpa using inv_mem h1
        exact hW.tw_not_mem (mem_sup_left (hL.muOne_mem_T₁_of_mem_T hS h1' hW.tw_mem))
      · rwa [pow_succ, pow_mul, hx2, one_pow, one_mul] at h1
    have hucomm : x * (t * w)⁻¹ * (t * w) = (t * w) * (x * (t * w)⁻¹) := by
      calc x * (t * w)⁻¹ * (t * w) = x := by group
        _ = (t * w) * x * (t * w)⁻¹ := by rw [← hxv]; group
        _ = (t * w) * (x * (t * w)⁻¹) := by group
    have huF := hcF _ hxv' hucomm
    rw [show x = x * (t * w)⁻¹ * (t * w) by group]
    exact mul_mem (mem_sup_left huF) (mem_sup_right (mem_zpowers _))

theorem gmf_exists_conj_of_mem_szA₁_mul_w {x : G} (hx : x * w⁻¹ ∈ szA₁ (szT₁ L T)) :
    ∃ g : G, g * t * g⁻¹ = x := by
  have hsN' : s⁻¹ ∈ normalizer ((U ⊔ T : Subgroup G) : Set G) := inv_mem hW.s_mem_normalizer
  have ha' := hW.level.gms_conj_szA₁ hW.step hsN' hx
  rw [inv_inv] at ha'
  obtain ⟨y, -, hy⟩ := hW.exists_F_conj_eq ha'
  refine ⟨s * y, ?_⟩
  calc s * y * t * (s * y)⁻¹ = s * (y * t * y⁻¹) * s⁻¹ := by group
    _ = s * (s⁻¹ * (x * w⁻¹) * s * t) * s⁻¹ := by rw [hy]
    _ = (x * w⁻¹) * (s * t * s⁻¹) := by group
    _ = x := by rw [hW.conj_t]; group

theorem gmf_mem_A_of_sq_eq_one {x : G} (hxS : x ∈ U ⊔ T) (hxv : x * (t * w) = (t * w) * x)
    (hx2 : x ^ 2 = 1) (hxt : ∀ g : G, g * t * g⁻¹ ≠ x) :
    x ∈ (U₁ ⊓ centralizer ({t * w} : Set G)) ⊔ zpowers (t * w) := by
  rcases hW.gmf_inv_cases hxS hxv hx2 with h1 | h1 | h1
  · exact h1
  · exfalso
    obtain ⟨y, -, hy⟩ := hW.exists_F_conj_eq h1
    exact hxt y (by rw [hy]; group)
  · exfalso
    obtain ⟨g, hg⟩ := hW.gmf_exists_conj_of_mem_szA₁_mul_w h1
    exact hxt g hg

theorem gmf_exists_F_not_comm_t :
    ∃ e ∈ U₁ ⊓ centralizer ({t * w} : Set G), e * t ≠ t * e := by
  have hS := hW.step
  have hL := hW.level
  have h := hS.start
  obtain ⟨-, hA₁card, -, -, -, -, -⟩ := h.facts_of_card_sylow hS.card_sylow
  by_contra hall
  push Not at hall
  have hle : U₁ ⊓ centralizer ({t * w} : Set G) ≤ szA₁ (szT₁ L T) := by
    intro e he
    obtain ⟨heU, heC⟩ := mem_inf.mp he
    have het : e ∈ U ⊓ centralizer ({t} : Set G) :=
      mem_inf.mpr ⟨hL.U₁_le heU, mem_centralizer_singleton_iff.mpr (hall e he)⟩
    rw [hL.inf_centralizer] at het
    have heT₁ : e ∈ szT₁ L T := hL.muOne_mem_T₁_of_mem_T hS heU
      ((sup_le (szT₁_le_left L T) (zpowers_le.mpr hW.t_mem)) het)
    exact (h.outer_facts_of_card_sylow hS.card_sylow hW.tw_mem hW.tw_sq hW.tw_not_mem).2.2.1 _
      heT₁ (mem_centralizer_singleton_iff.mp heC).symm
  have hcard := Subgroup.card_le_of_le hle
  rw [hW.card_F, hA₁card] at hcard
  have hq : 2 ≤ 2 ^ f := le_self_pow₀ (by norm_num) (by have := h.two_le; omega)
  nlinarith

theorem gmf_exists_F_not_comm_w :
    ∃ e ∈ U₁ ⊓ centralizer ({t * w} : Set G), e * w ≠ w * e := by
  obtain ⟨e, he, het⟩ := hW.gmf_exists_F_not_comm_t
  have hsS₀ : s ∈ swapS₂ P U T ⊓ centralizer ({t * w} : Set G) :=
    mem_inf.mpr ⟨hW.s_mem_S₂, mem_centralizer_singleton_iff.mpr (by
      calc s * (t * w) = s * (t * w) * s⁻¹ * s := by group
        _ = (t * w) * s := by rw [hW.conj_tw])⟩
  refine ⟨s * e * s⁻¹, hW.gmf_conj_F hsS₀ he, fun hc => het ?_⟩
  have hts : t = s⁻¹ * w * s := by rw [← hW.conj_t]; group
  calc e * t = s⁻¹ * ((s * e * s⁻¹) * w) * s := by rw [hts]; group
    _ = s⁻¹ * (w * (s * e * s⁻¹)) * s := by rw [hc]
    _ = t * e := by rw [hts]; group

theorem gmf_mem_A_of_comm {x : G} (hxS : x ∈ U ⊔ T) (hxv : x * (t * w) = (t * w) * x)
    (hxF : ∀ e ∈ U₁ ⊓ centralizer ({t * w} : Set G), x * e = e * x) :
    x ∈ (U₁ ⊓ centralizer ({t * w} : Set G)) ⊔ zpowers (t * w) := by
  have hS := hW.step
  have hL := hW.level
  have h := hS.start
  have hS2 := hS.card_sylow
  set F := U₁ ⊓ centralizer ({t * w} : Set G) with hFdef
  have hT₁U₁ : szT₁ L T ≤ U₁ := hW.T₁_le_U₁
  have hTU₁ : ∀ x ∈ T, ∀ u ∈ U₁, x * u * x⁻¹ ∈ U₁ := fun x hx u hu =>
    (mem_normalizer_iff.mp (hL.T_le hx) u).mp hu
  have hcF : ∀ u ∈ U₁, u * (t * w) = (t * w) * u → u ∈ F :=
    fun u hu hcomm => mem_inf.mpr ⟨hu, mem_centralizer_singleton_iff.mpr hcomm⟩
  have hwt := hW.wt_comm
  have htv : t * (t * w) = (t * w) * t := by rw [mul_assoc t w t, hwt]
  have hwv : w * (t * w) = (t * w) * w := by rw [← mul_assoc, hwt]
  have hnot : ∀ z : G, (∀ e ∈ F, z * e = e * z) → (z = t ∨ z = w) → False := by
    rintro z hz (rfl | rfl)
    · obtain ⟨e, he, hne⟩ := hW.gmf_exists_F_not_comm_t
      exact hne (hz e he).symm
    · obtain ⟨e, he, hne⟩ := hW.gmf_exists_F_not_comm_w
      exact hne (hz e he).symm
  have hcent : ∀ u' ∈ F, ∀ z : G, x = u' * z → ∀ e ∈ F, z * e = e * z := by
    intro u' hu' z hxz e he
    have h1 := hxF e he
    rw [hxz] at h1
    have h2 : u' * e = e * u' := hW.F_comm hu' he
    calc z * e = u'⁻¹ * (u' * z * e) := by group
      _ = u'⁻¹ * (e * (u' * z)) := by rw [h1]
      _ = u'⁻¹ * (e * u') * z := by group
      _ = u'⁻¹ * (u' * e) * z := by rw [h2]
      _ = e * z := by group
  rw [hL.muOne_sup_eq hS] at hxS
  obtain ⟨τ, hτ, u, hu, rfl⟩ := ncyc_exists_mul_of_mem_sup hL.T_le hxS
  have hτA : ∀ a ∈ szA₁ (szT₁ L T), τ * a = a * τ := by
    intro a ha
    have h1 := hxF a (hW.gmf_szA₁_le_F ha)
    have h2 : u * a * u⁻¹ = a := hL.conj_szA₁ u (hL.U₁_le hu) a ha
    have h3 : u * a = a * u := by
      calc u * a = u * a * u⁻¹ * u := by group
        _ = a * u := by rw [h2]
    calc τ * a = τ * u * a * u⁻¹ := by rw [mul_assoc τ u a, h3]; group
      _ = a * (τ * u) * u⁻¹ := by rw [h1]
      _ = a * τ := by group
  have hτ2 : τ ^ 2 ∈ szT₁ L T ⊔ zpowers t := by
    by_contra h2
    obtain ⟨E, _, _, _, σ, u₀, v₀, hSC⟩ := h.exists_semilinearCoords_of_card_sylow hS2
    obtain ⟨a, ha, hne⟩ := hSC.exists_not_comm_of_sq_not_mem h hS2 hτ h2
    exact hne (hτA a ha)
  by_cases hτH : τ ∈ szT₁ L T ⊔ zpowers t
  · obtain ⟨y, hy, e, he, hye⟩ := exists_mul_eq_of_mem_sup_zpowers h.mem_centralizer_szT₁ hτH
    rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one he with he1 | he1
    · rw [he1, mul_one] at hye
      subst hye
      exact mem_sup_left (hcF _ (mul_mem (hT₁U₁ hy) hu) hxv)
    · exfalso
      rw [he1] at hye
      have hu'U : τ * u * t⁻¹ ∈ U₁ := by
        rw [← hye, show y * t * u * t⁻¹ = y * (t * u * t⁻¹) by group]
        exact mul_mem (hT₁U₁ hy) (hTU₁ t hW.t_mem u hu)
      have hu'c : τ * u * t⁻¹ * (t * w) = (t * w) * (τ * u * t⁻¹) := by
        have htv' : t⁻¹ * (t * w) = (t * w) * t⁻¹ := (Commute.inv_left htv).eq
        calc τ * u * t⁻¹ * (t * w) = τ * u * (t⁻¹ * (t * w)) := by group
          _ = τ * u * ((t * w) * t⁻¹) := by rw [htv']
          _ = (τ * u * (t * w)) * t⁻¹ := by group
          _ = (t * w) * (τ * u) * t⁻¹ := by rw [hxv]
          _ = (t * w) * (τ * u * t⁻¹) := by group
      exact hnot t (hcent _ (hcF _ hu'U hu'c) t (by group)) (Or.inl rfl)
  · have hM := h.mul_inv_mem_of_sq_mem_of_card_sylow hS2 hτ hW.tw_mem hτ2
      (by rw [hW.tw_sq]; exact one_mem _) hτH hW.tw_not_mem
    obtain ⟨y, hy, e, he, hye⟩ := exists_mul_eq_of_mem_sup_zpowers h.mem_centralizer_szT₁ hM
    rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one he with he1 | he1
    · rw [he1, mul_one] at hye
      have hu'U : τ * u * (t * w)⁻¹ ∈ U₁ := by
        rw [show τ * u * (t * w)⁻¹ = (τ * (t * w)⁻¹) * ((t * w) * u * (t * w)⁻¹) by group,
          ← hye]
        exact mul_mem (hT₁U₁ hy) (hTU₁ _ hW.tw_mem u hu)
      have hu'c : τ * u * (t * w)⁻¹ * (t * w) = (t * w) * (τ * u * (t * w)⁻¹) := by
        calc τ * u * (t * w)⁻¹ * (t * w) = τ * u := by group
          _ = (t * w) * (τ * u) * (t * w)⁻¹ := by rw [← hxv]; group
          _ = (t * w) * (τ * u * (t * w)⁻¹) := by group
      rw [show τ * u = τ * u * (t * w)⁻¹ * (t * w) by group]
      exact mul_mem (mem_sup_left (hcF _ hu'U hu'c)) (mem_sup_right (mem_zpowers _))
    · exfalso
      rw [he1] at hye
      have htt : t * t = 1 := by rw [← sq, h.sq_eq_one]
      have hτw : τ * w⁻¹ = y := by
        calc τ * w⁻¹ = τ * (t * w)⁻¹ * t := by group
          _ = y * t * t := by rw [← hye]
          _ = y := by rw [mul_assoc, htt, mul_one]
      have hu'U : τ * u * w⁻¹ ∈ U₁ := by
        rw [show τ * u * w⁻¹ = (τ * w⁻¹) * (w * u * w⁻¹) by group, hτw]
        exact mul_mem (hT₁U₁ hy) (hTU₁ w hW.w_mem u hu)
      have hu'c : τ * u * w⁻¹ * (t * w) = (t * w) * (τ * u * w⁻¹) := by
        have hwv' : w⁻¹ * (t * w) = (t * w) * w⁻¹ := (Commute.inv_left hwv).eq
        calc τ * u * w⁻¹ * (t * w) = τ * u * (w⁻¹ * (t * w)) := by group
          _ = τ * u * ((t * w) * w⁻¹) := by rw [hwv']
          _ = (τ * u * (t * w)) * w⁻¹ := by group
          _ = (t * w) * (τ * u) * w⁻¹ := by rw [hxv]
          _ = (t * w) * (τ * u * w⁻¹) := by group
      exact hnot w (hcent _ (hcF _ hu'U hu'c) w (by group)) (Or.inr rfl)

end U3C1OuterSwapHigh

end CFSG.SeitzReduction.RankOne
