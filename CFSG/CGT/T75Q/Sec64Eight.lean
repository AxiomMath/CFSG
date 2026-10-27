module

public import CFSG.CGT.T75Q.FixedPoint
public import CFSG.CGT.T75Q.Sec64Aux
public import CFSG.CGT.T75P.DecD
public import CFSG.CGT.T75P.Chain4
public import CFSG.CGT.T75I.Ctx
public import CFSG.CGT.Timmesfeld75.Sec3TwelveRho
public import CFSG.CGT.Timmesfeld75.Sec6TwoSetup
import Mathlib.Tactic.Group
public import CFSG.CGT.T75P.Syl
public import CFSG.CGT.Timmesfeld75.OddCenter
public import CFSG.CGT.Timmesfeld75.Sec5ElevenIso
public import CFSG.CGT.Timmesfeld75.Sec5FiveEng
public import CFSG.CGT.Timmesfeld75.Sec6One
public import CFSG.CGT.Timmesfeld75.Step57Reduction
public import CFSG.Sporadic.M23.M23Group
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonSplitTorus

public section

namespace CFSG.CGT.T75Q

open CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.CGT.T75P CFSG.CGT.T75I

variable {G : Type} [Group G] {T T₁ : Subgroup G}

theorem natural_of_ctx (hc : Sec6Ctx T T₁ 4 1) :
    NaturalSL T (hSub T (normIn T₁ T)) 4 1 := by
  classical
  have : Finite G := hc.finite
  have hS3 : Sec3 T T₁ := hc.sec3
  have hL8 : Nat.card (normIn T T₁) = 8 := by rw [hc.card_normIn]; norm_num
  rcases hc.hcase with h4 | hnat | ⟨h16, hnorm, hhat⟩
  · exfalso
    have := hc.hT
    rw [h4] at this
    norm_num at this
  · exact hnat
  · exfalso
    have hL₁8 : Nat.card (normIn T₁ T) = 8 := hS3.card_normIn_swap.trans hL8
    set H := hSub T (normIn T₁ T) with hH
    have hL₁H : normIn T₁ T ≤ H := le_hSub
    have hT₁ : IsElemAbelian 2 T₁ := hS3.cfg.wc₁.1
    have hL₁el : IsElemAbelian 2 (normIn T₁ T) := by
      refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => hT₁.2 x (normIn_le _ _ hx)⟩
      apply Subtype.ext
      exact elemAbelian_mul_comm hT₁ (normIn_le _ _ a.2) (normIn_le _ _ b.2)
    set A : Subgroup ↥H := (normIn T₁ T).subgroupOf H with hA
    have hAel : IsElemAbelian 2 A := isElemAbelian_comap_subtype hL₁el H
    have hAcard : Nat.card A = 8 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL₁H).toEquiv, hL₁8]
    let ψ : ↥H →* ↥H ⧸ T.subgroupOf H := QuotientGroup.mk' (T.subgroupOf H)
    have hAker : A ⊓ ψ.ker = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hxA, hxk⟩
      have hxT : (x : G) ∈ T := by
        have : x ∈ T.subgroupOf H := by simpa [ψ] using hxk
        exact Subgroup.mem_subgroupOf.1 this
      have hxL : (x : G) ∈ normIn T₁ T := Subgroup.mem_subgroupOf.1 hxA
      have hxT₁ : (x : G) ∈ T₁ := normIn_le _ _ hxL
      have hinf : (x : G) ∈ T ⊓ T₁ := ⟨hxT, hxT₁⟩
      rw [hS3.cfg.inf, Subgroup.mem_bot] at hinf
      exact Subgroup.mem_bot.2 (Subtype.ext hinf)
    have hEcard := card_map_eq_of_inf_ker_eq_bot ψ hAker
    have hEel : IsElemAbelian 2 (A.map ψ) := isElemAbelian_map_of_hom hAel ψ
    have hle : Nat.card (A.map ψ) ≤ 4 := by
      rcases hhat with h | h
      · exact card_le_four_of_hatA (Or.inl rfl) h hEel
      · exact card_le_four_of_hatA (Or.inr rfl) h hEel
    omega


section Algebra

variable {H C : Subgroup G}

theorem mul_hc_mul_hc (hcomm : ∀ h ∈ H, ∀ c ∈ C, h * c = c * h) {h₁ h₂ c₁ c₂ : G}
    (hh₂ : h₂ ∈ H) (hc₁ : c₁ ∈ C) : (h₁ * c₁) * (h₂ * c₂) = (h₁ * h₂) * (c₁ * c₂) := by
  have := hcomm h₂ hh₂ c₁ hc₁
  calc (h₁ * c₁) * (h₂ * c₂) = h₁ * (c₁ * h₂) * c₂ := by group
    _ = h₁ * (h₂ * c₁) * c₂ := by rw [← this]
    _ = (h₁ * h₂) * (c₁ * c₂) := by group

theorem inv_hc (hcomm : ∀ h ∈ H, ∀ c ∈ C, h * c = c * h) {h c : G} (hh : h ∈ H) (hc : c ∈ C) :
    (h * c)⁻¹ = h⁻¹ * c⁻¹ := by
  have := hcomm h⁻¹ (H.inv_mem hh) c⁻¹ (C.inv_mem hc)
  rw [mul_inv_rev, this]

theorem comm_hc (hcomm : ∀ h ∈ H, ∀ c ∈ C, h * c = c * h) {h₁ h₂ c₁ c₂ : G}
    (hh₁ : h₁ ∈ H) (hh₂ : h₂ ∈ H) (hc₁ : c₁ ∈ C) (hc₂ : c₂ ∈ C) :
    (h₁ * c₁) * (h₂ * c₂) * (h₁ * c₁)⁻¹ * (h₂ * c₂)⁻¹ =
      (h₁ * h₂ * h₁⁻¹ * h₂⁻¹) * (c₁ * c₂ * c₁⁻¹ * c₂⁻¹) := by
  rw [inv_hc hcomm hh₁ hc₁, inv_hc hcomm hh₂ hc₂]
  have e1 := mul_hc_mul_hc hcomm (h₁ := h₁) (h₂ := h₂) (c₁ := c₁) (c₂ := c₂) hh₂ hc₁
  have e2 : (h₁ * h₂) * (c₁ * c₂) * (h₁⁻¹ * c₁⁻¹) =
      (h₁ * h₂ * h₁⁻¹) * (c₁ * c₂ * c₁⁻¹) := by
    have := mul_hc_mul_hc hcomm (h₁ := h₁ * h₂) (h₂ := h₁⁻¹) (c₁ := c₁ * c₂) (c₂ := c₁⁻¹)
      (H.inv_mem hh₁) (C.mul_mem hc₁ hc₂)
    exact this
  have e3 : (h₁ * h₂ * h₁⁻¹) * (c₁ * c₂ * c₁⁻¹) * (h₂⁻¹ * c₂⁻¹) =
      (h₁ * h₂ * h₁⁻¹ * h₂⁻¹) * (c₁ * c₂ * c₁⁻¹ * c₂⁻¹) := by
    have := mul_hc_mul_hc hcomm (h₁ := h₁ * h₂ * h₁⁻¹) (h₂ := h₂⁻¹) (c₁ := c₁ * c₂ * c₁⁻¹)
      (c₂ := c₂⁻¹) (H.inv_mem hh₂) (C.mul_mem (C.mul_mem hc₁ hc₂) (C.inv_mem hc₁))
    exact this
  rw [e1, e2, e3]

theorem comp_comm_of_abelian {H C : Subgroup G} (hcomm : ∀ h ∈ H, ∀ c ∈ C, h * c = c * h)
    (hHC : H ⊓ C = ⊥) {h₀ w hy cy : G} (hh₀ : h₀ ∈ H) (hw : w ∈ C) (hhy : hy ∈ H)
    (hcy : cy ∈ C) (hxy : (h₀ * w) * (hy * cy) = (hy * cy) * (h₀ * w)) : w * cy = cy * w := by
  have e1 := mul_hc_mul_hc hcomm (h₁ := h₀) (h₂ := hy) (c₁ := w) (c₂ := cy) hhy hw
  have e2 := mul_hc_mul_hc hcomm (h₁ := hy) (h₂ := h₀) (c₁ := cy) (c₂ := w) hh₀ hcy
  rw [e1, e2] at hxy
  have hmem : (hy * h₀)⁻¹ * (h₀ * hy) ∈ H ⊓ C := by
    refine ⟨H.mul_mem (H.inv_mem (H.mul_mem hhy hh₀)) (H.mul_mem hh₀ hhy), ?_⟩
    have : (hy * h₀)⁻¹ * (h₀ * hy) = (cy * w) * (w * cy)⁻¹ := by
      have h1 : h₀ * hy = (hy * h₀) * ((cy * w) * (w * cy)⁻¹) := by
        calc h₀ * hy = (h₀ * hy) * (w * cy) * (w * cy)⁻¹ := by group
          _ = (hy * h₀) * (cy * w) * (w * cy)⁻¹ := by rw [hxy]
          _ = (hy * h₀) * ((cy * w) * (w * cy)⁻¹) := by group
      calc (hy * h₀)⁻¹ * (h₀ * hy) = (hy * h₀)⁻¹ * ((hy * h₀) * ((cy * w) * (w * cy)⁻¹)) := by
            rw [← h1]
        _ = (cy * w) * (w * cy)⁻¹ := by group
    rw [this]
    exact C.mul_mem (C.mul_mem hcy hw) (C.inv_mem (C.mul_mem hw hcy))
  rw [hHC, Subgroup.mem_bot] at hmem
  have h2 : (cy * w) * (w * cy)⁻¹ = 1 := by
    have e : (hy * h₀)⁻¹ * (h₀ * hy) = (cy * w) * (w * cy)⁻¹ := by
      have h1 : h₀ * hy = (hy * h₀) * ((cy * w) * (w * cy)⁻¹) := by
        calc h₀ * hy = (h₀ * hy) * (w * cy) * (w * cy)⁻¹ := by group
          _ = (hy * h₀) * (cy * w) * (w * cy)⁻¹ := by rw [hxy]
          _ = (hy * h₀) * ((cy * w) * (w * cy)⁻¹) := by group
      calc (hy * h₀)⁻¹ * (h₀ * hy) = (hy * h₀)⁻¹ * ((hy * h₀) * ((cy * w) * (w * cy)⁻¹)) := by
            rw [← h1]
        _ = (cy * w) * (w * cy)⁻¹ := by group
    rw [← e]
    exact hmem
  exact (mul_inv_eq_one.1 h2).symm

end Algebra

section Core

variable [Finite G]

theorem sec64Eight_core (h62 : Sec62) (h63 : Sec63) (hc : Sec6Ctx T T₁ 4 1)
    (hnat : NaturalSL T (hSub T (normIn T₁ T)) 4 1) {x : G} (hx : x ∈ normD T) (hxT : x ∉ T)
    {g : G} (hxg : x ∈ conjSubgroup g T)
    (hcard : Nat.card ↥(T ⊓ Subgroup.centralizer ({x} : Set G)) = 4) :
    x ∈ hSub T (normIn T₁ T) := by
  classical
  have : IsSimpleGroup G := hc.hy.simple
  obtain ⟨hTH, hHN, hHnorm⟩ := hSub_data T T₁
  have hTwc : IsWC T := hc.hy.pair.wc
  have hx1 : x ≠ 1 := ne_one_of_mem_classD hx.1
  have hne : conjSubgroup g T ≠ T := fun h => hxT (h ▸ hxg)
  have hxN' : x ∈ normIn (conjSubgroup g T) T := mem_normIn.2 ⟨hxg, hx.2⟩
  have hbot' : normIn (conjSubgroup g T) T ≠ ⊥ := fun hb =>
    hx1 (Subgroup.mem_bot.1 (hb ▸ hxN'))
  have hbot : normIn T (conjSubgroup g T) ≠ ⊥ := normIn_ne_bot_of_conj hTwc hne hbot'
  have hcfg : Cfg T (conjSubgroup g T) :=
    cfg_of_conj_conj hTwc ⟨1, (conjSubgroup_one T).symm⟩ ⟨g, rfl⟩ hne hbot
  have hS3 : Sec3 T (conjSubgroup g T) := hc.hS g hne hbot
  obtain ⟨hNM, f, hf, hiso⟩ := hc.hI g hne hbot
  have := hNM
  have hcardL : Nat.card ↥(normIn T (conjSubgroup g T)) = 4 := by
    rw [← hcfg.inf_centralizer_eq_normIn hxN' hx1]
    exact hcard
  have h2f : (2 : ℕ) ^ f = 2 ^ 2 := by
    have h := hS3.card_eq_mul hf hiso
    rw [hc.hT, hcardL] at h
    norm_num at h
    omega
  have hf2 : f = 2 := Nat.pow_right_injective (le_refl 2) h2f
  subst hf2
  have hX := hS3.isL2Pair_quotient hf hiso
  obtain ⟨k, hkX, hkNm, hkodd, hk1⟩ := exists_odd_normalizer hS3 (le_refl 2) hX
  have hfix := Sec3.centralizer_cfgM_eq_bot_of_odd hS3 hX hkX hkodd hk1
  obtain ⟨h₀, hh₀, w, hw, hxw⟩ := normalizer_eq_mul h62 h63 hc hnat chain4 hx.2
  obtain ⟨hk', hhk, ck, hck, hkdec⟩ := normalizer_eq_mul h62 h63 hc hnat chain4 hkNm
  have hHC := inf_hSub_centralizer_eq_bot hc hnat
  have hTC := inf_centralizer_hSub_eq_bot hc hnat
  have hcomm : ∀ h ∈ hSub T (normIn T₁ T), ∀ c ∈ Subgroup.centralizer
      (hSub T (normIn T₁ T) : Set G), h * c = c * h := fun h hh c hc' =>
    Subgroup.mem_centralizer_iff.1 hc' h hh
  have hwT : ∀ t ∈ T, w * t = t * w := fun t ht =>
    (Subgroup.mem_centralizer_iff.1 (Subgroup.centralizer_le hTH hw) t ht).symm
  have hwx : w * x = x * w := by
    rw [hxw]
    calc w * (h₀ * w) = (w * h₀) * w := by group
      _ = (h₀ * w) * w := by rw [(hcomm h₀ hh₀ w hw).symm]
  have hwN' : w ∈ Subgroup.normalizer (conjSubgroup g T : Set G) :=
    hcfg.wc₁.centralizer_le_normalizer hxg hx1 (Subgroup.mem_centralizer_singleton_iff.2 hwx)
  have hwN : w ∈ Subgroup.normalizer (T : Set G) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hTH hw)
  have hwY : ∀ z ∈ T ⊔ conjSubgroup g T, w * z * w⁻¹ ∈ T ⊔ conjSubgroup g T := by
    intro z hz
    have hY : conjSubgroup w (T ⊔ conjSubgroup g T) = T ⊔ conjSubgroup g T := by
      rw [conjSubgroup_sup_eq_sup, mem_normalizer_iff_conjSubgroup_eq.1 hwN,
        mem_normalizer_iff_conjSubgroup_eq.1 hwN']
    rw [← hY]
    refine mem_conjSubgroup.2 ?_
    rw [show w⁻¹ * (w * z * w⁻¹) * w = z by group]
    exact hz
  have hwM : ∀ m ∈ cfgM T (conjSubgroup g T), w * m = m * w := by
    intro m hm
    obtain ⟨l, hl, y, hy, rfl⟩ := hcfg.mem_cfgM_iff.1 hm
    have hlT : l ∈ T := (mem_normIn.1 hl).1
    obtain ⟨hy', hhy, cy, hcy, hydec⟩ :=
      normalizer_eq_mul h62 h63 hc hnat chain4 (mem_normIn.1 hy).2
    have hxy : x * y = y * x := elemAbelian_mul_comm hcfg.wc₁.1 hxg (mem_normIn.1 hy).1
    have hwcy : w * cy = cy * w := by
      refine comp_comm_of_abelian hcomm hHC hh₀ hw hhy hcy ?_
      rw [← hxw, ← hydec]
      exact hxy
    have h2 : w * y = y * w := by
      rw [hydec]
      calc w * (hy' * cy) = (w * hy') * cy := by group
        _ = (hy' * w) * cy := by rw [(hcomm hy' hhy w hw).symm]
        _ = hy' * (w * cy) := by group
        _ = hy' * (cy * w) := by rw [hwcy]
        _ = (hy' * cy) * w := by group
    calc w * (l * y) = (w * l) * y := by group
      _ = (l * w) * y := by rw [hwT l hlT]
      _ = l * (w * y) := by group
      _ = l * (y * w) := by rw [h2]
      _ = (l * y) * w := by group
  have hwk : w * hk' = hk' * w := (hcomm hk' hhk w hw).symm
  have hvC : w * ck * w⁻¹ * ck⁻¹ ∈ Subgroup.centralizer (hSub T (normIn T₁ T) : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hw hck) (Subgroup.inv_mem _ hw))
      (Subgroup.inv_mem _ hck)
  have hu : w * k * w⁻¹ * k⁻¹ = w * ck * w⁻¹ * ck⁻¹ := by
    rw [hkdec]
    have hhv : hk' * (w * ck * w⁻¹ * ck⁻¹) = (w * ck * w⁻¹ * ck⁻¹) * hk' :=
      hcomm hk' hhk _ hvC
    calc w * (hk' * ck) * w⁻¹ * (hk' * ck)⁻¹
        = (w * hk') * ck * w⁻¹ * ck⁻¹ * hk'⁻¹ := by group
      _ = (hk' * w) * ck * w⁻¹ * ck⁻¹ * hk'⁻¹ := by rw [hwk]
      _ = hk' * (w * ck * w⁻¹ * ck⁻¹) * hk'⁻¹ := by group
      _ = w * ck * w⁻¹ * ck⁻¹ := by rw [hhv]; group
  have hu_in : w * k * w⁻¹ * k⁻¹ ∈ T ⊔ conjSubgroup g T :=
    Subgroup.mul_mem _ (hwY k hkX) (Subgroup.inv_mem _ hkX)
  have huT : w * k * w⁻¹ * k⁻¹ ∈ T := by
    refine mem_left_of_centralizes hS3 hX hu_in fun t ht => ?_
    rw [hu]
    exact (Subgroup.mem_centralizer_iff.1 (Subgroup.centralizer_le hTH hvC) t ht).symm
  have hv1 : w * ck * w⁻¹ * ck⁻¹ = 1 := by
    have hmem : w * ck * w⁻¹ * ck⁻¹ ∈ T ⊓ Subgroup.centralizer
        (hSub T (normIn T₁ T) : Set G) := ⟨hu ▸ huT, hvC⟩
    rw [hTC, Subgroup.mem_bot] at hmem
    exact hmem
  have hwck : w * ck = ck * w := by
    have h1 := mul_inv_eq_one.1 hv1
    exact mul_inv_eq_iff_eq_mul.1 h1
  have hKerH : k * x * k⁻¹ * x⁻¹ ∈ hSub T (normIn T₁ T) := by
    have e : k * x * k⁻¹ * x⁻¹ = (hk' * h₀ * hk'⁻¹ * h₀⁻¹) * (ck * w * ck⁻¹ * w⁻¹) := by
      rw [hkdec, hxw]
      exact comm_hc hcomm hhk hh₀ hck hw
    have e2 : ck * w * ck⁻¹ * w⁻¹ = 1 := by
      rw [← hwck]
      group
    rw [e, e2, mul_one]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hhk hh₀)
      (Subgroup.inv_mem _ hhk)) (Subgroup.inv_mem _ hh₀)
  have hxM : x ∈ cfgM T (conjSubgroup g T) := Cfg.normIn_le_cfgM_right T _ hxN'
  have hkM : ∀ m ∈ cfgM T (conjSubgroup g T), k * m * k⁻¹ ∈ cfgM T (conjSubgroup g T) :=
    fun m hm => hcfg.conj_mem_cfgM hkX hm
  have hxK : x ∈ cfgM T (conjSubgroup g T) ⊓ hSub T (normIn T₁ T) := by
    refine mem_of_commutator_mem (N := cfgM T (conjSubgroup g T))
      (K := cfgM T (conjSubgroup g T) ⊓ hSub T (normIn T₁ T))
      (fun a ha b hb => elemAbelian_mul_comm hcfg.isElemAbelian_cfgM ha hb) inf_le_left hkM
      (fun m hm => ⟨hkM m hm.1, hHnorm k hkNm m hm.2⟩) hfix hxM ?_
    exact ⟨Subgroup.mul_mem _ (hkM x hxM) (Subgroup.inv_mem _ hxM), hKerH⟩
  exact hxK.2

end Core

theorem sec64Eight_of (h62 : Sec62) (h63 : Sec63) : Sec64Eight := by
  intro G _ T T₁ n m hc hT16 hL8 x hx hxT hcard
  have : Finite G := hc.finite
  obtain ⟨hn, hm⟩ := hc.card_eq_sixteen_iff.1 ⟨hT16, hL8⟩
  subst hn
  subst hm
  obtain ⟨g, hg⟩ := exists_mem_conj_of_mem_classD hx.1
  exact sec64Eight_core h62 h63 hc (natural_of_ctx hc) hx hxT hg hcard

end CFSG.CGT.T75Q
