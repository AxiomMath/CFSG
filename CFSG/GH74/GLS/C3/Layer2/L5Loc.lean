module

public import CFSG.GH74.GLS.C3.Layer2.L5Rel

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Prop121
  CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

variable {G : Type} [Group G] [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}

structure Loc5 (h : IsAConfig 5 x K T Q S a) where
  hxS : x ∈ S
  hvS : x * (a * x * a⁻¹) ∈ S
  hT32 : Nat.card T = 32
  ι : ↥(centralizer ({x} : Set G)) ≃* ↥(Fgrp 5)
  hι1 : ((ι (xC x) : Fgrp 5) : Amb 5) = x0 5
  hιQ : ∀ c : ↥(centralizer ({x} : Set G)), (((ι c : Fgrp 5) : Amb 5).1 = 1 ↔ (c : G) ∈ Q)
  hιT : ∀ c : ↥(centralizer ({x} : Set G)), (c : G) ∈ T ↔ ((ι c : Fgrp 5) : Amb 5) ∈ T5
  ψ : ↥S →* Perm (Fin 9)
  hψ : Psi5 x a S hxS hvS ψ
  b : Amb 5 → Amb 5
  hb : Adm b
  hbψ : ∀ (s : ↥S) (c : ↥(centralizer ({x} : Set G))), (c : G) = (s : G) → (c : G) ∈ T →
    ψ s = emb 5 (b ((ι c : Fgrp 5) : Amb 5))

namespace Loc5

@[expose] def pt (h : IsAConfig 5 x K T Q S a) (t : ↥T) : ↥S := ⟨(t : G), h.T_lt_S.le t.2⟩

variable {h : IsAConfig 5 x K T Q S a} (L : Loc5 h)
include L

@[expose] def pc (t : ↥T) : Amb 5 := ((L.ι ⟨(t : G), h.T_le_C t.2⟩ : Fgrp 5) : Amb 5)

theorem pc_mem (t : ↥T) : L.pc t ∈ T5 := (L.hιT _).1 t.2

theorem psi_pt (t : ↥T) : L.ψ (pt h t) = emb 5 (L.b (L.pc t)) :=
  L.hbψ (pt h t) ⟨(t : G), h.T_le_C t.2⟩ rfl t.2

theorem pc_mul (t₁ t₂ : ↥T) : L.pc (t₁ * t₂) = L.pc t₁ * L.pc t₂ := by
  have : (⟨((t₁ * t₂ : ↥T) : G), h.T_le_C (t₁ * t₂).2⟩ : ↥(centralizer ({x} : Set G))) =
      ⟨(t₁ : G), h.T_le_C t₁.2⟩ * ⟨(t₂ : G), h.T_le_C t₂.2⟩ := rfl
  unfold pc
  rw [this, map_mul]
  rfl

theorem pc_one : L.pc 1 = 1 := by
  have : (⟨(((1 : ↥T)) : G), h.T_le_C (1 : ↥T).2⟩ : ↥(centralizer ({x} : Set G))) = 1 := rfl
  unfold pc
  rw [this, map_one]
  rfl

theorem pc_ne_one {t : ↥T} (ht : t ≠ 1) : L.pc t ≠ 1 := by
  intro h1
  apply ht
  have h2 : L.ι ⟨(t : G), h.T_le_C t.2⟩ = L.ι 1 := by
    apply Subtype.ext
    rw [map_one]
    exact h1
  have h3 := L.ι.injective h2
  have h4 := congrArg Subtype.val h3
  exact Subtype.ext h4

theorem pc_x : L.pc ⟨x, h.x_mem_T⟩ = f1 := L.hι1

theorem nm_psi
    (t : ↥T) (ht2 : t * t = 1) (ht1 : t ≠ 1) :
    numMoved (L.ψ (pt h t)) = nmE (L.pc t) := by
  have hp : L.pc t ∈ T5 := L.pc_mem t
  have hsq : L.pc t * L.pc t = 1 := by rw [← L.pc_mul, ht2, L.pc_one]
  rw [L.psi_pt t]
  exact L.hb.keyB hp hsq (L.pc_ne_one ht1)

theorem iota_v :
    ((L.ι ⟨L4.vElt x a, h.T_le_C (L4.v_mem_T h)⟩ : Fgrp 5) : Amb 5) = vhat5 := by
  have hvT : L4.vElt x a ∈ T := L4.v_mem_T h
  have h1 := L.psi_pt ⟨L4.vElt x a, hvT⟩
  have h2 : L.ψ (pt h ⟨L4.vElt x a, hvT⟩) = yS := L.hψ.v_eq
  rw [h2] at h1
  have h1' : emb 5 (L.b (L.pc ⟨L4.vElt x a, hvT⟩)) = emb 5 vhat5 := h1.symm
  have h3 : L.b (L.pc ⟨L4.vElt x a, hvT⟩) = vhat5 := emb_injective 5 h1'
  have hp : L.pc ⟨L4.vElt x a, hvT⟩ ∈ T5 := L.pc_mem _
  exact L.hb.aut.inj _ hp _ vhat5_mem_T5 (h3.trans L.hb.vhat.symm)

theorem card_S : Nat.card S = 64 := by
  have hr : L.ψ.range = S0 := by
    ext p
    constructor
    · rintro ⟨s, rfl⟩
      exact L.hψ.mem s
    · intro hp
      obtain ⟨s, hs⟩ := L.hψ.surj p hp
      exact ⟨s, hs⟩
  have h1 : Nat.card S = Nat.card L.ψ.range :=
    Nat.card_congr (MonoidHom.ofInjective L.hψ.inj).toEquiv
  rw [h1, hr, card_S0]

@[expose] def EG : Subgroup G := (E9.comap L.ψ).map S.subtype

theorem mem_EG
    {y : G} : y ∈ L.EG ↔ ∃ hy : y ∈ S, L.ψ ⟨y, hy⟩ ∈ E9 := by
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s.2, hs⟩
  · rintro ⟨hy, hψ⟩
    exact ⟨⟨y, hy⟩, hψ, rfl⟩

theorem EG_le_S : L.EG ≤ S := by
  rintro y ⟨s, -, rfl⟩
  exact s.2

theorem EG_le_T : L.EG ≤ T := by
  intro y hy
  obtain ⟨hyS, hψy⟩ := L.mem_EG.1 hy
  exact (psi_mem_R5_iff h L.hψ ⟨y, hyS⟩).2 (E9_le_R5 hψy)

theorem card_EG : Nat.card L.EG = 8 := by
  have hr : E9 ≤ L.ψ.range := by
    intro p hp
    obtain ⟨s, hs⟩ := L.hψ.surj p (E9_le_S0 hp)
    exact ⟨s, hs⟩
  have h1 : (E9.comap L.ψ).map L.ψ = E9 := Subgroup.map_comap_eq_self hr
  have h2 : Nat.card ((E9.comap L.ψ).map L.ψ) = Nat.card (E9.comap L.ψ) :=
    Subgroup.card_map_of_injective L.hψ.inj
  rw [h1, card_E9] at h2
  have h3 : Nat.card L.EG = Nat.card (E9.comap L.ψ) :=
    Subgroup.card_map_of_injective S.subtype_injective
  rw [h3, ← h2]

theorem EG_comm : ∀ y₁ ∈ L.EG, ∀ y₂ ∈ L.EG, y₁ * y₂ = y₂ * y₁ := by
  intro y₁ h₁ y₂ h₂
  obtain ⟨hy₁, hψ₁⟩ := L.mem_EG.1 h₁
  obtain ⟨hy₂, hψ₂⟩ := L.mem_EG.1 h₂
  have h3 : (⟨y₁, hy₁⟩ : ↥S) * ⟨y₂, hy₂⟩ = ⟨y₂, hy₂⟩ * ⟨y₁, hy₁⟩ := by
    apply L.hψ.inj
    rw [map_mul, map_mul]
    exact E9_comm _ hψ₁ _ hψ₂
  have h4 := congrArg Subtype.val h3
  exact h4

theorem EG_sq : ∀ y ∈ L.EG, y * y = 1 := by
  intro y hy
  obtain ⟨hyS, hψy⟩ := L.mem_EG.1 hy
  have h3 : (⟨y, hyS⟩ : ↥S) * ⟨y, hyS⟩ = 1 := by
    apply L.hψ.inj
    rw [map_mul, map_one]
    exact E9_sq _ hψy
  have h4 := congrArg Subtype.val h3
  exact h4

theorem x_mem_EG : x ∈ L.EG := by
  refine L.mem_EG.2 ⟨L.hxS, ?_⟩
  rw [L.hψ.x_eq]
  exact emb_f1_mem_E9

theorem v_mem_EG : L4.vElt x a ∈ L.EG := by
  refine L.mem_EG.2 ⟨L.hvS, ?_⟩
  rw [L.hψ.v_eq]
  exact yS_mem_E9

theorem S_norm_EG
    : ∀ s ∈ S, ∀ e ∈ L.EG, s * e * s⁻¹ ∈ L.EG := by
  intro s hs e he
  obtain ⟨heS, hψe⟩ := L.mem_EG.1 he
  refine L.mem_EG.2 ⟨mul_mem (mul_mem hs heS) (inv_mem hs), ?_⟩
  have : L.ψ ⟨s * e * s⁻¹, mul_mem (mul_mem hs heS) (inv_mem hs)⟩ =
      L.ψ ⟨s, hs⟩ * L.ψ ⟨e, heS⟩ * (L.ψ ⟨s, hs⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [this]
  exact S0_norm_E9 (L.hψ.mem _) hψe

theorem mem_EG_T
    (t : ↥T) : (t : G) ∈ L.EG ↔ L.pc t ∈ E5 := by
  rw [L.mem_EG]
  constructor
  · rintro ⟨hy, hψy⟩
    have h1 : L.ψ ⟨(t : G), hy⟩ = emb 5 (L.b (L.pc t)) := L.psi_pt t
    rw [h1] at hψy
    obtain ⟨e, he, hee⟩ := mem_E9.1 hψy
    have h2 : e = L.b (L.pc t) := emb_injective 5 hee
    rw [← (L.hb.mem_E5_iff (L.pc_mem t))]
    rw [← h2]
    exact he
  · intro hE
    refine ⟨h.T_lt_S.le t.2, ?_⟩
    have h1 : L.ψ ⟨(t : G), h.T_lt_S.le t.2⟩ = emb 5 (L.b (L.pc t)) := L.psi_pt t
    rw [h1]
    exact ⟨_, (L.hb.mem_E5_iff (L.pc_mem t)).2 hE, rfl⟩

theorem mem_EG_of_sub
    {Cv : Subgroup G} (e : ↥(L.EG.subgroupOf Cv)) : ((e : ↥Cv) : G) ∈ L.EG :=
  e.2

theorem exists_pc {p : Amb 5} (hp : p ∈ T5) : ∃ t : ↥T, L.pc t = p := by
  have hpF : p ∈ Fgrp 5 := T5_le_Fgrp hp
  let c₀ : ↥(centralizer ({x} : Set G)) := L.ι.symm ⟨p, hpF⟩
  have hιc : ((L.ι c₀ : Fgrp 5) : Amb 5) = p := by
    show ((L.ι (L.ι.symm ⟨p, hpF⟩) : Fgrp 5) : Amb 5) = p
    rw [MulEquiv.apply_symm_apply]
  have hcT : (c₀ : G) ∈ T := (L.hιT c₀).2 (by rw [hιc]; exact hp)
  exact ⟨⟨(c₀ : G), hcT⟩, hιc⟩

theorem exists_conj_sigma5
    {v₁ : G} (hv1 : IsConj v₁ (L4.vElt x a)) (hc : v₁ * x = x * v₁)
    (hxv : IsConj (x * v₁) x) : ∃ d : G, d * x = x * d ∧ d * v₁ * d⁻¹ = L4.vElt x a := by
  obtain ⟨g₁, hg₁⟩ := isConj_iff.1 hv1
  have hv1sq : v₁ * v₁ = 1 := by
    have h2 : v₁ = g₁⁻¹ * L4.vElt x a * g₁ := by rw [← hg₁]; group
    rw [h2]
    calc g₁⁻¹ * L4.vElt x a * g₁ * (g₁⁻¹ * L4.vElt x a * g₁)
        = g₁⁻¹ * (L4.vElt x a * L4.vElt x a) * g₁ := by group
      _ = 1 := by rw [L4.v_mul_self h]; group
  have hv1C : v₁ ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.2 hc
  obtain ⟨k, hk, hkT⟩ := exists_mem_conj_le_of_isSylowOf (p := 2) h.sylowT
    (X := zpowers v₁) (zpowers_le.2 hv1C) (L4.TIData.isPGroup_zpowers hv1sq)
  have hv2T : k⁻¹ * v₁ * k ∈ T := hkT v₁ (mem_zpowers v₁)
  have hkx : k * x = x * k := mem_centralizer_singleton_iff.1 hk
  have hxk' : x * k⁻¹ = k⁻¹ * x := by
    calc x * k⁻¹ = k⁻¹ * (k * x) * k⁻¹ := by group
      _ = k⁻¹ * (x * k) * k⁻¹ := by rw [hkx]
      _ = k⁻¹ * x := by group
  let t₂ : ↥T := ⟨k⁻¹ * v₁ * k, hv2T⟩
  have hv2sq : (t₂ : G) * (t₂ : G) = 1 := by
    show k⁻¹ * v₁ * k * (k⁻¹ * v₁ * k) = 1
    calc k⁻¹ * v₁ * k * (k⁻¹ * v₁ * k) = k⁻¹ * (v₁ * v₁) * k := by group
      _ = 1 := by rw [hv1sq]; group
  have hv2ne : (t₂ : G) ≠ 1 := by
    intro h1
    have h2 : k⁻¹ * v₁ * k = 1 := h1
    have h3 : v₁ = 1 := by
      calc v₁ = k * (k⁻¹ * v₁ * k) * k⁻¹ := by group
        _ = 1 := by rw [h2]; group
    apply L4.v_ne_one h
    obtain ⟨g₂, hg₂⟩ := isConj_iff.1 hv1
    rw [h3] at hg₂
    simpa using hg₂.symm
  have ht2c : (t₂ : G) * x = x * (t₂ : G) := by
    show k⁻¹ * v₁ * k * x = x * (k⁻¹ * v₁ * k)
    calc k⁻¹ * v₁ * k * x = k⁻¹ * v₁ * (k * x) := by group
      _ = k⁻¹ * v₁ * (x * k) := by rw [hkx]
      _ = k⁻¹ * (v₁ * x) * k := by group
      _ = k⁻¹ * (x * v₁) * k := by rw [hc]
      _ = (k⁻¹ * x) * v₁ * k := by group
      _ = (x * k⁻¹) * v₁ * k := by rw [hxk']
      _ = x * (k⁻¹ * v₁ * k) := by group
  have ht2v : IsConj (t₂ : G) (L4.vElt x a) :=
    (isConj_iff.2 ⟨k⁻¹, by group⟩ : IsConj v₁ (k⁻¹ * v₁ * k)).symm.trans hv1
  have hxt2 : IsConj (x * (t₂ : G)) x := by
    have h2 : x * (k⁻¹ * v₁ * k) = k⁻¹ * (x * v₁) * k := by
      calc x * (k⁻¹ * v₁ * k) = (x * k⁻¹) * v₁ * k := by group
        _ = (k⁻¹ * x) * v₁ * k := by rw [hxk']
        _ = k⁻¹ * (x * v₁) * k := by group
    show IsConj (x * (k⁻¹ * v₁ * k)) x
    rw [h2]
    exact (isConj_iff.2 ⟨k⁻¹, by group⟩ : IsConj (x * v₁) (k⁻¹ * (x * v₁) * k)).symm.trans hxv
  let xt₂ : ↥T := ⟨x * (t₂ : G), mul_mem h.x_mem_T t₂.2⟩
  have hxt2sq : (xt₂ : G) * (xt₂ : G) = 1 := by
    show x * (t₂ : G) * (x * (t₂ : G)) = 1
    calc x * (t₂ : G) * (x * (t₂ : G)) = x * ((t₂ : G) * x) * (t₂ : G) := by group
      _ = x * (x * (t₂ : G)) * (t₂ : G) := by rw [ht2c]
      _ = (x * x) * ((t₂ : G) * (t₂ : G)) := by group
      _ = 1 := by rw [L4.x_mul_self h, hv2sq, one_mul]
  have hxt2ne : (xt₂ : G) ≠ 1 := by
    intro h1
    have h2 : x * (t₂ : G) = 1 := h1
    rw [h2] at hxt2
    exact h.x_ne_one (isConj_one_right.1 hxt2)
  have hv2sq' : t₂ * t₂ = 1 := Subtype.ext hv2sq
  have hv2ne' : t₂ ≠ 1 := fun h1 => hv2ne (congrArg Subtype.val h1)
  have hxt2sq' : xt₂ * xt₂ = 1 := Subtype.ext hxt2sq
  have hxt2ne' : xt₂ ≠ 1 := fun h1 => hxt2ne (congrArg Subtype.val h1)
  have hS2 : orderOf (pt h t₂) = 2 := L4.orderOf_eq_two_of_mul_self (pt h t₂) hv2sq hv2ne
  have hSv : orderOf (⟨L4.vElt x a, L.hvS⟩ : ↥S) = 2 :=
    L4.orderOf_eq_two_of_mul_self _ (L4.v_mul_self h) (L4.v_ne_one h)
  have hSxt : orderOf (pt h xt₂) = 2 := L4.orderOf_eq_two_of_mul_self (pt h xt₂) hxt2sq hxt2ne
  have hSx : orderOf (⟨x, L.hxS⟩ : ↥S) = 2 :=
    L4.orderOf_eq_two_of_mul_self _ (L4.x_mul_self h) h.x_ne_one
  have hnm1 : numMoved (L.ψ (pt h t₂)) = numMoved (L.ψ ⟨L4.vElt x a, L.hvS⟩) :=
    (L.hψ.conj (pt h t₂) ⟨L4.vElt x a, L.hvS⟩ hS2 hSv).1 ht2v
  rw [L.hψ.v_eq, numMoved_yS] at hnm1
  have h8 : nmE (L.pc t₂) = 8 := by
    rw [← L.nm_psi t₂ hv2sq' hv2ne']
    exact hnm1
  have hnm2 : numMoved (L.ψ (pt h xt₂)) = numMoved (L.ψ ⟨x, L.hxS⟩) :=
    (L.hψ.conj (pt h xt₂) ⟨x, L.hxS⟩ hSxt hSx).1 hxt2
  rw [L.hψ.x_eq] at hnm2
  have h4 : nmE (L.pc xt₂) = 4 := by
    rw [← L.nm_psi xt₂ hxt2sq' hxt2ne']
    rw [hnm2]
    exact nmE_f1
  have hpcx : L.pc xt₂ = f1 * L.pc t₂ := by
    have : xt₂ = ⟨x, h.x_mem_T⟩ * t₂ := rfl
    rw [this, L.pc_mul, L.pc_x]
  have hss : L.pc t₂ * L.pc t₂ = 1 := by rw [← L.pc_mul, hv2sq', L.pc_one]
  have hs1 : L.pc t₂ ≠ 1 := L.pc_ne_one hv2ne'
  have h4' : nmE (f1 * L.pc t₂) = 4 := by rw [← hpcx]; exact h4
  obtain ⟨g, hg, hgs⟩ := sigma5 (L.pc_mem t₂) hss hs1 h8 h4'
  set d₂ : ↥(centralizer ({x} : Set G)) := L.ι.symm ⟨g, hg⟩ with hd₂
  have hconj : d₂ * (⟨(t₂ : G), h.T_le_C t₂.2⟩ : ↥(centralizer ({x} : Set G))) * d₂⁻¹ =
      ⟨L4.vElt x a, h.T_le_C (L4.v_mem_T h)⟩ := by
    apply L.ι.injective
    apply Subtype.ext
    have e : L.ι d₂ = ⟨g, hg⟩ := MulEquiv.apply_symm_apply _ _
    rw [map_mul, map_mul, map_inv, e, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [L.iota_v]
    exact hgs
  have hdx : (d₂ : G) * x = x * (d₂ : G) := mem_centralizer_singleton_iff.1 d₂.2
  refine ⟨(d₂ : G) * k⁻¹, ?_, ?_⟩
  · calc (d₂ : G) * k⁻¹ * x = (d₂ : G) * (k⁻¹ * x) := by group
      _ = (d₂ : G) * (x * k⁻¹) := by rw [hxk']
      _ = ((d₂ : G) * x) * k⁻¹ := by group
      _ = x * ((d₂ : G) * k⁻¹) := by rw [hdx]; group
  · have h4 := congrArg Subtype.val hconj
    calc (d₂ : G) * k⁻¹ * v₁ * ((d₂ : G) * k⁻¹)⁻¹
        = (d₂ : G) * (k⁻¹ * v₁ * k) * (d₂ : G)⁻¹ := by group
      _ = L4.vElt x a := h4

theorem exists_conj_Cv5
    {y : G} (hyx : IsConj y x)
    (hyv : y * L4.vElt x a = L4.vElt x a * y) (hyvx : IsConj (y * L4.vElt x a) x) :
    ∃ g : G, g * L4.vElt x a = L4.vElt x a * g ∧ g * x * g⁻¹ = y := by
  obtain ⟨g₀, hg₀⟩ := isConj_iff.1 hyx.symm
  set v : G := L4.vElt x a with hv
  have h1 : IsConj (g₀⁻¹ * v * g₀) v := isConj_iff.2 ⟨g₀, by group⟩
  have h2 : (g₀⁻¹ * v * g₀) * x = x * (g₀⁻¹ * v * g₀) := by
    have h5 : (g₀ * x * g₀⁻¹) * v = v * (g₀ * x * g₀⁻¹) := by rw [hg₀]; exact hyv
    calc (g₀⁻¹ * v * g₀) * x = g₀⁻¹ * (v * (g₀ * x * g₀⁻¹)) * g₀ := by group
      _ = g₀⁻¹ * ((g₀ * x * g₀⁻¹) * v) * g₀ := by rw [h5]
      _ = x * (g₀⁻¹ * v * g₀) := by group
  have h3 : IsConj (x * (g₀⁻¹ * v * g₀)) x := by
    have h6 : x * (g₀⁻¹ * v * g₀) = g₀⁻¹ * (y * v) * g₀ := by rw [← hg₀]; group
    rw [h6]
    exact (isConj_iff.2 ⟨g₀⁻¹, by group⟩ : IsConj (y * v) (g₀⁻¹ * (y * v) * g₀)).symm.trans hyvx
  obtain ⟨d, hd, hdv⟩ := L.exists_conj_sigma5 h1 h2 h3
  have hdv' : d⁻¹ * v * d = g₀⁻¹ * v * g₀ := by
    calc d⁻¹ * v * d = d⁻¹ * (d * (g₀⁻¹ * v * g₀) * d⁻¹) * d := by rw [hdv]
      _ = g₀⁻¹ * v * g₀ := by group
  have hgv : (g₀ * d⁻¹) * v * (g₀ * d⁻¹)⁻¹ = v := by
    calc (g₀ * d⁻¹) * v * (g₀ * d⁻¹)⁻¹ = g₀ * (d⁻¹ * v * d) * g₀⁻¹ := by group
      _ = g₀ * (g₀⁻¹ * v * g₀) * g₀⁻¹ := by rw [hdv']
      _ = v := by group
  refine ⟨g₀ * d⁻¹, ?_, ?_⟩
  · calc g₀ * d⁻¹ * v = ((g₀ * d⁻¹) * v * (g₀ * d⁻¹)⁻¹) * (g₀ * d⁻¹) := by group
      _ = v * (g₀ * d⁻¹) := by rw [hgv]
  · have hdx' : d⁻¹ * x * d = x := by
      calc d⁻¹ * x * d = d⁻¹ * (x * d) := by group
        _ = d⁻¹ * (d * x) := by rw [hd]
        _ = x := by group
    calc g₀ * d⁻¹ * x * (g₀ * d⁻¹)⁻¹ = g₀ * (d⁻¹ * x * d) * g₀⁻¹ := by group
      _ = g₀ * x * g₀⁻¹ := by rw [hdx']
      _ = y := hg₀

theorem EG_class5
    {y : G} (hyE : y ∈ L.EG) (hy1 : y ≠ 1) (hyv : y ≠ L4.vElt x a) :
    ∃ g : G, g * L4.vElt x a = L4.vElt x a * g ∧ g * x * g⁻¹ = y := by
  obtain ⟨hyS, hψy⟩ := L.mem_EG.1 hyE
  have hyc : y * L4.vElt x a = L4.vElt x a * y := by
    have := EG_comm L y hyE _ L.v_mem_EG
    exact this
  let yS' : ↥S := ⟨y, hyS⟩
  let vS' : ↥S := ⟨L4.vElt x a, L.hvS⟩
  let xS' : ↥S := ⟨x, L.hxS⟩
  have hsq : yS' * yS' = 1 := L.hψ.inj (by rw [map_mul, map_one]; exact E9_sq _ hψy)
  have hy2 : (y : G) * y = 1 := congrArg Subtype.val hsq
  have hne : (y : G) ≠ 1 := hy1
  have hord : orderOf yS' = 2 := L4.orderOf_eq_two_of_mul_self yS' hy2 hne
  have hxord : orderOf xS' = 2 := L4.orderOf_eq_two_of_mul_self _ (L4.x_mul_self h) h.x_ne_one
  have hψsq : L.ψ yS' * L.ψ yS' = 1 := by rw [← map_mul, hsq, map_one]
  have hψne : L.ψ yS' ≠ 1 := fun h1 =>
    hne (congrArg Subtype.val (L.hψ.inj (h1.trans (map_one _).symm)))
  have hψv : L.ψ yS' ≠ yS := fun h1 =>
    hyv (congrArg Subtype.val (L.hψ.inj (h1.trans L.hψ.v_eq.symm)))
  have hchar := (E9_char (L.hψ.mem yS') hψsq hψne).1 ⟨hψy, hψv⟩
  have hyx : IsConj y x := by
    have := (L.hψ.conj yS' xS' hord hxord).2 (by
      show numMoved (L.ψ yS') = numMoved (L.ψ ⟨x, L.hxS⟩)
      rw [L.hψ.x_eq]
      exact hchar.1.trans nmE_f1.symm)
    exact this
  have hyvS : y * L4.vElt x a ∈ S := mul_mem hyS L.hvS
  let yvS : ↥S := ⟨y * L4.vElt x a, hyvS⟩
  have hyvsq : (y * L4.vElt x a) * (y * L4.vElt x a) = 1 := by
    calc y * L4.vElt x a * (y * L4.vElt x a) = y * (L4.vElt x a * y) * L4.vElt x a := by group
      _ = y * (y * L4.vElt x a) * L4.vElt x a := by rw [← hyc]
      _ = (y * y) * (L4.vElt x a * L4.vElt x a) := by group
      _ = 1 := by rw [hy2, L4.v_mul_self h, one_mul]
  have hyvne : y * L4.vElt x a ≠ 1 := by
    intro h1
    apply hyv
    calc y = y * L4.vElt x a * (L4.vElt x a)⁻¹ := by group
      _ = (L4.vElt x a)⁻¹ := by rw [h1, one_mul]
      _ = L4.vElt x a := inv_eq_of_mul_eq_one_right (L4.v_mul_self h)
  have hyvord : orderOf yvS = 2 := L4.orderOf_eq_two_of_mul_self yvS hyvsq hyvne
  have hψyv : L.ψ yvS = L.ψ yS' * yS := by
    have : yvS = yS' * vS' := rfl
    rw [this, map_mul, L.hψ.v_eq]
  have hyvx : IsConj (y * L4.vElt x a) x := by
    have := (L.hψ.conj yvS xS' hyvord hxord).2 (by
      show numMoved (L.ψ yvS) = numMoved (L.ψ ⟨x, L.hxS⟩)
      rw [L.hψ.x_eq, hψyv]
      exact hchar.2.trans nmE_f1.symm)
    exact this
  exact L.exists_conj_Cv5 hyx hyc hyvx

theorem cent_xv_T
    {g : G} (hgx : g * x = x * g) (hgv : g * L4.vElt x a = L4.vElt x a * g) :
    g ∈ T := by
  let gC : ↥(centralizer ({x} : Set G)) := ⟨g, mem_centralizer_singleton_iff.2 hgx⟩
  let vC : ↥(centralizer ({x} : Set G)) := ⟨L4.vElt x a, h.T_le_C (L4.v_mem_T h)⟩
  have hιv : ((L.ι vC : Fgrp 5) : Amb 5) = vhat5 := L.iota_v
  have hcomm : ((L.ι gC : Fgrp 5) : Amb 5) * vhat5 = vhat5 * ((L.ι gC : Fgrp 5) : Amb 5) := by
    have h1 : gC * vC = vC * gC := Subtype.ext hgv
    have h2 := congrArg (fun z => ((L.ι z : Fgrp 5) : Amb 5)) h1
    simp only [map_mul, Subgroup.coe_mul, hιv] at h2
    exact h2
  exact (L.hιT gC).2 (cent_vhat5 (L.ι gC).2 hcomm)

theorem D_norm5
    {g e : G} (hgx : g * x = x * g) (hgv : g * L4.vElt x a = L4.vElt x a * g)
    (he : e ∈ L.EG) : g * e * g⁻¹ ∈ L.EG :=
  L.S_norm_EG g (h.T_lt_S.le (L.cent_xv_T hgx hgv)) e he

end Loc5

end CFSG.GH74.GLS.C3.Layer2.L5
