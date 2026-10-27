module

public import CFSG.GH74.GLS.C3.Layer2.L4Fusion
public import CFSG.GH74.GLS.C3.Layer2.L4End
public import CFSG.GH74.GLS.C3.Layer2.L4ModelDefs

public section

namespace CFSG.GH74.GLS.C3.Layer2.L4

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer2
open CFSG.GH74.GLS.C3.Layer2.Model

abbrev vElt {G : Type} [Group G] (x a : G) : G := x * (a * x * a⁻¹)

structure E1Pkg (n : ℕ) [NeZero n] (α : ↥(T0 n) ≃* ↥(T0 n)) (X V : Set ↥(T0 n))
    (E : Subgroup ↥(T0 n)) : Prop where
  mem : ∀ t : ↥(T0 n), t ∈ E ↔ (t = 1 ∨ t = vHat n α ∨
    (orderOf t = 2 ∧ t ∈ X ∧ t * vHat n α = vHat n α * t ∧ t * vHat n α ∈ X))
  card : Nat.card E = 8
  comm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a
  sq : ∀ a ∈ E, a * a = 1
  T_norm : ∀ t : ↥(T0 n), ∀ e ∈ E, t * e * t⁻¹ ∈ E
  alpha_norm : ∀ e ∈ E, α e ∈ E
  D_norm : ∀ g ∈ Fgrp n, g * ((vHat n α : ↥(T0 n)) : Amb n) = ((vHat n α : ↥(T0 n)) : Amb n) * g →
    ∀ e ∈ E, g * (e : Amb n) * g⁻¹ ∈ liftT n E
  sigma : ∀ s t : ↥(T0 n), orderOf s = 2 → orderOf t = 2 → s ∈ V → t ∈ V → x0T n * s ∈ X →
    x0T n * t ∈ X → ∃ g ∈ Fgrp n, g * (s : Amb n) * g⁻¹ = (t : Amb n)
  hcard : Nat.card ↥(Hgrp n ((vHat n α : ↥(T0 n)) : Amb n)) = if n = 6 then 64 else 192

section Basic

variable {G : Type} [Group G] [Finite G] {n : ℕ} [NeZero n] {x : G} {K T Q S : Subgroup G} {a : G}

omit [NeZero n] in
theorem x_mul_self (h : IsAConfig n x K T Q S a) : x * x = 1 := by
  have := pow_orderOf_eq_one x
  rwa [h.x_order, sq] at this

omit [NeZero n] in
theorem y_mul_self (h : IsAConfig n x K T Q S a) : (a * x * a⁻¹) * (a * x * a⁻¹) = 1 := by
  calc a * x * a⁻¹ * (a * x * a⁻¹) = a * (x * x) * a⁻¹ := by group
    _ = 1 := by rw [x_mul_self h]; group

omit [NeZero n] in
theorem v_mul_self (h : IsAConfig n x K T Q S a) : vElt x a * vElt x a = 1 := by
  have hc := h.conj_x_comm h.x_mem_T
  calc x * (a * x * a⁻¹) * (x * (a * x * a⁻¹))
      = x * ((a * x * a⁻¹) * x) * (a * x * a⁻¹) := by group
    _ = x * (x * (a * x * a⁻¹)) * (a * x * a⁻¹) := by rw [← hc]
    _ = (x * x) * ((a * x * a⁻¹) * (a * x * a⁻¹)) := by group
    _ = 1 := by rw [x_mul_self h, y_mul_self h, one_mul]

omit [NeZero n] in
theorem v_ne_one (h : IsAConfig n x K T Q S a) : vElt x a ≠ 1 := by
  intro h1
  apply h.a_conj_x_ne
  have h2 : a * x * a⁻¹ = x⁻¹ := eq_inv_of_mul_eq_one_right h1
  rw [h2]
  exact inv_eq_of_mul_eq_one_right (x_mul_self h)

omit [NeZero n] in
theorem v_mem_T (h : IsAConfig n x K T Q S a) : vElt x a ∈ T := mul_mem h.x_mem_T h.conj_x_mem

omit [NeZero n] in
theorem T_le_centralizer_v (h : IsAConfig n x K T Q S a) :
    T ≤ centralizer ({vElt x a} : Set G) :=
  le_sup_left.trans h.sup_le_centralizer_v

omit [NeZero n] in
theorem a_mem_centralizer_v (h : IsAConfig n x K T Q S a) :
    a ∈ centralizer ({vElt x a} : Set G) :=
  h.sup_le_centralizer_v (le_sup_right (a := T) (mem_zpowers a))

omit [NeZero n] in
theorem x_mem_centralizer_v (h : IsAConfig n x K T Q S a) :
    x ∈ centralizer ({vElt x a} : Set G) :=
  T_le_centralizer_v h h.x_mem_T

omit [NeZero n] in
theorem x_mul_v (h : IsAConfig n x K T Q S a) : x * vElt x a = a * x * a⁻¹ := by
  calc x * (x * (a * x * a⁻¹)) = (x * x) * (a * x * a⁻¹) := by group
    _ = a * x * a⁻¹ := by rw [x_mul_self h, one_mul]

end Basic

section Model

variable {G : Type} [Group G] [Finite G] {n : ℕ} [NeZero n] {x : G} {K T Q S : Subgroup G} {a : G}
  {h : IsAConfig n x K T Q S a} (c : Coord h)

theorem x0T_comm (s : ↥(T0 n)) : s * x0T n = x0T n * s :=
  Subtype.ext (x0_central n (T0_le_Fgrp n s.2))

theorem vHat_comm (α : ↥(T0 n) ≃* ↥(T0 n)) (t : ↥(T0 n)) : t * vHat n α = vHat n α * t := by
  obtain ⟨t', rfl⟩ := α.surjective t
  have h1 : α t' * α (x0T n) = α (x0T n) * α t' := by
    rw [← map_mul, ← map_mul, x0T_comm]
  unfold vHat
  calc α t' * (x0T n * α (x0T n)) = (α t' * x0T n) * α (x0T n) := by rw [mul_assoc]
    _ = (x0T n * α t') * α (x0T n) := by rw [x0T_comm]
    _ = x0T n * (α t' * α (x0T n)) := by rw [mul_assoc]
    _ = x0T n * (α (x0T n) * α t') := by rw [h1]
    _ = (x0T n * α (x0T n)) * α t' := by rw [mul_assoc]

theorem tau_mem_XSet_iff (t : ↥T) : c.tau t ∈ c.XSet ↔ IsConj (t : G) x := by
  show IsConj ((c.tau.symm (c.tau t) : ↥T) : G) x ↔ _
  rw [MulEquiv.symm_apply_apply]

theorem tau_mem_VSet_iff (t : ↥T) : c.tau t ∈ c.VSet ↔ IsConj (t : G) (vElt x a) := by
  show IsConj ((c.tau.symm (c.tau t) : ↥T) : G) (x * (a * x * a⁻¹)) ↔ _
  rw [MulEquiv.symm_apply_apply]

@[expose] def vT (h : IsAConfig n x K T Q S a) : ↥T := ⟨vElt x a, v_mem_T h⟩

theorem tau_vT : c.tau (vT h) = vHat n c.alpha := by
  have := c.x0T_mul_alpha
  unfold vHat
  rw [this]
  congr 1

theorem x0T_vHat_mem_XSet : x0T n * vHat n c.alpha ∈ c.XSet := by
  rw [← c.tau_xT, ← tau_vT c, ← map_mul, tau_mem_XSet_iff]
  show IsConj (x * vElt x a) x
  rw [x_mul_v h]
  exact (isConj_iff.2 ⟨a, rfl⟩ : IsConj x (a * x * a⁻¹)).symm

end Model

section Eg

variable {G : Type} [Group G] [Finite G] {n : ℕ} [NeZero n] {x : G} {K T Q S : Subgroup G} {a : G}
  {h : IsAConfig n x K T Q S a} (c : Coord h)

@[expose] noncomputable def Eg (c : Coord h) (E : Subgroup ↥(T0 n)) : Subgroup G :=
  (E.map c.tau.symm.toMonoidHom).map T.subtype

theorem mem_Eg {E : Subgroup ↥(T0 n)} {y : G} :
    y ∈ Eg c E ↔ ∃ t ∈ E, ((c.tau.symm t : ↥T) : G) = y := by
  constructor
  · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨t, ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨_, ⟨t, ht, rfl⟩, rfl⟩

theorem mem_Eg_iff {E : Subgroup ↥(T0 n)} (t : ↥T) : (t : G) ∈ Eg c E ↔ c.tau t ∈ E := by
  rw [mem_Eg]
  constructor
  · rintro ⟨s, hs, hst⟩
    have : c.tau.symm s = t := Subtype.ext hst
    rw [← this, MulEquiv.apply_symm_apply]
    exact hs
  · intro ht
    exact ⟨c.tau t, ht, by rw [MulEquiv.symm_apply_apply]⟩

theorem Eg_le_T {E : Subgroup ↥(T0 n)} : Eg c E ≤ T := by
  intro y hy
  obtain ⟨t, -, rfl⟩ := (mem_Eg c).1 hy
  exact (c.tau.symm t).2

variable {E : Subgroup ↥(T0 n)} (hE : E1Pkg n c.alpha c.XSet c.VSet E)
include hE

theorem Eg_comm : ∀ y₁ ∈ Eg c E, ∀ y₂ ∈ Eg c E, y₁ * y₂ = y₂ * y₁ := by
  intro y₁ h₁ y₂ h₂
  obtain ⟨t₁, ht₁, rfl⟩ := (mem_Eg c).1 h₁
  obtain ⟨t₂, ht₂, rfl⟩ := (mem_Eg c).1 h₂
  have h3 : c.tau.symm t₁ * c.tau.symm t₂ = c.tau.symm t₂ * c.tau.symm t₁ := by
    rw [← map_mul, ← map_mul, hE.comm t₁ ht₁ t₂ ht₂]
  exact congrArg Subtype.val h3

theorem Eg_sq : ∀ y ∈ Eg c E, y * y = 1 := by
  intro y hy
  obtain ⟨t, ht, rfl⟩ := (mem_Eg c).1 hy
  have h3 : c.tau.symm t * c.tau.symm t = 1 := by
    rw [← map_mul, hE.sq t ht, map_one]
  exact congrArg Subtype.val h3

theorem Eg_card : Nat.card (Eg c E) = 8 := by
  have h1 : Nat.card (Eg c E) = Nat.card E := by
    unfold Eg
    rw [Subgroup.card_map_of_injective T.subtype_injective,
      Subgroup.card_map_of_injective (f := c.tau.symm.toMonoidHom)
        (fun a b hab => c.tau.symm.injective hab)]
  rw [h1]
  exact hE.card

theorem v_mem_Eg : vElt x a ∈ Eg c E := by
  have := (mem_Eg_iff c (E := E) (vT h)).2 (by
    rw [tau_vT c]
    exact (hE.mem _).2 (Or.inr (Or.inl rfl)))
  exact this

theorem x_mem_Eg : x ∈ Eg c E := by
  have hx : orderOf (x0T n) = 2 := by
    rw [← c.tau_xT, MulEquiv.orderOf_eq]
    rw [← Subgroup.orderOf_coe]
    exact h.x_order
  have := (mem_Eg_iff c (E := E) ⟨x, h.x_mem_T⟩).2 (by
    rw [c.tau_xT]
    exact (hE.mem _).2 (Or.inr (Or.inr ⟨hx, c.x0T_mem_XSet, vHat_comm c.alpha _,
      x0T_vHat_mem_XSet c⟩)))
  exact this

theorem Eg_conj_T : ∀ t ∈ T, ∀ e ∈ Eg c E, t * e * t⁻¹ ∈ Eg c E := by
  intro t ht e he
  obtain ⟨ε, hε, rfl⟩ := (mem_Eg c).1 he
  have h1 : (⟨t, ht⟩ : ↥T) * c.tau.symm ε * (⟨t, ht⟩ : ↥T)⁻¹ =
      c.tau.symm (c.tau ⟨t, ht⟩ * ε * (c.tau ⟨t, ht⟩)⁻¹) := by
    rw [map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
  rw [mem_Eg]
  exact ⟨_, hE.T_norm (c.tau ⟨t, ht⟩) ε hε, congrArg Subtype.val h1.symm⟩

theorem Eg_conj_a : ∀ e ∈ Eg c E, a * e * a⁻¹ ∈ Eg c E := by
  intro e he
  obtain ⟨ε, hε, rfl⟩ := (mem_Eg c).1 he
  have h1 : c.tau.symm (c.alpha ε) = conjAutT h.a_mem.2.1 (c.tau.symm ε) := by
    simp [Coord.alpha]
  rw [mem_Eg]
  exact ⟨c.alpha ε, hE.alpha_norm ε hε, by rw [h1]; rfl⟩

theorem S_norm_Eg (hS : S = T ⊔ zpowers a) : ∀ s ∈ S, ∀ e ∈ Eg c E, s * e * s⁻¹ ∈ Eg c E := by
  have hT : T ≤ normalizer (Eg c E : Set G) := fun t ht =>
    TIData.mem_normalizer_of_forall _ (Eg_conj_T c hE t ht)
  have ha : a ∈ normalizer (Eg c E : Set G) :=
    TIData.mem_normalizer_of_forall _ (Eg_conj_a c hE)
  have hS' : S ≤ normalizer (Eg c E : Set G) :=
    hS.le.trans (sup_le hT (zpowers_le.2 ha))
  intro s hs e he
  exact ((mem_normalizer_iff.1 (hS' hs)) e).1 he

end Eg

section Sigma

variable {G : Type} [Group G] [Finite G] {n : ℕ} [NeZero n] {x : G} {K T Q S : Subgroup G} {a : G}
  {h : IsAConfig n x K T Q S a} (c : Coord h)

omit [Finite G] in
theorem orderOf_eq_two_of_mul_self {H : Subgroup G} (t : ↥H) (h1 : (t : G) * (t : G) = 1)
    (h2 : (t : G) ≠ 1) : orderOf t = 2 := by
  rw [← Subgroup.orderOf_coe]
  exact orderOf_eq_prime (by rw [sq]; exact h1) h2

variable {E : Subgroup ↥(T0 n)} (hE : E1Pkg n c.alpha c.XSet c.VSet E)
include hE

theorem exists_conj_sigma (_hn : n = 6 ∨ n = 7) {v₁ : G} (hv1 : IsConj v₁ (vElt x a))
    (hc : v₁ * x = x * v₁) (hxv : IsConj (x * v₁) x) :
    ∃ d : G, d * x = x * d ∧ d * v₁ * d⁻¹ = vElt x a := by
  obtain ⟨g₁, hg₁⟩ := isConj_iff.1 hv1
  have hv1sq : v₁ * v₁ = 1 := by
    have h2 : v₁ = g₁⁻¹ * vElt x a * g₁ := by rw [← hg₁]; group
    rw [h2]
    calc g₁⁻¹ * vElt x a * g₁ * (g₁⁻¹ * vElt x a * g₁)
        = g₁⁻¹ * (vElt x a * vElt x a) * g₁ := by group
      _ = 1 := by rw [v_mul_self h]; group
  have hv1C : v₁ ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.2 hc
  obtain ⟨k, hk, hkT⟩ := exists_mem_conj_le_of_isSylowOf (p := 2) h.sylowT
    (X := zpowers v₁) (zpowers_le.2 hv1C) (TIData.isPGroup_zpowers hv1sq)
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
    apply v_ne_one h
    obtain ⟨g₂, hg₂⟩ := isConj_iff.1 hv1
    rw [h3] at hg₂
    simpa using hg₂.symm
  have hs_V : c.tau t₂ ∈ c.VSet := by
    rw [tau_mem_VSet_iff]
    show IsConj (k⁻¹ * v₁ * k) (vElt x a)
    exact (isConj_iff.2 ⟨k⁻¹, by group⟩ : IsConj v₁ (k⁻¹ * v₁ * k)).symm.trans hv1
  have hs_ord : orderOf (c.tau t₂) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_two_of_mul_self t₂ hv2sq hv2ne
  have hs_X : x0T n * c.tau t₂ ∈ c.XSet := by
    rw [← c.tau_xT, ← map_mul, tau_mem_XSet_iff]
    show IsConj (x * (k⁻¹ * v₁ * k)) x
    have h2 : x * (k⁻¹ * v₁ * k) = k⁻¹ * (x * v₁) * k := by
      calc x * (k⁻¹ * v₁ * k) = (x * k⁻¹) * v₁ * k := by group
        _ = (k⁻¹ * x) * v₁ * k := by rw [hxk']
        _ = k⁻¹ * (x * v₁) * k := by group
    rw [h2]
    exact (isConj_iff.2 ⟨k⁻¹, by group⟩ : IsConj (x * v₁) (k⁻¹ * (x * v₁) * k)).symm.trans hxv
  have hvV : vHat n c.alpha ∈ c.VSet := by
    rw [← tau_vT c, tau_mem_VSet_iff]
    exact IsConj.refl _
  have hvord : orderOf (vHat n c.alpha) = 2 := by
    rw [← tau_vT c, MulEquiv.orderOf_eq]
    exact orderOf_eq_two_of_mul_self (vT h) (v_mul_self h) (v_ne_one h)
  obtain ⟨g, hg, hgs⟩ := hE.sigma (c.tau t₂) (vHat n c.alpha) hs_ord hvord hs_V hvV hs_X
    (x0T_vHat_mem_XSet c)
  set d₂ : ↥(centralizer ({x} : Set G)) := c.ι.symm ⟨g, hg⟩ with hd₂
  have hι_t₂ : ((c.ι ⟨k⁻¹ * v₁ * k, h.T_le_C hv2T⟩ : Fgrp n) : Amb n) =
      ((c.tau t₂ : ↥(T0 n)) : Amb n) :=
    (c.tau_apply t₂).symm
  have hι_v : ((c.ι ⟨vElt x a, h.T_le_C (v_mem_T h)⟩ : Fgrp n) : Amb n) =
      ((vHat n c.alpha : ↥(T0 n)) : Amb n) := by
    rw [← tau_vT c]
    exact (c.tau_apply (vT h)).symm
  have hconj : d₂ * (⟨k⁻¹ * v₁ * k, h.T_le_C hv2T⟩ : ↥(centralizer ({x} : Set G))) * d₂⁻¹ =
      ⟨vElt x a, h.T_le_C (v_mem_T h)⟩ := by
    apply c.ι.injective
    apply Subtype.ext
    have e : c.ι d₂ = ⟨g, hg⟩ := MulEquiv.apply_symm_apply _ _
    rw [map_mul, map_mul, map_inv, e, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      hι_t₂, hι_v]
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
      _ = vElt x a := h4

theorem exists_conj_Cv (hn : n = 6 ∨ n = 7) {y : G} (hyx : IsConj y x)
    (hyv : y * vElt x a = vElt x a * y) (hyvx : IsConj (y * vElt x a) x) :
    ∃ g : G, g * vElt x a = vElt x a * g ∧ g * x * g⁻¹ = y := by
  obtain ⟨g₀, hg₀⟩ := isConj_iff.1 hyx.symm
  set v : G := vElt x a with hv
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
  obtain ⟨d, hd, hdv⟩ := exists_conj_sigma c hE hn h1 h2 h3
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

theorem Eg_class (hn : n = 6 ∨ n = 7) {y : G} (hyE : y ∈ Eg c E) (hy1 : y ≠ 1)
    (hyv : y ≠ vElt x a) (hyc : y * vElt x a = vElt x a * y) :
    ∃ g : G, g * vElt x a = vElt x a * g ∧ g * x * g⁻¹ = y := by
  have hyT : y ∈ T := Eg_le_T c hyE
  let yT : ↥T := ⟨y, hyT⟩
  have hτ : c.tau yT ∈ E := (mem_Eg_iff c yT).1 hyE
  rw [hE.mem] at hτ
  rcases hτ with h1 | h1 | ⟨-, hX, -, hXv⟩
  · exfalso
    apply hy1
    have : yT = 1 := c.tau.injective (by rw [h1, map_one])
    exact congrArg Subtype.val this
  · exfalso
    apply hyv
    have : yT = vT h := c.tau.injective (by rw [h1, tau_vT c])
    exact congrArg Subtype.val this
  · have hyx : IsConj y x := (tau_mem_XSet_iff c yT).1 hX
    have hyvx : IsConj (y * vElt x a) x := by
      rw [← tau_vT c, ← map_mul, tau_mem_XSet_iff] at hXv
      exact hXv
    exact exists_conj_Cv c hE hn hyx hyc hyvx

theorem D_norm_Eg {g e : G} (hgx : g * x = x * g) (hgv : g * vElt x a = vElt x a * g)
    (he : e ∈ Eg c E) : g * e * g⁻¹ ∈ Eg c E := by
  obtain ⟨ε, hε, rfl⟩ := (mem_Eg c).1 he
  set eT : ↥T := c.tau.symm ε with heT
  let gC : ↥(centralizer ({x} : Set G)) := ⟨g, mem_centralizer_singleton_iff.2 hgx⟩
  let eC : ↥(centralizer ({x} : Set G)) := ⟨(eT : G), h.T_le_C eT.2⟩
  let vC : ↥(centralizer ({x} : Set G)) := ⟨vElt x a, h.T_le_C (v_mem_T h)⟩
  have hιe : ((c.ι eC : Fgrp n) : Amb n) = (ε : Amb n) := by
    have := c.tau_apply eT
    rw [heT, MulEquiv.apply_symm_apply] at this
    exact this.symm
  have hιv : ((c.ι vC : Fgrp n) : Amb n) = ((vHat n c.alpha : ↥(T0 n)) : Amb n) := by
    rw [← tau_vT c]
    exact (c.tau_apply (vT h)).symm
  have hcomm : ((c.ι gC : Fgrp n) : Amb n) * ((vHat n c.alpha : ↥(T0 n)) : Amb n) =
      ((vHat n c.alpha : ↥(T0 n)) : Amb n) * ((c.ι gC : Fgrp n) : Amb n) := by
    have h1 : gC * vC = vC * gC := Subtype.ext hgv
    have h2 := congrArg (fun z => ((c.ι z : Fgrp n) : Amb n)) h1
    simp only [map_mul, Subgroup.coe_mul, hιv] at h2
    exact h2
  have hmem := hE.D_norm (c.ι gC : Fgrp n) (c.ι gC).2 hcomm ε hε
  rw [hιe.symm] at hmem
  obtain ⟨ε', hε', hε'eq⟩ := (Subgroup.mem_map.1 (by simpa [liftT] using hmem :
    ((c.ι gC : Fgrp n) : Amb n) * ((c.ι eC : Fgrp n) : Amb n) * ((c.ι gC : Fgrp n) : Amb n)⁻¹ ∈
      liftT n E))
  set r : ↥(centralizer ({x} : Set G)) := gC * eC * gC⁻¹ with hr
  have hιr : ((c.ι r : Fgrp n) : Amb n) = (ε' : Amb n) := by
    rw [hr, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hε'eq.symm
  have hrT : (r : G) ∈ T := (c.ι_T r).2 (by rw [hιr]; exact ε'.2)
  have hτr : c.tau ⟨(r : G), hrT⟩ = ε' := Subtype.ext (by rw [c.tau_apply]; exact hιr)
  have := (mem_Eg_iff c (E := E) ⟨(r : G), hrT⟩).2 (by rw [hτr]; exact hε')
  exact this

end Sigma

section Main

variable {G : Type} [Group G] [Finite G] {n : ℕ} [NeZero n] {x : G} {K T Q S : Subgroup G} {a : G}
  {h : IsAConfig n x K T Q S a} (c : Coord h) {E : Subgroup ↥(T0 n)}
  (hE : E1Pkg n c.alpha c.XSet c.VSet E)
include hE

theorem normalizer_Eg
    (hZD : CFSG.GH74.Uniqueness.S_ZD) (hn : n = 6 ∨ n = 7) (hG : IsSimpleGroup G)
    (hnab : ∃ u w : G, u * w ≠ w * u) (hM : ModelIso n c.alpha c.uElt c.XSet c.VSet)
    (hZc : ∀ s : ↥(T0 n), (∀ t : ↥(T0 n), s * t = t * s) → c.alpha s = s → s * s = 1 → s ≠ 1 →
      s = vHat n c.alpha) :
    ∀ g : G, g * vElt x a = vElt x a * g → ∀ e ∈ Eg c E, g * e * g⁻¹ ∈ Eg c E := by
  obtain ⟨hS128, hSeq, ⟨y₀, hy₀S, hy₀sq, hy₀T⟩, hfus⟩ := fusion_facts h c hn hG hnab hM
  have hT64 : Nat.card T = 64 := c.card_T hn
  have hTS : T ≤ S := h.T_lt_S.le
  set Cv : Subgroup G := centralizer ({vElt x a} : Set G) with hCv
  have hSCv : S ≤ Cv := by
    rw [hSeq]
    exact sup_le (T_le_centralizer_v h) (zpowers_le.2 (a_mem_centralizer_v h))
  have hEgT : Eg c E ≤ T := Eg_le_T c
  have hEgCv : Eg c E ≤ Cv := hEgT.trans (T_le_centralizer_v h)
  have hmemCv : ∀ g : G, g ∈ Cv ↔ g * vElt x a = vElt x a * g := fun g =>
    mem_centralizer_singleton_iff
  have hCT : centralizer ({x} : Set G) ⊓ S = T :=
    h.sylowT.eq_of_le (le_inf h.T_le_C hTS) inf_le_left
      (IsPGroup.to_le h.sylowS.isPGroup inf_le_right)
  let v' : ↥Cv := ⟨vElt x a, (hmemCv _).2 rfl⟩
  let x' : ↥Cv := ⟨x, x_mem_centralizer_v h⟩
  let a' : ↥Cv := ⟨a, a_mem_centralizer_v h⟩
  let Zs : Set ↥Cv := {z | ∃ g : ↥Cv, g * x' * g⁻¹ = z}
  let S' : Subgroup ↥Cv := S.subgroupOf Cv
  let E' : Subgroup ↥Cv := (Eg c E).subgroupOf Cv
  have hx'sq : x' * x' = 1 := Subtype.ext (x_mul_self h)
  have hx'v : x' * v' = a' * x' * a'⁻¹ := Subtype.ext (x_mul_v h)
  have hv'c : ∀ g : ↥Cv, g * v' = v' * g := fun g =>
    Subtype.ext (mem_centralizer_singleton_iff.1 g.2)
  have hZmv : ∀ z ∈ Zs, z * v' ∈ Zs := by
    rintro _ ⟨g, rfl⟩
    refine ⟨g * a', ?_⟩
    calc g * a' * x' * (g * a')⁻¹ = g * (a' * x' * a'⁻¹) * g⁻¹ := by group
      _ = g * (x' * v') * g⁻¹ := by rw [hx'v]
      _ = g * x' * (v' * g⁻¹) := by group
      _ = g * x' * (g⁻¹ * v') := by rw [← hv'c g⁻¹]
      _ = g * x' * g⁻¹ * v' := by group
  have hconjord : ∀ g : ↥Cv, orderOf ((g : G) * x * (g : G)⁻¹) = 2 := by
    intro g
    have := MulEquiv.orderOf_eq (MulAut.conj (g : G)) x
    simpa [MulAut.conj_apply, h.x_order] using this
  have hTI : TIData v' Zs S' E' x' := by
    refine ⟨?_, ?_, hv'c, ?_, ?_, ?_, ?_, hZmv, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact Subtype.ext (v_mul_self h)
    · exact fun h1 => v_ne_one h (congrArg Subtype.val h1)
    · rintro _ ⟨g, rfl⟩
      calc g * x' * g⁻¹ * (g * x' * g⁻¹) = g * (x' * x') * g⁻¹ := by group
        _ = 1 := by rw [hx'sq]; group
    · rintro _ ⟨g, rfl⟩ h1
      have h2 : x' = 1 := by
        calc x' = g⁻¹ * (g * x' * g⁻¹) * g := by group
          _ = 1 := by rw [h1]; group
      have h3 : x = 1 := congrArg Subtype.val h2
      have h4 := h.x_order
      rw [h3, orderOf_one] at h4
      omega
    · rintro ⟨g, hg⟩
      have hgc : (g : G) * x * (g : G)⁻¹ = vElt x a := congrArg Subtype.val hg
      exact h.not_isConj_x_v hT64 (isConj_iff.2 ⟨g, hgc⟩)
    · rintro _ ⟨g', rfl⟩ g
      exact ⟨g * g', by group⟩
    ·
      show IsSylowOf 2 (S.subgroupOf Cv) ⊤
      rw [← isSylowOf_map_subtype_iff Cv, Subgroup.subgroupOf_map_subtype, Subgroup.map_top,
        Subgroup.range_subtype, inf_eq_left.2 hSCv]
      exact h.sylowS.of_le hSCv le_top
    · exact fun e he => hTS (hEgT he)
    · exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEgCv).toEquiv).trans (Eg_card c hE)
    · exact fun a ha b hb => Subtype.ext (Eg_comm c hE a ha b hb)
    · exact fun a ha => Subtype.ext (Eg_sq c hE a ha)
    · exact v_mem_Eg c hE
    · exact fun s hs e he => S_norm_Eg c hE hSeq (s : G) hs (e : G) he
    ·
      intro y hy
      constructor
      · rintro ⟨g, hg⟩
        have hgy : (g : G) * x * (g : G)⁻¹ = (y : G) := congrArg Subtype.val hg
        have hxy : IsConj x (y : G) := isConj_iff.2 ⟨g, hgy⟩
        have hy2 : orderOf (y : G) = 2 := by rw [← hgy]; exact hconjord g
        have hyT : (y : G) ∈ T := by
          by_contra hnT
          exact hfus (y : G) hy hy2 hnT hxy
        let yT : ↥T := ⟨(y : G), hyT⟩
        have hy1 : (yT : G) * (yT : G) = 1 := by
          have h5 := pow_orderOf_eq_one (y : G)
          rw [hy2, sq] at h5
          exact h5
        have hyne : (yT : G) ≠ 1 := by
          intro h6
          rw [h6, orderOf_one] at hy2
          omega
        have hy3 : (y : G) * vElt x a ∈ ({z : G | ∃ g' : ↥Cv, (g' : G) * x * (g' : G)⁻¹ = z}) := by
          obtain ⟨g'', hg''⟩ := hZmv y ⟨g, hg⟩
          exact ⟨g'', congrArg Subtype.val hg''⟩
        have hyE : c.tau yT ∈ E := by
          rw [hE.mem]
          right; right
          refine ⟨?_, ?_, vHat_comm c.alpha _, ?_⟩
          · rw [MulEquiv.orderOf_eq]
            exact orderOf_eq_two_of_mul_self yT hy1 hyne
          · rw [tau_mem_XSet_iff]
            exact hxy.symm
          · rw [← tau_vT c, ← map_mul, tau_mem_XSet_iff]
            obtain ⟨g', hg'⟩ := hy3
            exact (isConj_iff.2 ⟨g', hg'⟩ : IsConj x ((y : G) * vElt x a)).symm
        refine ⟨(mem_Eg_iff c yT).2 hyE, ?_, ?_⟩
        · intro h7
          have : (y : G) = 1 := congrArg Subtype.val h7
          exact hyne this
        · intro h7
          have h8 : (y : G) = vElt x a := congrArg Subtype.val h7
          rw [h8] at hxy
          exact h.not_isConj_x_v hT64 hxy
      · rintro ⟨hyE, hy1, hyv⟩
        have hyvc : (y : G) * vElt x a = vElt x a * (y : G) :=
          mem_centralizer_singleton_iff.1 y.2
        obtain ⟨g, hg, hgy⟩ := Eg_class c hE hn hyE (fun h' => hy1 (Subtype.ext h'))
          (fun h' => hyv (Subtype.ext h')) hyvc
        exact ⟨⟨g, (hmemCv g).2 hg⟩, Subtype.ext hgy⟩
    · exact ⟨1, by simp⟩
    · exact x_mem_Eg c hE
    · exact fun z hz => hz
    · intro g hg e he
      have hgx : (g : G) * x = x * (g : G) := congrArg Subtype.val hg
      have hgv : (g : G) * vElt x a = vElt x a * (g : G) := mem_centralizer_singleton_iff.1 g.2
      exact D_norm_Eg c hE hgx hgv he
  have hS : Nat.card S' ≤ 128 := by
    have : Nat.card S' = Nat.card S := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSCv).toEquiv
    omega
  have hex : ∃ s ∈ S', s * s = 1 ∧ s ∉ E' :=
    ⟨⟨y₀, hSCv hy₀S⟩, hy₀S, Subtype.ext hy₀sq, fun hmem => hy₀T (hEgT hmem)⟩
  have hZS : ∀ s ∈ S', (∀ t ∈ S', s * t = t * s) → s * s = 1 → s ≠ 1 → s = v' := by
    intro s hs hcen hs2 hs1
    have hsS : (s : G) ∈ S := hs
    have hsc : ∀ t ∈ S, (s : G) * t = t * (s : G) := by
      intro t ht
      exact congrArg Subtype.val (hcen ⟨t, hSCv ht⟩ ht)
    have hsx : (s : G) ∈ centralizer ({x} : Set G) :=
      mem_centralizer_singleton_iff.2 (hsc x (hTS h.x_mem_T))
    have hsT : (s : G) ∈ T := by
      have : (s : G) ∈ centralizer ({x} : Set G) ⊓ S := ⟨hsx, hsS⟩
      rw [hCT] at this
      exact this
    let sT : ↥T := ⟨(s : G), hsT⟩
    have hσc : ∀ t : ↥(T0 n), c.tau sT * t = t * c.tau sT := by
      intro t
      obtain ⟨t'', rfl⟩ := c.tau.surjective t
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hsc (t'' : G) (hTS t''.2))
    have hσa : c.alpha (c.tau sT) = c.tau sT := by
      rw [Coord.alpha_tau]
      congr 1
      apply Subtype.ext
      show a * (s : G) * a⁻¹ = (s : G)
      have := hsc a h.a_mem.1
      calc a * (s : G) * a⁻¹ = (s : G) * a * a⁻¹ := by rw [this]
        _ = s := by group
    have hs2G : (s : G) * (s : G) = 1 := congrArg Subtype.val hs2
    have hs1G : (s : G) ≠ 1 := fun h1 => hs1 (Subtype.ext h1)
    have hσ2 : c.tau sT * c.tau sT = 1 := by
      rw [← map_mul, ← map_one c.tau]
      congr 1
      exact Subtype.ext hs2G
    have hσ1 : c.tau sT ≠ 1 := by
      intro h1
      apply hs1G
      have h3 : sT = 1 := c.tau.injective (by rw [h1, map_one])
      exact congrArg Subtype.val h3
    have h4 := hZc _ hσc hσa hσ2 hσ1
    rw [← tau_vT c] at h4
    have h5 : sT = vT h := c.tau.injective h4
    have h6 : (sT : G) = ((vT h : ↥T) : G) := congrArg Subtype.val h5
    exact Subtype.ext h6
  have hNT := normalizer_eq_top hZD hTI hS hex hZS
  intro g hg e he
  have hgC : g ∈ Cv := (hmemCv g).2 hg
  have hmem : (⟨g, hgC⟩ : ↥Cv) ∈ normalizer (E' : Set ↥Cv) := by
    rw [hNT]; exact mem_top _
  exact (mem_normalizer_iff.1 hmem ⟨e, hEgCv he⟩).1 he

end Main

end CFSG.GH74.GLS.C3.Layer2.L4
