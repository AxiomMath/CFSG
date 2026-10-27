module

public import CFSG.GH74.GLS.C3.Layer2.L4Cv6
public import CFSG.GH74.GLS.C3.Layer2.L4PartB7
public import CFSG.GH74.GLS.C3.Layer2.L4Star7

public section

namespace CFSG.GH74.GLS.C3.Layer2.L4

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer2
open CFSG.GH74.GLS.C3.Layer2.Model

@[expose] def E3Out (n : ℕ) [NeZero n] (E A : Subgroup ↥(T0 n)) (b : Fin 4 → ↥(T0 n)) : Prop :=
  ∃ w : Amb n, w ∈ Fgrp n ∧ orderOf w = 3 ∧ (∀ e ∈ liftT n E, w * e = e * w) ∧
    (∀ g ∈ Fgrp n ⊓ Subgroup.centralizer (liftT n E : Set (Amb n)),
      ∃ k : ℕ, ∃ t ∈ A, g = w ^ k * ((t : ↥(T0 n)) : Amb n)) ∧
    (∀ t ∈ A, t ∉ E → ((t : ↥(T0 n)) : Amb n) * w * ((t : ↥(T0 n)) : Amb n)⁻¹ = w⁻¹) ∧
    (∀ (t y : ↥(T0 n)) (π₁ π₂ : Equiv.Perm (Fin 4)), t ∉ A → y ∉ A → orderOf t = 2 →
      orderOf y = 2 → t * y = y * t → π₁.IsSwap → π₂.IsSwap → Equiv.Perm.Disjoint π₁ π₂ →
      (∀ i, t * b i * t⁻¹ = b (π₁ i)) → (∀ i, y * b i * y⁻¹ = b (π₂ i)) →
      ((t : ↥(T0 n)) : Amb n) * w = w * ((t : ↥(T0 n)) : Amb n)) ∧
    (∃ t y : ↥(T0 n), t ∉ A ∧ y ∉ A ∧ orderOf t = 2 ∧ orderOf y = 2 ∧ t * y = y * t ∧
      ∃ π₁ π₂ : Equiv.Perm (Fin 4), π₁.IsSwap ∧ π₂.IsSwap ∧ Equiv.Perm.Disjoint π₁ π₂ ∧
        (∀ i, t * b i * t⁻¹ = b (π₁ i)) ∧ (∀ i, y * b i * y⁻¹ = b (π₂ i)))

section Transport7

variable {G : Type} [Group G] [Finite G] {n : ℕ} [NeZero n] {x : G} {K T Q S : Subgroup G} {a : G}
  {h : IsAConfig n x K T Q S a} (c : Coord h)

theorem Eg_sq_of {E : Subgroup ↥(T0 n)} (hsq : ∀ a ∈ E, a * a = 1) :
    ∀ y ∈ Eg c E, y * y = 1 := by
  intro y hy
  obtain ⟨t, ht, rfl⟩ := (mem_Eg c).1 hy
  have h3 : c.tau.symm t * c.tau.symm t = 1 := by
    rw [← map_mul, hsq t ht, map_one]
  exact congrArg Subtype.val h3

variable {E A : Subgroup ↥(T0 n)} (hE : E1Pkg n c.alpha c.XSet c.VSet E)
  (hE2 : E2Pkg n c.alpha c.uElt c.XSet E A)
include hE hE2

omit hE in
theorem mem_Ag_char7 {y : G} : y ∈ Eg c A ↔ y ∈ T ∧ ∀ e ∈ Eg c E, y * e = e * y := by
  constructor
  · intro hy
    refine ⟨Eg_le_T c hy, fun e he => ?_⟩
    obtain ⟨t, ht, rfl⟩ := (mem_Eg c).1 hy
    obtain ⟨ε, hε, rfl⟩ := (mem_Eg c).1 he
    have h4 := (hE2.memA t).1 ht ε hε
    have h3 : c.tau.symm t * c.tau.symm ε = c.tau.symm ε * c.tau.symm t := by
      rw [← map_mul, ← map_mul, h4]
    exact congrArg Subtype.val h3
  · rintro ⟨hyT, hcomm⟩
    refine (mem_Eg_iff c (⟨y, hyT⟩ : ↥T)).2 ((hE2.memA _).2 fun ε hε => ?_)
    have heE : ((c.tau.symm ε : ↥T) : G) ∈ Eg c E := (mem_Eg c).2 ⟨ε, hε, rfl⟩
    have h1 : (⟨y, hyT⟩ : ↥T) * c.tau.symm ε = c.tau.symm ε * ⟨y, hyT⟩ :=
      Subtype.ext (hcomm _ heE)
    have h2 := congrArg c.tau h1
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
    exact h2

theorem Eg_le_Ag : Eg c E ≤ Eg c A := fun e he =>
  (mem_Ag_char7 c hE2).2 ⟨Eg_le_T c he, fun e' he' => Eg_comm c hE e he e' he'⟩

theorem S_norm_Ag (hS : S = T ⊔ zpowers a) : ∀ s ∈ S, ∀ y ∈ Eg c A, s * y * s⁻¹ ∈ Eg c A := by
  have hSN : S ≤ normalizer (T : Set G) := by
    rw [hS]
    exact sup_le Subgroup.le_normalizer (zpowers_le.2 h.a_mem.2.1)
  intro s hs y hy
  obtain ⟨hyT, hyc⟩ := (mem_Ag_char7 c hE2).1 hy
  refine (mem_Ag_char7 c hE2).2 ⟨?_, fun e he => ?_⟩
  · exact ((mem_normalizer_iff.1 (hSN hs)) y).1 hyT
  · have hs' : s⁻¹ * e * s ∈ Eg c E := by
      have := S_norm_Eg c hE hS s⁻¹ (inv_mem hs) e he
      simpa using this
    have h1 := hyc _ hs'
    calc s * y * s⁻¹ * e = s * (y * (s⁻¹ * e * s)) * s⁻¹ := by group
      _ = s * ((s⁻¹ * e * s) * y) * s⁻¹ := by rw [h1]
      _ = e * (s * y * s⁻¹) := by group

end Transport7

section IotaComm

variable {G : Type} [Group G] [Finite G] {n : ℕ} [NeZero n] {x : G} {K T Q S : Subgroup G} {a : G}
  {h : IsAConfig n x K T Q S a} (c : Coord h) {E : Subgroup ↥(T0 n)}

theorem iota_comm_of_comm {g : G} (hgx : g * x = x * g)
    (hcomm : ∀ e ∈ Eg c E, g * e = e * g) :
    ∀ ε ∈ E, ((c.ι ⟨g, mem_centralizer_singleton_iff.2 hgx⟩ : Fgrp n) : Amb n) * (ε : Amb n) =
      (ε : Amb n) * ((c.ι ⟨g, mem_centralizer_singleton_iff.2 hgx⟩ : Fgrp n) : Amb n) := by
  intro ε hε
  set eT : ↥T := c.tau.symm ε with heT
  let eC : ↥(centralizer ({x} : Set G)) := ⟨(eT : G), h.T_le_C eT.2⟩
  have hιe : ((c.ι eC : Fgrp n) : Amb n) = (ε : Amb n) := by
    have := c.tau_apply eT
    rw [heT, MulEquiv.apply_symm_apply] at this
    exact this.symm
  have heE : (eT : G) ∈ Eg c E := (mem_Eg c).2 ⟨ε, hε, rfl⟩
  have h1 : (⟨g, mem_centralizer_singleton_iff.2 hgx⟩ : ↥(centralizer ({x} : Set G))) * eC =
      eC * ⟨g, mem_centralizer_singleton_iff.2 hgx⟩ := Subtype.ext (hcomm _ heE)
  have h2 := congrArg (fun z => ((c.ι z : Fgrp n) : Amb n)) h1
  simp only [map_mul, Subgroup.coe_mul, hιe] at h2
  exact h2

end IotaComm


section Main7

variable {G : Type} [Group G] [Finite G] {n : ℕ} [NeZero n] {x : G} {K T Q S : Subgroup G} {a : G}
  {h : IsAConfig n x K T Q S a} (c : Coord h) {E A : Subgroup ↥(T0 n)}
  (hE : E1Pkg n c.alpha c.XSet c.VSet E) (hE2 : E2Pkg n c.alpha c.uElt c.XSet E A)
  (hE3 : ∀ b : Fin 4 → ↥(T0 n), Function.Injective b →
    (∀ i, b i ∈ A ∧ orderOf (b i) = 2 ∧ b i ∈ c.XSet ∧ b i ∉ E) →
    (∀ t ∈ A, orderOf t = 2 → t ∈ c.XSet → t ∉ E → ∃ i, t = b i) → E3Out n E A b)
include hE hE2 hE3

theorem exists_mulEquiv_W7_Cv
    (hZD : CFSG.GH74.Uniqueness.S_ZD) (hn : n = 7) (hG : IsSimpleGroup G)
    (hnab : ∃ u w : G, u * w ≠ w * u) (hM : ModelIso n c.alpha c.uElt c.XSet c.VSet) :
    Nonempty (Wreath.W7 ≃* ↥(centralizer ({vElt x a} : Set G))) := by
  have hn' : n = 6 ∨ n = 7 := Or.inr hn
  have hnorm := normalizer_Eg c hE hZD hn' hG hnab hM hE2.zcenter
  obtain ⟨-, hSeq, -, -⟩ := fusion_facts h c hn' hG hnab hM
  obtain ⟨RS, hRS_S, hARS_bot, hARS_top⟩ := exists_split_G c hE2 hn' hG hnab hM
  have hTS : T ≤ S := h.T_lt_S.le
  set Cv : Subgroup G := centralizer ({vElt x a} : Set G) with hCv
  have hTCv : T ≤ Cv := T_le_centralizer_v h
  have hSCv : S ≤ Cv := by
    rw [hSeq]
    exact sup_le hTCv (zpowers_le.2 (a_mem_centralizer_v h))
  have hEgT : Eg c E ≤ T := Eg_le_T c
  have hAgT : Eg c A ≤ T := Eg_le_T c
  have hEgCv : Eg c E ≤ Cv := hEgT.trans hTCv
  have hAgCv : Eg c A ≤ Cv := hAgT.trans hTCv
  have hRSCv : RS ≤ Cv := hRS_S.trans hSCv
  have hmemCv : ∀ g : G, g ∈ Cv ↔ g * vElt x a = vElt x a * g := fun g =>
    mem_centralizer_singleton_iff
  let v' : ↥Cv := ⟨vElt x a, (hmemCv _).2 rfl⟩
  let x' : ↥Cv := ⟨x, x_mem_centralizer_v h⟩
  let E' : Subgroup ↥Cv := (Eg c E).subgroupOf Cv
  let A' : Subgroup ↥Cv := (Eg c A).subgroupOf Cv
  let R' : Subgroup ↥Cv := RS.subgroupOf Cv
  let S' : Subgroup ↥Cv := S.subgroupOf Cv
  let Tm : Subgroup ↥Cv := T.subgroupOf Cv
  have hv'c : ∀ g : ↥Cv, g * v' = v' * g := fun g =>
    Subtype.ext (mem_centralizer_singleton_iff.1 g.2)
  have hSyl : IsSylowOf 2 S' ⊤ := by
    show IsSylowOf 2 (S.subgroupOf Cv) ⊤
    rw [← isSylowOf_map_subtype_iff Cv, Subgroup.subgroupOf_map_subtype, Subgroup.map_top,
      Subgroup.range_subtype, inf_eq_left.2 hSCv]
    exact h.sylowS.of_le hSCv le_top
  have hv1 : v' ≠ 1 := fun h1 => v_ne_one h (congrArg Subtype.val h1)
  have hEn : E'.Normal :=
    ⟨fun e he g => hnorm (g : G) (mem_centralizer_singleton_iff.1 g.2) (e : G) he⟩
  have hEcard : Nat.card E' = 8 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEgCv).toEquiv).trans
      ((Eg_card_of c E).trans hE.card)
  have hEcomm : ∀ a ∈ E', ∀ a' ∈ E', a * a' = a' * a := fun a ha b hb =>
    Subtype.ext (Eg_comm c hE a ha b hb)
  have hvE : v' ∈ E' := v_mem_Eg c hE
  have hxE : x' ∈ E' := x_mem_Eg c hE
  have hx1 : x' ≠ 1 := by
    intro h1
    have h3 : x = 1 := congrArg Subtype.val h1
    have h4 := h.x_order
    rw [h3, orderOf_one] at h4
    omega
  have hxv : x' ≠ v' := by
    intro h1
    have h3 : x = vElt x a := congrArg Subtype.val h1
    have h2 : a * x * a⁻¹ = 1 := by
      calc a * x * a⁻¹ = x⁻¹ * (x * (a * x * a⁻¹)) := by group
        _ = x⁻¹ * x := by rw [show x * (a * x * a⁻¹) = x from h3.symm]
        _ = 1 := by group
    have h5 : x = 1 := by
      calc x = a⁻¹ * (a * x * a⁻¹) * a := by group
        _ = 1 := by rw [h2]; group
    have h4 := h.x_order
    rw [h5, orderOf_one] at h4
    omega
  have hcls : ∀ e ∈ E', e ≠ 1 → e ≠ v' → ∃ g : ↥Cv, g * x' * g⁻¹ = e := by
    intro e he he1 hev
    obtain ⟨g, hg, hgy⟩ := Eg_class c hE hn' he (fun h' => he1 (Subtype.ext h'))
      (fun h' => hev (Subtype.ext h')) (mem_centralizer_singleton_iff.1 e.2)
    exact ⟨⟨g, (hmemCv g).2 hg⟩, Subtype.ext hgy⟩
  have hD : Nat.card ↥(centralizer ({x'} : Set ↥Cv)) = 192 := by
    rw [card_centralizer_x' c, hE.hcard]
    have hn6 : ¬ n = 6 := by omega
    simp [hn6]
  have hCcard : Nat.card ↥Cv = 1152 := by
    have := PartB6.card_of_classes v' x' E' hv1 hv'c hEn hEcard hvE hxE hx1 hxv hcls
    rw [hD] at this
    omega
  have hEA : E' ≤ A' := fun e he => Eg_le_Ag c hE hE2 he
  have hAE : ∀ t ∈ A', ∀ e ∈ E', t * e = e * t := fun t ht e he =>
    Subtype.ext (((mem_Ag_char7 c hE2).1 ht).2 e he)
  have hAcard : Nat.card A' = 16 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAgCv).toEquiv).trans
      ((Eg_card_of c A).trans hE2.cardA)
  have hAcomm : ∀ a ∈ A', ∀ a' ∈ A', a * a' = a' * a := fun a ha b hb =>
    Subtype.ext (Eg_comm_of c hE2.commA a ha b hb)
  have hAsq : ∀ a ∈ A', a * a = 1 := fun a ha => Subtype.ext (Eg_sq_of c hE2.sqA a ha)
  obtain ⟨b, hbinj, hb1, hb2, hb3⟩ := hE2.b
  let b' : Fin 4 → ↥Cv := fun i => ⟨((c.tau.symm (b i) : ↥T) : G), hTCv (c.tau.symm (b i)).2⟩
  obtain ⟨w₀, hw₀F, hw₀o, hw₀E, hw₀C0, hw₀inv, hM9all₀, hM9ex₀⟩ := hE3 b hbinj hb1 hb2
  have hvhatE : vHat n c.alpha ∈ E := (hE.mem _).2 (Or.inr (Or.inl rfl))
  have hvlift : ((vHat n c.alpha : ↥(T0 n)) : Amb n) ∈ liftT n E := ⟨_, hvhatE, rfl⟩
  let wC : ↥(centralizer ({x} : Set G)) := c.ι.symm ⟨w₀, hw₀F⟩
  have hιw : ((c.ι wC : Fgrp n) : Amb n) = w₀ := by
    show (((c.ι (c.ι.symm ⟨w₀, hw₀F⟩)) : Fgrp n) : Amb n) = w₀
    rw [MulEquiv.apply_symm_apply]
  let vC : ↥(centralizer ({x} : Set G)) := ⟨vElt x a, h.T_le_C (v_mem_T h)⟩
  have hιv : ((c.ι vC : Fgrp n) : Amb n) = ((vHat n c.alpha : ↥(T0 n)) : Amb n) := by
    rw [← tau_vT c]
    exact (c.tau_apply (vT h)).symm
  have hwv : wC * vC = vC * wC := by
    apply c.ι.injective
    apply Subtype.ext
    simp only [map_mul, Subgroup.coe_mul, hιw, hιv]
    exact hw₀E _ hvlift
  have hwvG := congrArg Subtype.val hwv
  have hwCv : (wC : G) ∈ Cv := (hmemCv _).2 hwvG
  let w' : ↥Cv := ⟨(wC : G), hwCv⟩
  have hwo : orderOf wC = 3 := by
    rw [← MulEquiv.orderOf_eq c.ι wC]
    have e1 : c.ι wC = ⟨w₀, hw₀F⟩ := MulEquiv.apply_symm_apply _ _
    rw [e1, ← Subgroup.orderOf_coe]
    exact hw₀o
  have hw3 : w' ^ 3 = 1 := by
    have h1 := pow_orderOf_eq_one wC
    rw [hwo] at h1
    have h1G := congrArg Subtype.val h1
    exact Subtype.ext h1G
  have hw1 : w' ≠ 1 := by
    intro h1
    have h1G := congrArg Subtype.val h1
    have h2 : wC = 1 := Subtype.ext h1G
    rw [h2, orderOf_one] at hwo
    omega
  have hιT : ∀ t : ↥T, ((c.ι ⟨(t : G), h.T_le_C t.2⟩ : Fgrp n) : Amb n) =
      ((c.tau t : ↥(T0 n)) : Amb n) := fun t => (c.tau_apply t).symm
  have hcommι : ∀ g₁ g₂ : ↥(centralizer ({x} : Set G)),
      g₁ * g₂ = g₂ * g₁ ↔ ((c.ι g₁ : Fgrp n) : Amb n) * ((c.ι g₂ : Fgrp n) : Amb n) =
        ((c.ι g₂ : Fgrp n) : Amb n) * ((c.ι g₁ : Fgrp n) : Amb n) := by
    intro g₁ g₂
    constructor
    · intro h1
      have h2 := congrArg (fun z => ((c.ι z : Fgrp n) : Amb n)) h1
      simpa only [map_mul, Subgroup.coe_mul] using h2
    · intro h1
      apply c.ι.injective
      apply Subtype.ext
      simpa only [map_mul, Subgroup.coe_mul] using h1
  have hwE : ∀ e ∈ E', w' * e = e * w' := by
    intro e he
    obtain ⟨ε, hε, hεe⟩ := (mem_Eg c).1 he
    let eT : ↥T := c.tau.symm ε
    have heT : ((eT : ↥T) : G) = (e : G) := hεe
    have h1 : wC * ⟨(eT : G), h.T_le_C eT.2⟩ = ⟨(eT : G), h.T_le_C eT.2⟩ * wC := by
      rw [hcommι, hιw, hιT eT]
      have : c.tau eT = ε := MulEquiv.apply_symm_apply _ _
      rw [this]
      exact hw₀E _ ⟨ε, hε, rfl⟩
    apply Subtype.ext
    have h2 := congrArg Subtype.val h1
    simpa [w', heT] using h2
  have hC0 : ∀ g : ↥Cv, (∀ e ∈ E', g * e = e * g) → ∃ k : ℕ, ∃ t ∈ A', g = w' ^ k * t := by
    intro g hg
    have hgx : (g : G) * x = x * (g : G) := congrArg Subtype.val (hg x' hxE)
    have hgcomm : ∀ e ∈ Eg c E, (g : G) * e = e * (g : G) := fun e he =>
      congrArg Subtype.val (hg ⟨e, hEgCv he⟩ he)
    let gC : ↥(centralizer ({x} : Set G)) := ⟨(g : G), mem_centralizer_singleton_iff.2 hgx⟩
    have hιg : ((c.ι gC : Fgrp n) : Amb n) ∈
        Fgrp n ⊓ Subgroup.centralizer (liftT n E : Set (Amb n)) := by
      refine Subgroup.mem_inf.2 ⟨(c.ι gC).2, Subgroup.mem_centralizer_iff.2 ?_⟩
      rintro _ ⟨ε, hε, rfl⟩
      exact (iota_comm_of_comm c hgx hgcomm ε hε).symm
    obtain ⟨k, t, ht, hkt⟩ := hw₀C0 _ hιg
    obtain ⟨tG, htG⟩ : ∃ tG : ↥T, c.tau tG = t := ⟨c.tau.symm t, MulEquiv.apply_symm_apply _ _⟩
    let tC : ↥(centralizer ({x} : Set G)) := ⟨(tG : G), h.T_le_C tG.2⟩
    have hιtC : ((c.ι tC : Fgrp n) : Amb n) = ((t : ↥(T0 n)) : Amb n) :=
      (hιT tG).trans (congrArg (fun z : ↥(T0 n) => (z : Amb n)) htG)
    have h1 : c.ι gC = c.ι (wC ^ k * tC) := by
      apply Subtype.ext
      simp only [map_mul, map_pow, Subgroup.coe_mul, Subgroup.coe_pow, hιw, hιtC]
      exact hkt
    have h2 : gC = wC ^ k * tC := c.ι.injective h1
    have htA : (tG : G) ∈ Eg c A := (mem_Eg_iff c tG).2 (by rw [htG]; exact ht)
    refine ⟨k, ⟨(tG : G), hTCv tG.2⟩, htA, ?_⟩
    apply Subtype.ext
    have h3 := congrArg Subtype.val h2
    simpa [w', gC, tC] using h3
  have hinv : ∀ t ∈ A', t ∉ E' → t * w' * t⁻¹ = w'⁻¹ := by
    intro t ht htE
    have htA : (t : G) ∈ Eg c A := ht
    have htT : (t : G) ∈ T := Eg_le_T c htA
    let tT : ↥T := ⟨(t : G), htT⟩
    have h1 : c.tau tT ∈ A := (mem_Eg_iff c tT).1 htA
    have h2 : c.tau tT ∉ E := fun hm => htE ((mem_Eg_iff c tT).2 hm)
    have h3 := hw₀inv _ h1 h2
    let tC : ↥(centralizer ({x} : Set G)) := ⟨(t : G), h.T_le_C htT⟩
    have h4 : c.ι (tC * wC * tC⁻¹) = c.ι wC⁻¹ := by
      apply Subtype.ext
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hιw]
      rw [hιT tT]
      exact h3
    have h5 : tC * wC * tC⁻¹ = wC⁻¹ := c.ι.injective h4
    apply Subtype.ext
    have h6 := congrArg Subtype.val h5
    simpa [w', tC] using h6
  have hbE : ∀ i, b' i ∉ E' := by
    intro i hi
    have h1 : ((c.tau.symm (b i) : ↥T) : G) ∈ Eg c E := hi
    have h2 := (mem_Eg_iff c (c.tau.symm (b i))).1 h1
    rw [MulEquiv.apply_symm_apply] at h2
    exact (hb1 i).2.2.2 h2
  have hbA : ∀ i, b' i ∈ A' := fun i =>
    (mem_Eg_iff c (c.tau.symm (b i))).2 (by rw [MulEquiv.apply_symm_apply]; exact (hb1 i).1)
  have hbsq : ∀ i, b' i * b' i = 1 := by
    intro i
    have h2 : b i * b i = 1 := by
      have := pow_orderOf_eq_one (b i)
      rwa [(hb1 i).2.1, sq] at this
    have h3 : c.tau.symm (b i) * c.tau.symm (b i) = 1 := by rw [← map_mul, h2, map_one]
    have h3G := congrArg Subtype.val h3
    exact Subtype.ext h3G
  have hbinj' : Function.Injective b' := by
    intro i j hij
    have h1 := congrArg Subtype.val hij
    exact hbinj (c.tau.symm.injective (Subtype.ext h1))
  have hbgen : ∀ t ∈ A', t ∈ Subgroup.closure (Set.range b') := by
    intro t ht
    obtain ⟨τ₀, hτ₀A, hτ₀⟩ := (mem_Eg c).1 ht
    let φ : ↥(T0 n) →* ↥Cv := (Subgroup.inclusion hTCv).comp c.tau.symm.toMonoidHom
    have h1 : φ τ₀ = t := Subtype.ext hτ₀
    have hmem : φ τ₀ ∈ (Subgroup.closure (Set.range b)).map φ := ⟨τ₀, hb3 τ₀ hτ₀A, rfl⟩
    rw [MonoidHom.map_closure, ← Set.range_comp] at hmem
    have h2 : (φ ∘ b) = b' := funext fun i => Subtype.ext rfl
    rw [h2, h1] at hmem
    exact hmem
  have hbo : ∀ i, orderOf ((b' i : ↥Cv) : G) = 2 := by
    intro i
    show orderOf ((c.tau.symm (b i) : ↥T) : G) = 2
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact (hb1 i).2.1
  have hbX : ∀ i, IsConj ((b' i : ↥Cv) : G) x := by
    intro i
    have := (tau_mem_XSet_iff c (c.tau.symm (b i))).1 (by
      rw [MulEquiv.apply_symm_apply]; exact (hb1 i).2.2.1)
    exact this
  have hbperm : ∀ r ∈ normalizer (A' : Set ↥Cv), ∀ i, ∃ j, r * b' i * r⁻¹ = b' j := by
    intro r hr i
    have hyA' : r * b' i * r⁻¹ ∈ A' := (mem_normalizer_iff.1 hr (b' i)).1 (hbA i)
    set y : G := (r : G) * ((b' i : ↥Cv) : G) * (r : G)⁻¹ with hy
    have hyA : y ∈ Eg c A := hyA'
    have hyT : y ∈ T := hAgT hyA
    let yT : ↥T := ⟨y, hyT⟩
    have hyord : orderOf y = 2 := by
      have := MulEquiv.orderOf_eq (MulAut.conj (r : G)) ((b' i : ↥Cv) : G)
      simpa [MulAut.conj_apply, hbo i] using this
    have hyc : IsConj y x :=
      (isConj_iff.2 ⟨(r : G), rfl⟩ : IsConj ((b' i : ↥Cv) : G) y).symm.trans (hbX i)
    have hτA : c.tau yT ∈ A := (mem_Eg_iff c yT).1 hyA
    have hτord : orderOf (c.tau yT) = 2 := by
      rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
      exact hyord
    have hτX : c.tau yT ∈ c.XSet := (tau_mem_XSet_iff c yT).2 hyc
    have hτE : c.tau yT ∉ E := by
      intro hτE
      have hyE : y ∈ Eg c E := (mem_Eg_iff c yT).2 hτE
      have hbE' : ((b' i : ↥Cv) : G) ∈ Eg c E := by
        have := hnorm ((r⁻¹ : ↥Cv) : G) (mem_centralizer_singleton_iff.1 (r⁻¹).2) y hyE
        have h6 : (r : G)⁻¹ * y * ((r : G)⁻¹)⁻¹ = ((b' i : ↥Cv) : G) := by rw [hy]; group
        rw [← h6]
        simpa using this
      have := (mem_Eg_iff c (c.tau.symm (b i))).1 hbE'
      rw [MulEquiv.apply_symm_apply] at this
      exact (hb1 i).2.2.2 this
    obtain ⟨j, hj⟩ := hb2 _ hτA hτord hτX hτE
    refine ⟨j, Subtype.ext ?_⟩
    have h7 : yT = c.tau.symm (b j) := by rw [← hj, MulEquiv.symm_apply_apply]
    have h7G : ((yT : ↥T) : G) = ((c.tau.symm (b j) : ↥T) : G) := by rw [h7]
    exact h7G
  have hSN : S' ≤ normalizer (A' : Set ↥Cv) := by
    intro s hs
    rw [mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      exact S_norm_Ag c hE hE2 hSeq (s : G) hs (z : G) hz
    · intro hz
      have h1 : ((s⁻¹ : ↥Cv) : G) * ((s * z * s⁻¹ : ↥Cv) : G) * ((s⁻¹ : ↥Cv) : G)⁻¹ ∈ Eg c A :=
        S_norm_Ag c hE hE2 hSeq ((s⁻¹ : ↥Cv) : G) (inv_mem hs) _ hz
      have h2 : ((s⁻¹ : ↥Cv) : G) * ((s * z * s⁻¹ : ↥Cv) : G) * ((s⁻¹ : ↥Cv) : G)⁻¹ = (z : G) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [h2] at h1
      exact h1
  have hAS : A' ≤ S' := fun e he => hTS (hAgT he)
  have hAR : A' ⊓ R' = ⊥ := by
    rw [eq_bot_iff]
    rintro e ⟨he1, he2⟩
    have h1 : (e : G) ∈ Eg c A ⊓ RS := ⟨he1, he2⟩
    rw [hARS_bot, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.2 (Subtype.ext h1)
  have hARS : A' ⊔ R' = S' := by
    show A' ⊔ R' = S.subgroupOf Cv
    rw [← hARS_top]
    exact (Subgroup.subgroupOf_sup hAgCv hRSCv).symm
  have hATm : A' ≤ Tm := fun e he => hAgT he
  have hTmS : Tm ≤ S' := fun e he => hTS he
  have hsq2 : ∀ z : ↥(T0 n), orderOf z = 2 → z * z = 1 := fun z hz => by
    have := pow_orderOf_eq_one z
    rwa [hz, sq] at this
  have hM9all : ∀ (t y : ↥Cv) (π₁ π₂ : Equiv.Perm (Fin 4)), t ∈ Tm → y ∈ Tm → t ∉ A' → y ∉ A' →
      t * t = 1 → y * y = 1 → t * y = y * t → π₁.IsSwap → π₂.IsSwap → Equiv.Perm.Disjoint π₁ π₂ →
      (∀ i, t * b' i * t⁻¹ = b' (π₁ i)) → (∀ i, y * b' i * y⁻¹ = b' (π₂ i)) →
      t * w' = w' * t := by
    intro t y π₁ π₂ htTm hyTm htA hyA ht2 hy2 hty hπ₁ hπ₂ hdis htb hyb
    have htT : (t : G) ∈ T := htTm
    have hyT : (y : G) ∈ T := hyTm
    let tT : ↥T := ⟨(t : G), htT⟩
    let yT : ↥T := ⟨(y : G), hyT⟩
    have htnA : c.tau tT ∉ A := fun hm => htA ((mem_Eg_iff c tT).2 hm)
    have hynA : c.tau yT ∉ A := fun hm => hyA ((mem_Eg_iff c yT).2 hm)
    have ht2G := congrArg Subtype.val ht2
    have hy2G := congrArg Subtype.val hy2
    have htt : tT * tT = 1 := Subtype.ext ht2G
    have hyy : yT * yT = 1 := Subtype.ext hy2G
    have hto : orderOf (c.tau tT) = 2 := by
      refine orderOf_eq_prime (by rw [sq, ← map_mul, htt, map_one]) ?_
      intro h1
      exact htnA (by rw [h1]; exact one_mem A)
    have hyo : orderOf (c.tau yT) = 2 := by
      refine orderOf_eq_prime (by rw [sq, ← map_mul, hyy, map_one]) ?_
      intro h1
      exact hynA (by rw [h1]; exact one_mem A)
    have hcomm_tt : c.tau tT * c.tau yT = c.tau yT * c.tau tT := by
      rw [← map_mul, ← map_mul]
      congr 1
      have htyG := congrArg Subtype.val hty
      exact Subtype.ext htyG
    have hconj : ∀ (u : ↥Cv) (uT : ↥T) (π : Equiv.Perm (Fin 4)), (uT : G) = (u : G) →
        (∀ i, u * b' i * u⁻¹ = b' (π i)) →
        ∀ i, c.tau uT * b i * (c.tau uT)⁻¹ = b (π i) := by
      intro u uT π huT hu i
      have h1 := congrArg Subtype.val (hu i)
      have h2 : uT * c.tau.symm (b i) * uT⁻¹ = c.tau.symm (b (π i)) := by
        apply Subtype.ext
        show (uT : G) * ((c.tau.symm (b i) : ↥T) : G) * (uT : G)⁻¹ =
          ((c.tau.symm (b (π i)) : ↥T) : G)
        rw [huT]
        exact h1
      have h3 := congrArg c.tau h2
      rwa [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply,
        MulEquiv.apply_symm_apply] at h3
    have hmain := hM9all₀ (c.tau tT) (c.tau yT) π₁ π₂ htnA hynA hto hyo hcomm_tt hπ₁ hπ₂ hdis
      (hconj t tT π₁ rfl htb) (hconj y yT π₂ rfl hyb)
    let tC : ↥(centralizer ({x} : Set G)) := ⟨(t : G), h.T_le_C htT⟩
    have hιt : ((c.ι tC : Fgrp n) : Amb n) = ((c.tau tT : ↥(T0 n)) : Amb n) :=
      (c.tau_apply tT).symm
    have h5 : tC * wC = wC * tC := (hcommι tC wC).2 (by rw [hιt, hιw]; exact hmain)
    apply Subtype.ext
    have h5G := congrArg Subtype.val h5
    exact h5G
  have hM9ex : ∃ (t y : ↥Cv) (π₁ π₂ : Equiv.Perm (Fin 4)), t ∈ Tm ∧ y ∈ Tm ∧ t ∉ A' ∧ y ∉ A' ∧
      t * t = 1 ∧ y * y = 1 ∧ t * y = y * t ∧ π₁.IsSwap ∧ π₂.IsSwap ∧ Equiv.Perm.Disjoint π₁ π₂ ∧
      (∀ i, t * b' i * t⁻¹ = b' (π₁ i)) ∧ (∀ i, y * b' i * y⁻¹ = b' (π₂ i)) := by
    obtain ⟨t₀, y₀', ht₀A, hy₀A, ht₀o, hy₀o, ht₀y₀, π₁, π₂, hπ₁, hπ₂, hdis, ht₀b, hy₀b⟩ :=
      hM9ex₀
    obtain ⟨tT, rfl⟩ := c.tau.surjective t₀
    obtain ⟨yT, rfl⟩ := c.tau.surjective y₀'
    have hTT : tT * tT = 1 := c.tau.injective (by rw [map_mul, map_one]; exact hsq2 _ ht₀o)
    have hYY : yT * yT = 1 := c.tau.injective (by rw [map_mul, map_one]; exact hsq2 _ hy₀o)
    have hTY : tT * yT = yT * tT := c.tau.injective (by rw [map_mul, map_mul]; exact ht₀y₀)
    have hconj : ∀ (uT : ↥T) (π : Equiv.Perm (Fin 4)),
        (∀ i, c.tau uT * b i * (c.tau uT)⁻¹ = b (π i)) →
        ∀ i, (⟨(uT : G), hTCv uT.2⟩ : ↥Cv) * b' i * (⟨(uT : G), hTCv uT.2⟩ : ↥Cv)⁻¹ =
          b' (π i) := by
      intro uT π hu i
      apply Subtype.ext
      have h1 : uT * c.tau.symm (b i) * uT⁻¹ = c.tau.symm (b (π i)) := by
        apply c.tau.injective
        rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
        exact hu i
      have h1G := congrArg Subtype.val h1
      exact h1G
    have hTTG := congrArg Subtype.val hTT
    have hYYG := congrArg Subtype.val hYY
    have hTYG := congrArg Subtype.val hTY
    refine ⟨⟨(tT : G), hTCv tT.2⟩, ⟨(yT : G), hTCv yT.2⟩, π₁, π₂, tT.2, yT.2, ?_, ?_,
      Subtype.ext hTTG, Subtype.ext hYYG, Subtype.ext hTYG, hπ₁, hπ₂, hdis, hconj tT π₁ ht₀b,
      hconj yT π₂ hy₀b⟩
    · exact fun hm => ht₀A ((mem_Eg_iff c tT).1 hm)
    · exact fun hm => hy₀A ((mem_Eg_iff c yT).1 hm)
  exact PartB7.exists_mulEquiv_W7_of_data hCcard E' A' hEn hEcard hEcomm hAcard hAcomm hAsq hEA
    hAE w' hw3 hw1 hwE hC0 hinv b' hbA hbE hbsq hbinj' hbgen hbperm S' R' hSyl hSN hAS hAR hARS
    Tm hATm hTmS hM9all hM9ex

theorem exists_equiv_centralizer_v7
    (hZD : CFSG.GH74.Uniqueness.S_ZD) (hn : n = 7)
    (hG : IsSimpleGroup G)
    (hnab : ∃ u w : G, u * w ≠ w * u) (hM : ModelIso n c.alpha c.uElt c.XSet c.VSet) :
    ∃ v' : alternatingGroup (Fin (n + 4)), orderOf v' = 2 ∧
      numMoved (v' : Equiv.Perm (Fin (n + 4))) = 8 ∧
      Nonempty (↥(centralizer ({x * (a * x * a⁻¹)} : Set G)) ≃*
        ↥(centralizer ({v'} : Set (alternatingGroup (Fin (n + 4)))))) := by
  obtain ⟨e₁⟩ := exists_mulEquiv_W7_Cv c hE hE2 hE3 hZD hn hG hnab hM
  subst hn
  obtain ⟨v', hv'o, hv'n, ⟨e₂⟩⟩ := Star.exists_mulEquiv_seven
  exact ⟨v', hv'o, hv'n, ⟨e₁.symm.trans e₂⟩⟩

end Main7

end CFSG.GH74.GLS.C3.Layer2.L4
