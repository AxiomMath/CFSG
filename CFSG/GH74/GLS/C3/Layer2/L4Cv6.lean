module

public import CFSG.GH74.GLS.C3.Layer2.L4Setup
public import CFSG.GH74.GLS.C3.Layer2.L4PartB6
public import CFSG.GH74.GLS.C3.Layer2.L4Star

public section

namespace CFSG.GH74.GLS.C3.Layer2.L4

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer2
open CFSG.GH74.GLS.C3.Layer2.Model

structure E2Pkg (n : ℕ) [NeZero n] (α : ↥(T0 n) ≃* ↥(T0 n)) (u : ↥(T0 n)) (X : Set ↥(T0 n))
    (E A : Subgroup ↥(T0 n)) : Prop where
  memA : ∀ t : ↥(T0 n), t ∈ A ↔ ∀ e ∈ E, t * e = e * t
  cardA : Nat.card A = 16
  commA : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a
  sqA : ∀ a ∈ A, a * a = 1
  cent6 : n = 6 → ∀ g ∈ Fgrp n, (∀ e ∈ liftT n E, g * e = e * g) → g ∈ T0 n
  b : ∃ b : Fin 4 → ↥(T0 n), Function.Injective b ∧
    (∀ i, b i ∈ A ∧ orderOf (b i) = 2 ∧ b i ∈ X ∧ b i ∉ E) ∧
    (∀ t ∈ A, orderOf t = 2 → t ∈ X → t ∉ E → ∃ i, t = b i) ∧
    (∀ t ∈ A, t ∈ Subgroup.closure (Set.range b))
  split : ∀ t₀ : ↥(T0 n), t₀ * α t₀ * u = 1 → ∃ R : Subgroup ↥(T0 n),
    R ⊓ A = ⊥ ∧ (∀ r ∈ R, t₀ * α r * t₀⁻¹ ∈ R) ∧ A ⊔ R = ⊤
  zcenter : ∀ s : ↥(T0 n), (∀ t : ↥(T0 n), s * t = t * s) → α s = s → s * s = 1 → s ≠ 1 →
    s = vHat n α

section Transport

variable {G : Type} [Group G] [Finite G] {n : ℕ} [NeZero n] {x : G} {K T Q S : Subgroup G} {a : G}
  {h : IsAConfig n x K T Q S a} (c : Coord h)

theorem Eg_card_of (E : Subgroup ↥(T0 n)) : Nat.card (Eg c E) = Nat.card E := by
  unfold Eg
  rw [Subgroup.card_map_of_injective T.subtype_injective,
    Subgroup.card_map_of_injective (f := c.tau.symm.toMonoidHom)
      (fun a b hab => c.tau.symm.injective hab)]

theorem Eg_comm_of {E : Subgroup ↥(T0 n)} (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) :
    ∀ y₁ ∈ Eg c E, ∀ y₂ ∈ Eg c E, y₁ * y₂ = y₂ * y₁ := by
  intro y₁ h₁ y₂ h₂
  obtain ⟨t₁, ht₁, rfl⟩ := (mem_Eg c).1 h₁
  obtain ⟨t₂, ht₂, rfl⟩ := (mem_Eg c).1 h₂
  have h3 : c.tau.symm t₁ * c.tau.symm t₂ = c.tau.symm t₂ * c.tau.symm t₁ := by
    rw [← map_mul, ← map_mul, hcomm t₁ ht₁ t₂ ht₂]
  exact congrArg Subtype.val h3

theorem Eg_top : Eg c (⊤ : Subgroup ↥(T0 n)) = T := by
  apply le_antisymm (Eg_le_T c)
  intro y hy
  rw [mem_Eg]
  exact ⟨c.tau ⟨y, hy⟩, mem_top _, by simp⟩

theorem Eg_sup (A R : Subgroup ↥(T0 n)) : Eg c (A ⊔ R) = Eg c A ⊔ Eg c R := by
  unfold Eg
  rw [Subgroup.map_sup, Subgroup.map_sup]

theorem Eg_inf_bot {A R : Subgroup ↥(T0 n)} (h : R ⊓ A = ⊥) : Eg c R ⊓ Eg c A = ⊥ := by
  rw [eq_bot_iff]
  rintro y ⟨hyR, hyA⟩
  obtain ⟨r, hr, rfl⟩ := (mem_Eg c).1 hyR
  obtain ⟨t, ht, hrt⟩ := (mem_Eg c).1 hyA
  have h1 : t = r := c.tau.symm.injective (Subtype.ext hrt)
  rw [h1] at ht
  have h2 : r ∈ R ⊓ A := ⟨hr, ht⟩
  rw [h, Subgroup.mem_bot] at h2
  rw [h2, map_one]
  exact Subgroup.one_mem _

end Transport

section Split

variable {G : Type} [Group G] [Finite G] {n : ℕ} [NeZero n] {x : G} {K T Q S : Subgroup G} {a : G}
  {h : IsAConfig n x K T Q S a} (c : Coord h) {E A : Subgroup ↥(T0 n)}
  (hE2 : E2Pkg n c.alpha c.uElt c.XSet E A)
include hE2

theorem exists_split_G (hn : n = 6 ∨ n = 7) (hG : IsSimpleGroup G)
    (hnab : ∃ u w : G, u * w ≠ w * u) (hM : ModelIso n c.alpha c.uElt c.XSet c.VSet) :
    ∃ R : Subgroup G, R ≤ S ∧ Eg c A ⊓ R = ⊥ ∧ Eg c A ⊔ R = S := by
  obtain ⟨hS128, hSeq, ⟨y₀, hy₀S, hy₀sq, hy₀T⟩, hfus⟩ := fusion_facts h c hn hG hnab hM
  have hT64 : Nat.card T = 64 := c.card_T hn
  have hTS : T ≤ S := h.T_lt_S.le
  have hSN : S ≤ normalizer (T : Set G) := by
    rw [hSeq]
    exact sup_le Subgroup.le_normalizer (zpowers_le.2 h.a_mem.2.1)
  have hy₀N : ∀ t ∈ T, y₀ * t * y₀⁻¹ ∈ T := fun t ht => ((mem_normalizer_iff.1 (hSN hy₀S)) t).1 ht
  have hy₀sq' : y₀ ^ 2 = 1 := by rw [sq]; exact hy₀sq
  have hS₁ : T ⊔ zpowers y₀ = S := by
    apply Subgroup.eq_of_le_of_card_ge (sup_le hTS (zpowers_le.2 hy₀S))
    rw [card_sup_zpowers hy₀N hy₀sq' hy₀T, hT64, hS128]
  have hat : y₀ * a⁻¹ ∈ T := by
    have haS : a ∈ T ⊔ zpowers y₀ := by rw [hS₁]; exact h.a_mem.1
    rcases (mem_sup_zpowers_iff hy₀N hy₀sq').1 haS with h1 | h1
    · exact absurd h1 h.a_mem.2.2.1
    · have := T.inv_mem h1
      rwa [mul_inv_rev, inv_inv] at this
  let t₀ : ↥(T0 n) := c.tau ⟨y₀ * a⁻¹, hat⟩
  have ht₀ : t₀ * c.alpha t₀ * c.uElt = 1 := by
    have h1 : (⟨y₀ * a⁻¹, hat⟩ : ↥T) * conjAutT h.a_mem.2.1 ⟨y₀ * a⁻¹, hat⟩ *
        ⟨a ^ 2, h.a_mem.2.2.2⟩ = 1 := by
      apply Subtype.ext
      show y₀ * a⁻¹ * (a * (y₀ * a⁻¹) * a⁻¹) * a ^ 2 = 1
      calc y₀ * a⁻¹ * (a * (y₀ * a⁻¹) * a⁻¹) * a ^ 2 = y₀ * y₀ := by group
        _ = 1 := hy₀sq
    show c.tau _ * c.alpha (c.tau _) * c.tau _ = 1
    rw [Coord.alpha_tau, ← map_mul, ← map_mul, h1, map_one]
  obtain ⟨R, hRA, hRnorm, hRAt⟩ := hE2.split t₀ ht₀
  have hR_T : Eg c R ≤ T := Eg_le_T c
  have hy₀R : ∀ r ∈ Eg c R, y₀ * r * y₀⁻¹ ∈ Eg c R := by
    intro r hr
    obtain ⟨ρ, hρ, rfl⟩ := (mem_Eg c).1 hr
    have hτ : ((c.tau.symm t₀ : ↥T) : G) = y₀ * a⁻¹ := by
      show ((c.tau.symm (c.tau ⟨y₀ * a⁻¹, hat⟩) : ↥T) : G) = _
      rw [MulEquiv.symm_apply_apply]
    have h1 : c.tau.symm (t₀ * c.alpha ρ * t₀⁻¹) =
        c.tau.symm t₀ * conjAutT h.a_mem.2.1 (c.tau.symm ρ) * (c.tau.symm t₀)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
      have : c.tau.symm (c.alpha ρ) = conjAutT h.a_mem.2.1 (c.tau.symm ρ) := by
        simp [Coord.alpha]
      rw [this]
    rw [mem_Eg]
    refine ⟨t₀ * c.alpha ρ * t₀⁻¹, hRnorm ρ hρ, ?_⟩
    rw [h1]
    show ((c.tau.symm t₀ : ↥T) : G) * (a * ((c.tau.symm ρ : ↥T) : G) * a⁻¹) *
      ((c.tau.symm t₀ : ↥T) : G)⁻¹ = _
    rw [hτ]
    group
  have hy₀nR : y₀ ∉ Eg c R := fun hmem => hy₀T (hR_T hmem)
  have hAG_T : Eg c A ≤ T := Eg_le_T c
  have hRS_S : Eg c R ⊔ zpowers y₀ ≤ S := sup_le (hR_T.trans hTS) (zpowers_le.2 hy₀S)
  have hAR_bot : Eg c A ⊓ (Eg c R ⊔ zpowers y₀) = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyA, hyRS⟩
    have hyT : y ∈ T := hAG_T hyA
    rcases (mem_sup_zpowers_iff hy₀R hy₀sq').1 hyRS with h1 | h1
    · have h2 : y ∈ Eg c R ⊓ Eg c A := ⟨h1, hyA⟩
      rw [Eg_inf_bot c hRA, Subgroup.mem_bot] at h2
      rw [h2]
      exact one_mem _
    · exfalso
      apply hy₀T
      have h3 : y * y₀⁻¹ ∈ T := hR_T h1
      have h4 : y₀⁻¹ ∈ T := by
        have := T.mul_mem (T.inv_mem hyT) h3
        simpa using this
      simpa using T.inv_mem h4
  have hT_eq : Eg c A ⊔ Eg c R = T := by
    rw [← Eg_sup c A R, hRAt, Eg_top]
  have hle1 : T ≤ Eg c A ⊔ (Eg c R ⊔ zpowers y₀) :=
    hT_eq.symm.le.trans (sup_le_sup_left le_sup_left _)
  have hle2 : y₀ ∈ Eg c A ⊔ (Eg c R ⊔ zpowers y₀) :=
    le_sup_right (a := Eg c A) (le_sup_right (a := Eg c R) (mem_zpowers y₀))
  have hle3 : S ≤ Eg c A ⊔ (Eg c R ⊔ zpowers y₀) :=
    hS₁.symm.le.trans (sup_le hle1 (zpowers_le.2 hle2))
  exact ⟨Eg c R ⊔ zpowers y₀, hRS_S, hAR_bot,
    le_antisymm (sup_le (hAG_T.trans hTS) hRS_S) hle3⟩

end Split

section Char

variable {G : Type} [Group G] [Finite G] {n : ℕ} [NeZero n] {x : G} {K T Q S : Subgroup G} {a : G}
  {h : IsAConfig n x K T Q S a} (c : Coord h) {E A : Subgroup ↥(T0 n)}
  (hE : E1Pkg n c.alpha c.XSet c.VSet E) (hE2 : E2Pkg n c.alpha c.uElt c.XSet E A)
include hE hE2

theorem mem_Ag_char (hn6 : n = 6) {g : G} :
    g ∈ Eg c A ↔ ∀ e ∈ Eg c E, g * e = e * g := by
  constructor
  · intro hg e he
    obtain ⟨t, ht, rfl⟩ := (mem_Eg c).1 hg
    obtain ⟨ε, hε, rfl⟩ := (mem_Eg c).1 he
    have h4 := (hE2.memA t).1 ht ε hε
    have h3 : c.tau.symm t * c.tau.symm ε = c.tau.symm ε * c.tau.symm t := by
      rw [← map_mul, ← map_mul, h4]
    exact congrArg Subtype.val h3
  · intro hcomm
    have hgx : g * x = x * g := hcomm x (x_mem_Eg c hE)
    let gC : ↥(centralizer ({x} : Set G)) := ⟨g, mem_centralizer_singleton_iff.2 hgx⟩
    have hι : ∀ ε ∈ E, ((c.ι gC : Fgrp n) : Amb n) * (ε : Amb n) =
        (ε : Amb n) * ((c.ι gC : Fgrp n) : Amb n) := by
      intro ε hε
      set eT : ↥T := c.tau.symm ε with heT
      let eC : ↥(centralizer ({x} : Set G)) := ⟨(eT : G), h.T_le_C eT.2⟩
      have hιe : ((c.ι eC : Fgrp n) : Amb n) = (ε : Amb n) := by
        have := c.tau_apply eT
        rw [heT, MulEquiv.apply_symm_apply] at this
        exact this.symm
      have heE : (eT : G) ∈ Eg c E := (mem_Eg c).2 ⟨ε, hε, rfl⟩
      have h1 : gC * eC = eC * gC := Subtype.ext (hcomm _ heE)
      have h2 := congrArg (fun z => ((c.ι z : Fgrp n) : Amb n)) h1
      simp only [map_mul, Subgroup.coe_mul, hιe] at h2
      exact h2
    have hmemT0 : ((c.ι gC : Fgrp n) : Amb n) ∈ T0 n := by
      refine hE2.cent6 hn6 _ (c.ι gC).2 ?_
      rintro _ ⟨ε, hε, rfl⟩
      exact hι ε hε
    have hgT : g ∈ T := (c.ι_T gC).2 hmemT0
    let gT : ↥T := ⟨g, hgT⟩
    refine (mem_Eg_iff c gT).2 ((hE2.memA _).2 ?_)
    intro ε hε
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, c.tau_apply gT]
    exact hι ε hε

end Char

section Card

variable {G : Type} [Group G] [Finite G] {n : ℕ} [NeZero n] {x : G} {K T Q S : Subgroup G} {a : G}
  {h : IsAConfig n x K T Q S a} (c : Coord h)

omit [NeZero n] in
theorem Hgrp_x0_mul (z : Amb n) : Hgrp n (x0 n * z) = Hgrp n z := by
  ext g
  simp only [Hgrp, Subgroup.mem_inf, mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hgF, hg⟩
    refine ⟨hgF, ?_⟩
    have hc : g * x0 n = x0 n * g := x0_central n hgF
    have h1 : x0 n * (g * z) = x0 n * (z * g) := by
      calc x0 n * (g * z) = g * (x0 n * z) := by rw [← mul_assoc, ← hc, mul_assoc]
        _ = (x0 n * z) * g := hg
        _ = x0 n * (z * g) := by rw [mul_assoc]
    exact mul_left_cancel h1
  · rintro ⟨hgF, hg⟩
    refine ⟨hgF, ?_⟩
    have hc : g * x0 n = x0 n * g := x0_central n hgF
    calc g * (x0 n * z) = (g * x0 n) * z := by rw [mul_assoc]
      _ = x0 n * (g * z) := by rw [hc, mul_assoc]
      _ = x0 n * (z * g) := by rw [hg]
      _ = (x0 n * z) * g := by rw [mul_assoc]

theorem card_centralizer_x' :
    Nat.card ↥(centralizer ({(⟨x, x_mem_centralizer_v h⟩ :
        ↥(centralizer ({vElt x a} : Set G)))} : Set ↥(centralizer ({vElt x a} : Set G)))) =
      Nat.card ↥(Hgrp n ((vHat n c.alpha : ↥(T0 n)) : Amb n)) := by
  set Cv := centralizer ({vElt x a} : Set G) with hCv
  let x' : ↥Cv := ⟨x, x_mem_centralizer_v h⟩
  have hxv := x_mul_v h
  let e : ↥(centralizer ({x'} : Set ↥Cv)) ≃
      ↥(centralizer ({x} : Set G) ⊓ centralizer ({a * x * a⁻¹} : Set G)) :=
    { toFun := fun g => ⟨((g : ↥Cv) : G), by
        have h1 : ((g : ↥Cv) : G) * x = x * ((g : ↥Cv) : G) :=
          congrArg Subtype.val (mem_centralizer_singleton_iff.1 g.2)
        have h2 : ((g : ↥Cv) : G) * vElt x a = vElt x a * ((g : ↥Cv) : G) :=
          mem_centralizer_singleton_iff.1 (g : ↥Cv).2
        refine ⟨mem_centralizer_singleton_iff.2 h1, mem_centralizer_singleton_iff.2 ?_⟩
        rw [← hxv]
        calc ((g : ↥Cv) : G) * (x * vElt x a) = (((g : ↥Cv) : G) * x) * vElt x a := by group
          _ = (x * ((g : ↥Cv) : G)) * vElt x a := by rw [h1]
          _ = x * (((g : ↥Cv) : G) * vElt x a) := by group
          _ = x * (vElt x a * ((g : ↥Cv) : G)) := by rw [h2]
          _ = (x * vElt x a) * ((g : ↥Cv) : G) := by group⟩
      invFun := fun d => ⟨⟨(d : G), by
        have h1 : (d : G) * x = x * (d : G) := mem_centralizer_singleton_iff.1 (mem_inf.1 d.2).1
        have h2 : (d : G) * (a * x * a⁻¹) = (a * x * a⁻¹) * (d : G) :=
          mem_centralizer_singleton_iff.1 (mem_inf.1 d.2).2
        refine mem_centralizer_singleton_iff.2 ?_
        show (d : G) * (x * (a * x * a⁻¹)) = (x * (a * x * a⁻¹)) * (d : G)
        calc (d : G) * (x * (a * x * a⁻¹)) = ((d : G) * x) * (a * x * a⁻¹) := by group
          _ = (x * (d : G)) * (a * x * a⁻¹) := by rw [h1]
          _ = x * ((d : G) * (a * x * a⁻¹)) := by group
          _ = x * ((a * x * a⁻¹) * (d : G)) := by rw [h2]
          _ = (x * (a * x * a⁻¹)) * (d : G) := by group⟩, by
        refine mem_centralizer_singleton_iff.2 (Subtype.ext ?_)
        exact mem_centralizer_singleton_iff.1 (mem_inf.1 d.2).1⟩
      left_inv := fun g => Subtype.ext (Subtype.ext rfl)
      right_inv := fun d => Subtype.ext rfl }
  rw [Nat.card_congr e, Nat.card_congr c.iotaHEquiv.toEquiv]
  have : Hgrp n ((vHat n c.alpha : ↥(T0 n)) : Amb n) =
      Hgrp n ((c.alpha (x0T n) : ↥(T0 n)) : Amb n) := by
    have h1 : ((vHat n c.alpha : ↥(T0 n)) : Amb n) = x0 n * ((c.alpha (x0T n) : ↥(T0 n)) : Amb n) :=
      rfl
    rw [h1, Hgrp_x0_mul]
  rw [this]

end Card

section Main6

variable {G : Type} [Group G] [Finite G] {n : ℕ} [NeZero n] {x : G} {K T Q S : Subgroup G} {a : G}
  {h : IsAConfig n x K T Q S a} (c : Coord h) {E A : Subgroup ↥(T0 n)}
  (hE : E1Pkg n c.alpha c.XSet c.VSet E) (hE2 : E2Pkg n c.alpha c.uElt c.XSet E A)
include hE hE2

theorem exists_mulEquiv_W_Cv
    (hZD : CFSG.GH74.Uniqueness.S_ZD) (hn : n = 6) (hG : IsSimpleGroup G)
    (hnab : ∃ u w : G, u * w ≠ w * u) (hM : ModelIso n c.alpha c.uElt c.XSet c.VSet) :
    Nonempty (Wreath.W ≃* ↥(centralizer ({vElt x a} : Set G))) := by
  have hn' : n = 6 ∨ n = 7 := Or.inl hn
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
  have hv'c : ∀ g : ↥Cv, g * v' = v' * g := fun g =>
    Subtype.ext (mem_centralizer_singleton_iff.1 g.2)
  have hSyl : IsSylowOf 2 S' ⊤ := by
    show IsSylowOf 2 (S.subgroupOf Cv) ⊤
    rw [← isSylowOf_map_subtype_iff Cv, Subgroup.subgroupOf_map_subtype, Subgroup.map_top,
      Subgroup.range_subtype, inf_eq_left.2 hSCv]
    exact h.sylowS.of_le hSCv le_top
  obtain ⟨P, hP⟩ := PartB6.exists_sylow_eq_of_isSylowOf_top hSyl
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
  have hD : Nat.card ↥(centralizer ({x'} : Set ↥Cv)) = 64 := by
    rw [card_centralizer_x' c, hE.hcard]
    simp [hn]
  have hA : ∀ g : ↥Cv, g ∈ A' ↔ ∀ e ∈ E', g * e = e * g := by
    intro g
    show (g : G) ∈ Eg c A ↔ _
    rw [mem_Ag_char c hE hE2 hn]
    constructor
    · intro hg e he
      exact Subtype.ext (hg e he)
    · intro hg e he
      exact congrArg Subtype.val (hg ⟨e, hEgCv he⟩ he)
  have hAcard : Nat.card A' = 16 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAgCv).toEquiv).trans
      ((Eg_card_of c A).trans hE2.cardA)
  have hAcomm : ∀ a ∈ A', ∀ a' ∈ A', a * a' = a' * a := fun a ha b hb =>
    Subtype.ext (Eg_comm_of c hE2.commA a ha b hb)
  obtain ⟨b, hbinj, hb1, hb2, hb3⟩ := hE2.b
  let b' : Fin 4 → ↥Cv := fun i => ⟨((c.tau.symm (b i) : ↥T) : G), hTCv (c.tau.symm (b i)).2⟩
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
  have hbperm : ∀ g : ↥Cv, ∀ i, ∃ j, g * b' i * g⁻¹ = b' j := by
    intro g i
    set y : G := (g : G) * ((b' i : ↥Cv) : G) * (g : G)⁻¹ with hy
    have hyA : y ∈ Eg c A := by
      rw [mem_Ag_char c hE hE2 hn]
      intro e he
      have he' : (g : G)⁻¹ * e * (g : G) ∈ Eg c E := by
        have := hnorm ((g⁻¹ : ↥Cv) : G) (mem_centralizer_singleton_iff.1 (g⁻¹).2) e he
        simpa using this
      have hbAG : ((b' i : ↥Cv) : G) ∈ Eg c A := hbA i
      have hb := (mem_Ag_char c hE hE2 hn).1 hbAG _ he'
      calc y * e = (g : G) * (((b' i : ↥Cv) : G) * ((g : G)⁻¹ * e * (g : G))) * (g : G)⁻¹ := by
            rw [hy]; group
        _ = (g : G) * (((g : G)⁻¹ * e * (g : G)) * ((b' i : ↥Cv) : G)) * (g : G)⁻¹ := by rw [hb]
        _ = e * y := by rw [hy]; group
    have hyT : y ∈ T := hAgT hyA
    let yT : ↥T := ⟨y, hyT⟩
    have hyord : orderOf y = 2 := by
      have := MulEquiv.orderOf_eq (MulAut.conj (g : G)) ((b' i : ↥Cv) : G)
      simpa [MulAut.conj_apply, hbo i] using this
    have hyc : IsConj y x :=
      (isConj_iff.2 ⟨(g : G), rfl⟩ : IsConj ((b' i : ↥Cv) : G) y).symm.trans (hbX i)
    have hτA : c.tau yT ∈ A := (mem_Eg_iff c yT).1 hyA
    have hτord : orderOf (c.tau yT) = 2 := by
      rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
      exact hyord
    have hτX : c.tau yT ∈ c.XSet := (tau_mem_XSet_iff c yT).2 hyc
    have hτE : c.tau yT ∉ E := by
      intro hτE
      have hyE : y ∈ Eg c E := (mem_Eg_iff c yT).2 hτE
      have hbE : ((b' i : ↥Cv) : G) ∈ Eg c E := by
        have := hnorm ((g⁻¹ : ↥Cv) : G) (mem_centralizer_singleton_iff.1 (g⁻¹).2) y hyE
        have h6 : (g : G)⁻¹ * y * ((g : G)⁻¹)⁻¹ = ((b' i : ↥Cv) : G) := by rw [hy]; group
        rw [← h6]
        simpa using this
      have := (mem_Eg_iff c (c.tau.symm (b i))).1 hbE
      rw [MulEquiv.apply_symm_apply] at this
      exact (hb1 i).2.2.2 this
    obtain ⟨j, hj⟩ := hb2 _ hτA hτord hτX hτE
    refine ⟨j, Subtype.ext ?_⟩
    have h7 : yT = c.tau.symm (b j) := by rw [← hj, MulEquiv.symm_apply_apply]
    have h7G : ((yT : ↥T) : G) = ((c.tau.symm (b j) : ↥T) : G) := by rw [h7]
    exact h7G
  have hAP : A' ≤ P := by
    rw [hP]
    exact fun e he => hTS (hAgT he)
  have hAR : A' ⊓ R' = ⊥ := by
    rw [eq_bot_iff]
    rintro e ⟨he1, he2⟩
    have h1 : (e : G) ∈ Eg c A ⊓ RS := ⟨he1, he2⟩
    rw [hARS_bot, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.2 (Subtype.ext h1)
  have hARP : A' ⊔ R' = P := by
    rw [hP]
    show A' ⊔ R' = S.subgroupOf Cv
    rw [← hARS_top]
    exact (Subgroup.subgroupOf_sup hAgCv hRSCv).symm
  exact PartB6.exists_mulEquiv_W_of_data v' x' E' A' b' P R' hv1 hv'c hEn hEcard hEcomm hvE hxE
    hx1 hxv hcls hD hA hAcard hAcomm hbA hbsq hbinj' hbgen hbperm hAP hAR hARP

theorem exists_equiv_centralizer_v6
    (hZD : CFSG.GH74.Uniqueness.S_ZD) (hn : n = 6)
    (hG : IsSimpleGroup G)
    (hnab : ∃ u w : G, u * w ≠ w * u) (hM : ModelIso n c.alpha c.uElt c.XSet c.VSet) :
    ∃ v' : alternatingGroup (Fin (n + 4)), orderOf v' = 2 ∧
      numMoved (v' : Equiv.Perm (Fin (n + 4))) = 8 ∧
      Nonempty (↥(centralizer ({x * (a * x * a⁻¹)} : Set G)) ≃*
        ↥(centralizer ({v'} : Set (alternatingGroup (Fin (n + 4)))))) := by
  obtain ⟨e₁⟩ := exists_mulEquiv_W_Cv c hE hE2 hZD hn hG hnab hM
  subst hn
  obtain ⟨v', hv'o, hv'n, ⟨e₂⟩⟩ := Star.exists_mulEquiv_six
  exact ⟨v', hv'o, hv'n, ⟨e₁.symm.trans e₂⟩⟩

end Main6

end CFSG.GH74.GLS.C3.Layer2.L4
