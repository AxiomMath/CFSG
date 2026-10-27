module

public import CFSG.GH74.GLS.C3.Layer2.L5B7
public import CFSG.GH74.GLS.C3.Layer2.L5B3
public import CFSG.GH74.GLS.C3.Layer2.L5B4
public import CFSG.GH74.GLS.C3.Layer2.L5B5
public import CFSG.GH74.GLS.C3.Layer2.L5Pat

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Prop121
  CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.Stage1.Thm6
  CFSG.GH74.GLS.Stage1.Thm6.Sec12

variable {G : Type} [Group G] [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}

section Coords

variable {h : IsAConfig 5 x K T Q S a}

theorem Coord5.rco_x (c : Coord5 h) : c.rco x = f1 := by
  rw [Coord5.rco_of_mem c (h.T_le_C h.x_mem_T)]
  exact Coord5.x_co (c := c)

theorem Coord5.rco_x'
    {c : Coord5 h} (hc : Case47 h c) : c.rco (a * x * a⁻¹) = e1 := by
  have hx'P : a * x * a⁻¹ ∈ c.lift Pm := by
    rw [← Coord5.P_eq_lift (c := c)]
    exact x_conj_mem_P hc
  have h1 : c.rco (a * x * a⁻¹) ∈ Pm := Coord5.rco_mem c hx'P
  have hx'T : a * x * a⁻¹ ∈ T := h.conj_x_mem
  have h2 : c.rco (a * x * a⁻¹) ∈ ZTl := by
    refine T5_cent_Z (c.rco_mem_T5 hx'T) (fun t ht => ?_)
    obtain ⟨t₀, ht₀, rfl⟩ := c.exists_T_rco ht
    rw [← c.rco_T_mul hx'T ht₀, ← c.rco_T_mul ht₀ hx'T]
    congr 1
    exact (h.conj_x_comm ht₀).symm
  rcases ZTl_P h1 h2 with h3 | h3
  · exfalso
    have : c.rco (a * x * a⁻¹) = c.rco 1 := by rw [h3, Coord5.rco_one]
    exact conj_x_ne_one h (c.rco_T_inj hx'T T.one_mem this)
  · exact h3

theorem Coord5.rco_v
    {c : Coord5 h} (hc : Case47 h c) : c.rco (L4.vElt x a) = f1 * e1 := by
  show c.rco (x * (a * x * a⁻¹)) = f1 * e1
  rw [c.rco_T_mul h.x_mem_T h.conj_x_mem, Coord5.rco_x, Coord5.rco_x' hc]

end Coords

variable {h : IsAConfig 5 x K T Q S a} {c : Coord5 h}

theorem x_not_conj_v
    (_hc : Case47 h c) : ¬ IsConj x (L4.vElt x a) :=
  not_isConj_x_v5 h (card_T_five h c)

omit [Finite G] in
theorem x'_conj_x (x a : G) : IsConj (a * x * a⁻¹) x :=
  isConj_iff.2 ⟨a⁻¹, by group⟩

theorem x'_eq_x_mul_v (h : IsAConfig 5 x K T Q S a) : a * x * a⁻¹ = x * L4.vElt x a :=
  (L4.x_mul_v h).symm

theorem v_mem_R
    (hc : Case47 h c) : L4.vElt x a ∈ c.lift Rm := by
  have h1 : x ∈ c.lift Rm := Q_le_R h c h.x_mem_Q
  have h2 : a * x * a⁻¹ ∈ c.lift Rm := P_le_R h c (x_conj_mem_P hc)
  exact mul_mem h1 h2

theorem isConj_v_of_Mixm
    (hc : Case47 h c) {t : G} (ht : t ∈ T) (hm : Mixm (c.rco t)) :
    IsConj t (L4.vElt x a) := by
  have hl : t ∈ c.lift Rm := (Coord5.mem_lift_rco c).2 ⟨h.T_le_C ht, hm.1⟩
  refine isConj_v_of_mixed hc hl ?_ ?_
  · intro hP
    apply hm.2.1
    rw [Coord5.P_eq_lift (c := c)] at hP
    exact Coord5.rco_mem c hP
  · intro hQ
    apply hm.2.2
    rw [Coord5.Q_eq_lift (c := c)] at hQ
    exact Coord5.rco_mem c hQ

theorem isConj_x_of_R_nonmixed
    (hc : Case47 h c) {t : G} (ht : t ∈ c.lift Rm) (ht1 : t ≠ 1)
    (hnm : ¬ Mixm (c.rco t)) : IsConj t x := by
  have htC := Coord5.lift_mem_cent ht
  have hrm : c.rco t ∈ Rm := Coord5.rco_mem c ht
  have hor : c.rco t ∈ Pm ∨ c.rco t ∈ Qm := by
    by_contra hcon
    push Not at hcon
    exact hnm ⟨hrm, hcon.1, hcon.2⟩
  rcases hor with hP | hQ
  · have htP : t ∈ T ⊓ K := by
      rw [Coord5.P_eq_lift (c := c)]
      exact (Coord5.mem_lift_rco c).2 ⟨htC, hP⟩
    exact isConj_x_of_PQ hc (Or.inl htP) ht1
  · have htQ : t ∈ Q := by
      rw [Coord5.Q_eq_lift (c := c)]
      exact (Coord5.mem_lift_rco c).2 ⟨htC, hQ⟩
    exact isConj_x_of_PQ hc (Or.inr htQ) ht1

theorem JR_conj_G
    (c : Coord5 h) {t₁ t₂ : G} (h1 : t₁ ∈ T) (h1R : t₁ ∉ c.lift Rm)
    (h1s : t₁ * t₁ = 1) (h2 : t₂ ∈ T) (h2R : t₂ ∉ c.lift Rm) (h2s : t₂ * t₂ = 1) :
    ∃ r ∈ c.lift Rm, r * t₁ * r⁻¹ = t₂ := by
  have m1 := c.rco_mem_T5 h1
  have m2 := c.rco_mem_T5 h2
  have n1 : c.rco t₁ ∉ Rm := fun hm => h1R ((Coord5.mem_lift_rco c).2 ⟨h.T_le_C h1, hm⟩)
  have n2 : c.rco t₂ ∉ Rm := fun hm => h2R ((Coord5.mem_lift_rco c).2 ⟨h.T_le_C h2, hm⟩)
  have s1 : c.rco t₁ * c.rco t₁ = 1 := by rw [← c.rco_T_mul h1 h1, h1s, Coord5.rco_one]
  have s2 : c.rco t₂ * c.rco t₂ = 1 := by rw [← c.rco_T_mul h2 h2, h2s, Coord5.rco_one]
  obtain ⟨r, hr, hrt⟩ := T5_JR_conj m1 s1 n1 m2 s2 n2
  obtain ⟨g, hg, hgr⟩ := Coord5.exists_lift_rco c Rm_le_Fgrp hr
  have hgT : g ∈ T := Coord5.Rg_le_T (c := c) hg
  refine ⟨g, hg, ?_⟩
  apply c.rco_T_inj (T.mul_mem (T.mul_mem hgT h1) (T.inv_mem hgT)) h2
  rw [c.rco_T_mul (T.mul_mem hgT h1) (T.inv_mem hgT), c.rco_T_mul hgT h1, c.rco_T_inv hgT, hgr]
  exact hrt

theorem v_comm_S
    (hc : Case47 h c) {s : G} (hs : s ∈ S) :
    s * L4.vElt x a = L4.vElt x a * s := by
  have hv := h.sup_le_centralizer_v
  have hT' : ∀ t ∈ T, t * L4.vElt x a = L4.vElt x a * t := fun t ht =>
    mem_centralizer_singleton_iff.1 (hv (Subgroup.mem_sup_left ht))
  have ha' : a * L4.vElt x a = L4.vElt x a * a :=
    mem_centralizer_singleton_iff.1 (hv (Subgroup.mem_sup_right (Subgroup.mem_zpowers a)))
  rcases (mem_S_iff hc).1 hs with h1 | ⟨t, ht, rfl⟩
  · exact hT' s h1
  · calc a * t * L4.vElt x a = a * (t * L4.vElt x a) := by group
      _ = a * (L4.vElt x a * t) := by rw [hT' t ht]
      _ = (a * L4.vElt x a) * t := by group
      _ = L4.vElt x a * (a * t) := by rw [ha']; group

theorem S_nT_conj_x
    (hc : Case47 h c) {s : G} (hs : s ∈ S) (hsT : s ∉ T) :
    s * x * s⁻¹ = a * x * a⁻¹ := by
  rcases (mem_S_iff hc).1 hs with h1 | ⟨t, ht, rfl⟩
  · exact absurd h1 hsT
  · have h2 : t * x = x * t := mem_centralizer_singleton_iff.1 (h.T_le_C ht)
    calc a * t * x * (a * t)⁻¹ = a * (t * x) * t⁻¹ * a⁻¹ := by group
      _ = a * (x * t) * t⁻¹ * a⁻¹ := by rw [h2]
      _ = a * x * a⁻¹ := by group

theorem S_inf_C_eq (h : IsAConfig 5 x K T Q S a) : S ⊓ centralizer ({x} : Set G) = T := by
  apply h.sylowT.eq_of_le (le_inf h.T_lt_S.le h.T_le_C) inf_le_right
  exact (isSylowOf_iff.1 h.sylowS).2.1.to_inf_left

theorem isSylow2In_Sx (h : IsAConfig 5 x K T Q S a) :
    IsSylow2In (S ⊓ centralizer ({x} : Set G)) (centralizer ({x} : Set G)) := by
  rw [S_inf_C_eq h]
  exact isSylowOf_iff.1 h.sylowT

theorem scp_x (h : IsAConfig 5 x K T Q S a) {u : G} (huc : IsConj u x) :
    ∃ g : G, g * u * g⁻¹ = x ∧ ∀ z ∈ S, z * u = u * z → g * z * g⁻¹ ∈ T := by
  obtain ⟨g₀, hg₀⟩ := isConj_iff.1 huc
  obtain ⟨g, hg1, hg2⟩ := scp (isSylowOf_iff.1 h.sylowS).2.1 (isSylow2In_Sx h) hg₀
  refine ⟨g, hg1, fun z hz hzu => ?_⟩
  have := hg2 z hz hzu
  rwa [S_inf_C_eq h] at this

theorem isSylow2In_Sv
    (hc : Case47 h c) :
    IsSylow2In S (centralizer ({L4.vElt x a} : Set G)) := by
  have hSC : S ≤ centralizer ({L4.vElt x a} : Set G) := fun s hs =>
    mem_centralizer_singleton_iff.2 (v_comm_S hc hs)
  exact isSylowOf_iff.1 (h.sylowS.of_le hSC le_top)

theorem scp_v
    (hc : Case47 h c) {u : G} (huc : IsConj u (L4.vElt x a)) :
    ∃ g : G, g * u * g⁻¹ = L4.vElt x a ∧ ∀ z ∈ S, z * u = u * z → g * z * g⁻¹ ∈ S := by
  obtain ⟨g₀, hg₀⟩ := isConj_iff.1 huc
  have hSC : S ≤ centralizer ({L4.vElt x a} : Set G) := fun s hs =>
    mem_centralizer_singleton_iff.2 (v_comm_S hc hs)
  have hext : IsSylow2In (S ⊓ centralizer ({L4.vElt x a} : Set G))
      (centralizer ({L4.vElt x a} : Set G)) := by
    rw [inf_eq_left.2 hSC]
    exact isSylow2In_Sv hc
  obtain ⟨g, hg1, hg2⟩ := scp (isSylowOf_iff.1 h.sylowS).2.1 hext hg₀
  exact ⟨g, hg1, fun z hz hzu => (hg2 z hz hzu).1⟩

end CFSG.GH74.GLS.C3.Layer2.L5
