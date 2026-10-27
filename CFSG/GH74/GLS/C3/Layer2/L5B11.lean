module

public import CFSG.GH74.GLS.C3.Layer2.L5B10
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public meta import CFSG.GH74.GLS.C3.Layer2.L5Fin
public meta import CFSG.GH74.GLS.C3.Layer2.L5A1
public import Certificates.Certificate5045
public import Certificates.Certificate5046
public import Certificates.Certificate5047
public import Certificates.Certificate5050
public import Certificates.Certificate5091

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Prop121
  CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

theorem e1_ne_one' : (e1 : Amb 5) ≠ 1 :=
  Certificates.certificate5047.1

theorem e2_ne_one' : (e2 : Amb 5) ≠ 1 :=
  Certificates.certificate5047.2.1

theorem e1e2_ne_one' : (e1 * e2 : Amb 5) ≠ 1 :=
  Certificates.certificate5047.2.2.1

theorem f1_ne_one' : (f1 : Amb 5) ≠ 1 :=
  Certificates.certificate5047.2.2.2

variable {G : Type} [Group G] [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}

section Mg2

variable {h : IsAConfig 5 x K T Q S a} {c : Coord5 h}

theorem swap_q_mem
    (hc : Case47 h c) {u : G} (hu : u ∈ S) (huT : u ∉ T) {p : G}
    (hp : p ∈ T ⊓ K) : u * p * u⁻¹ ∈ Q := by
  rw [← cj_S_P hc hu huT]
  exact mem_cj_self hp

theorem ep_mem_R
    (hc : Case47 h c) {u : G} (hu : u ∈ S) (huT : u ∉ T) {p : G}
    (hp : p ∈ T ⊓ K) : p * (u * p * u⁻¹) ∈ c.lift Rm :=
  (c.lift Rm).mul_mem (P_le_R h c hp) (Q_le_R h c (swap_q_mem hc hu huT hp))

theorem ep_comm
    (hc : Case47 h c) {u : G} (hu : u ∈ S) (huT : u ∉ T) (huu : u * u = 1) {p : G}
    (hp : p ∈ T ⊓ K) : u * (p * (u * p * u⁻¹)) * u⁻¹ = p * (u * p * u⁻¹) := by
  have hq := swap_q_mem hc hu huT hp
  have hu1 : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  have e : u * (p * (u * p * u⁻¹)) * u⁻¹ = (u * p * u⁻¹) * ((u * u) * p * (u⁻¹ * u⁻¹)) := by group
  have e2 : u⁻¹ * u⁻¹ = 1 := by rw [hu1]; exact huu
  rw [e, huu, e2]
  simp only [one_mul, mul_one]
  exact (PQ_comm_G h c p hp _ hq).symm

theorem ep_mul_u (c : Coord5 h) {u : G} {p : G} (hp : p ∈ T ⊓ K) :
    p * (u * p * u⁻¹) * u = p * u * p⁻¹ := by
  have hp2 : p * p = 1 := R_sq_G c (P_le_R h c hp)
  have hp1 : p⁻¹ = p := inv_eq_of_mul_eq_one_right hp2
  rw [hp1]
  group

theorem ep_mul
    (hc : Case47 h c) {u : G} (hu : u ∈ S) (huT : u ∉ T) {p p' : G}
    (hp : p ∈ T ⊓ K) (hp' : p' ∈ T ⊓ K) :
    (p * p') * (u * (p * p') * u⁻¹) = (p * (u * p * u⁻¹)) * (p' * (u * p' * u⁻¹)) := by
  have hq := swap_q_mem hc hu huT hp
  have hc' : p' * (u * p * u⁻¹) = (u * p * u⁻¹) * p' := PQ_comm_G h c p' hp' _ hq
  calc (p * p') * (u * (p * p') * u⁻¹) = p * (p' * (u * p * u⁻¹)) * (u * p' * u⁻¹) := by group
    _ = p * ((u * p * u⁻¹) * p') * (u * p' * u⁻¹) := by rw [hc']
    _ = (p * (u * p * u⁻¹)) * (p' * (u * p' * u⁻¹)) := by group

theorem ep_ne_one
    (hc : Case47 h c) {u : G} (hu : u ∈ S) (huT : u ∉ T) {p : G}
    (hp : p ∈ T ⊓ K) (hp1 : p ≠ 1) : p * (u * p * u⁻¹) ≠ 1 := by
  intro e
  have hq := swap_q_mem hc hu huT hp
  have hpQ : p ∈ Q := by
    have : p = (u * p * u⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left e
    rw [this]
    exact Q.inv_mem hq
  have h2 : p ∈ (T ⊓ K) ⊓ Q := ⟨hp, hpQ⟩
  rw [P_inf_Q h c] at h2
  exact hp1 (Subgroup.mem_bot.1 h2)

theorem not_conj_x_nT
    (hc : Case47 h c) {u : G} (hu : u ∈ S) (huT : u ∉ T) (huu : u * u = 1) :
    ¬ IsConj u x := by
  intro huc
  obtain ⟨g, hg1, hg2⟩ := scp_x h huc
  have hxR : x ∈ c.lift Rm := Q_le_R h c h.x_mem_Q
  have key : ∀ p ∈ T ⊓ K, p ≠ 1 →
      g * (p * (u * p * u⁻¹)) * g⁻¹ ∈ c.lift Rm ∧
        Mixm (c.rco (g * (p * (u * p * u⁻¹)) * g⁻¹)) ∧
        ¬ Mixm (c.rco (x * (g * (p * (u * p * u⁻¹)) * g⁻¹))) := by
    intro p hp hp1
    have heR := ep_mem_R hc hu huT hp
    have heS : p * (u * p * u⁻¹) ∈ S := R_le_S hc heR
    have hec := ep_comm hc hu huT huu hp
    have he1 := ep_ne_one hc hu huT hp hp1
    have hev := cent_swap_conj_v hc hu huT heR he1 hec
    have heu : p * (u * p * u⁻¹) * u = u * (p * (u * p * u⁻¹)) := by
      calc p * (u * p * u⁻¹) * u = (u * (p * (u * p * u⁻¹)) * u⁻¹) * u := by rw [hec]
        _ = u * (p * (u * p * u⁻¹)) := by group
    have heT : g * (p * (u * p * u⁻¹)) * g⁻¹ ∈ T := hg2 _ heS heu
    have hesq := R_sq_G c heR
    have he'sq : (g * (p * (u * p * u⁻¹)) * g⁻¹) * (g * (p * (u * p * u⁻¹)) * g⁻¹) = 1 := by
      calc (g * (p * (u * p * u⁻¹)) * g⁻¹) * (g * (p * (u * p * u⁻¹)) * g⁻¹)
          = g * ((p * (u * p * u⁻¹)) * (p * (u * p * u⁻¹))) * g⁻¹ := by group
        _ = 1 := by rw [hesq]; group
    have he'1 : g * (p * (u * p * u⁻¹)) * g⁻¹ ≠ 1 := by
      intro e
      apply he1
      calc p * (u * p * u⁻¹) = g⁻¹ * (g * (p * (u * p * u⁻¹)) * g⁻¹) * g := by group
        _ = 1 := by rw [e]; group
    have he'v : IsConj (g * (p * (u * p * u⁻¹)) * g⁻¹) (L4.vElt x a) :=
      (isConj_conj g _).symm.trans hev
    have hxe' : IsConj x (x * (g * (p * (u * p * u⁻¹)) * g⁻¹)) := by
      refine isConj_iff.2 ⟨g * p * g⁻¹, ?_⟩
      have h1 : (g * p * g⁻¹) * x * (g * p * g⁻¹)⁻¹ = g * (p * u * p⁻¹) * g⁻¹ := by
        rw [← hg1]; group
      have h2 : x * (g * (p * (u * p * u⁻¹)) * g⁻¹) = g * (u * (p * (u * p * u⁻¹))) * g⁻¹ := by
        rw [← hg1]; group
      rw [h1, h2, ← ep_mul_u c hp, heu]
    have hxe'T : x * (g * (p * (u * p * u⁻¹)) * g⁻¹) ∈ T := T.mul_mem h.x_mem_T heT
    have he'R : g * (p * (u * p * u⁻¹)) * g⁻¹ ∈ c.lift Rm := by
      by_contra hnot
      have hxe'R : x * (g * (p * (u * p * u⁻¹)) * g⁻¹) ∉ c.lift Rm := fun hh => hnot (by
        have := (c.lift Rm).mul_mem ((c.lift Rm).inv_mem hxR) hh
        have e : x⁻¹ * (x * (g * (p * (u * p * u⁻¹)) * g⁻¹)) =
            g * (p * (u * p * u⁻¹)) * g⁻¹ := by group
        rwa [e] at this)
      have hcomm : (g * (p * (u * p * u⁻¹)) * g⁻¹) * x = x * (g * (p * (u * p * u⁻¹)) * g⁻¹) :=
        mem_centralizer_singleton_iff.1 (h.T_le_C heT)
      have hxe'sq : (x * (g * (p * (u * p * u⁻¹)) * g⁻¹)) *
          (x * (g * (p * (u * p * u⁻¹)) * g⁻¹)) = 1 := by
        calc (x * (g * (p * (u * p * u⁻¹)) * g⁻¹)) * (x * (g * (p * (u * p * u⁻¹)) * g⁻¹))
            = x * ((g * (p * (u * p * u⁻¹)) * g⁻¹) * x) * (g * (p * (u * p * u⁻¹)) * g⁻¹) := by
              group
          _ = x * (x * (g * (p * (u * p * u⁻¹)) * g⁻¹)) * (g * (p * (u * p * u⁻¹)) * g⁻¹) := by
              rw [hcomm]
          _ = (x * x) * ((g * (p * (u * p * u⁻¹)) * g⁻¹) * (g * (p * (u * p * u⁻¹)) * g⁻¹)) := by
              group
          _ = 1 := by rw [L4.x_mul_self h, he'sq, one_mul]
      obtain ⟨r, _, hrt⟩ := JR_conj_G c heT hnot he'sq hxe'T hxe'R hxe'sq
      have h3 : IsConj (g * (p * (u * p * u⁻¹)) * g⁻¹) (x * (g * (p * (u * p * u⁻¹)) * g⁻¹)) :=
        isConj_iff.2 ⟨r, hrt⟩
      exact x_not_conj_v hc (hxe'.trans (h3.symm.trans he'v))
    refine ⟨he'R, ?_, ?_⟩
    · by_contra hnm
      exact x_not_conj_v hc ((isConj_x_of_R_nonmixed hc he'R he'1 hnm).symm.trans he'v)
    · intro hm
      exact x_not_conj_v hc (hxe'.trans (isConj_v_of_Mixm hc hxe'T hm))
  obtain ⟨p₁, hp₁, hr₁⟩ := Coord5.exists_lift_rco c Pm_le_Fgrp e1_mem_Pm
  obtain ⟨p₂, hp₂, hr₂⟩ := Coord5.exists_lift_rco c Pm_le_Fgrp e2_mem_Pm
  have hp₁P : p₁ ∈ T ⊓ K := by rw [Coord5.P_eq_lift (c := c)]; exact hp₁
  have hp₂P : p₂ ∈ T ⊓ K := by rw [Coord5.P_eq_lift (c := c)]; exact hp₂
  have hp₁₂P : p₁ * p₂ ∈ T ⊓ K := (T ⊓ K).mul_mem hp₁P hp₂P
  have hp₁ne : p₁ ≠ 1 := fun e => e1_ne_one' (by rw [← hr₁, e, Coord5.rco_one])
  have hp₂ne : p₂ ≠ 1 := fun e => e2_ne_one' (by rw [← hr₂, e, Coord5.rco_one])
  have hp₁₂ne : p₁ * p₂ ≠ 1 := fun e => e1e2_ne_one' (by
    rw [← hr₁, ← hr₂, ← c.rco_T_mul hp₁P.1 hp₂P.1, e, Coord5.rco_one])
  obtain ⟨hA₁, hM₁, hN₁⟩ := key p₁ hp₁P hp₁ne
  obtain ⟨hA₂, hM₂, hN₂⟩ := key p₂ hp₂P hp₂ne
  obtain ⟨hA₁₂, hM₁₂, hN₁₂⟩ := key (p₁ * p₂) hp₁₂P hp₁₂ne
  have hmul : g * ((p₁ * p₂) * (u * (p₁ * p₂) * u⁻¹)) * g⁻¹ =
      (g * (p₁ * (u * p₁ * u⁻¹)) * g⁻¹) * (g * (p₂ * (u * p₂ * u⁻¹)) * g⁻¹) := by
    rw [ep_mul hc hu huT hp₁P hp₂P]
    group
  have hT₁ : g * (p₁ * (u * p₁ * u⁻¹)) * g⁻¹ ∈ T := Coord5.Rg_le_T (c := c) hA₁
  have hT₂ : g * (p₂ * (u * p₂ * u⁻¹)) * g⁻¹ ∈ T := Coord5.Rg_le_T (c := c) hA₂
  have hab : Mixm (c.rco (g * (p₁ * (u * p₁ * u⁻¹)) * g⁻¹) *
      c.rco (g * (p₂ * (u * p₂ * u⁻¹)) * g⁻¹)) := by
    rw [← c.rco_T_mul hT₁ hT₂, ← hmul]
    exact hM₁₂
  have hf1R : (f1 : Amb 5) ∈ Rm := Qm_le_Rm f1_mem_Qm'
  have hfm : ¬ Mixm (f1 : Amb 5) := fun hm => hm.2.2 f1_mem_Qm'
  have hx5 : c.rco x = f1 := Coord5.rco_x c
  rcases four_F hM₁ hM₂ hab hf1R f1_ne_one' hfm with hh | hh | hh
  · apply hN₁
    rw [c.rco_T_mul h.x_mem_T hT₁, hx5]
    exact hh
  · apply hN₂
    rw [c.rco_T_mul h.x_mem_T hT₂, hx5]
    exact hh
  · apply hN₁₂
    rw [hmul, c.rco_T_mul h.x_mem_T (T.mul_mem hT₁ hT₂), c.rco_T_mul hT₁ hT₂, hx5]
    exact hh

theorem Mg2
    (hsimple : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a) (hc : Case47 h c)
    (haa : a * a = 1) {u : G} (hu : u ∈ S) (huT : u ∉ T) (huu : u * u = 1) :
    IsConj u (L4.vElt x a) := by
  have hu1 : u ≠ 1 := fun e => huT (e ▸ T.one_mem)
  rcases invol_conj_x_or_v hsimple hnab hc haa u huu hu1 with h1 | h1
  · exact absurd h1 (not_conj_x_nT hc hu huT huu)
  · exact h1

end Mg2

end CFSG.GH74.GLS.C3.Layer2.L5
