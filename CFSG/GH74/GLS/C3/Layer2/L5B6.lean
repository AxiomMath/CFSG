module

public import CFSG.GH74.GLS.C3.Layer2.L5B1

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Prop121
  CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

variable {G : Type} [Group G] [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}

theorem mem_S_iff
    {h : IsAConfig 5 x K T Q S a} {c : Coord5 h} (hc : Case47 h c) {g : G} :
    g ∈ S ↔ g ∈ T ∨ ∃ t ∈ T, g = a * t := by
  rw [S_eq_Mh hc]
  exact mem_Mh

theorem relIndex_T_S
    {h : IsAConfig 5 x K T Q S a} {c : Coord5 h} (hc : Case47 h c) :
    T.relIndex S = 2 := by
  rw [S_eq_Mh hc]
  exact relIndex_T_Mh h

theorem S_norm_T
    {h : IsAConfig 5 x K T Q S a} {c : Coord5 h} (hc : Case47 h c) {s : G}
    (hs : s ∈ S) {t : G} (ht : t ∈ T) : s * t * s⁻¹ ∈ T := by
  rcases (mem_S_iff hc).1 hs with h1 | ⟨t', ht', rfl⟩
  · exact T.mul_mem (T.mul_mem h1 ht) (T.inv_mem h1)
  · have h2 : t' * t * t'⁻¹ ∈ T := T.mul_mem (T.mul_mem ht' ht) (T.inv_mem ht')
    have h3 := (mem_normalizer_iff.1 h.a_mem.2.1 _).1 h2
    have e : a * t' * t * (a * t')⁻¹ = a * (t' * t * t'⁻¹) * a⁻¹ := by group
    rw [e]
    exact h3

theorem S_norm_R
    {h : IsAConfig 5 x K T Q S a} {c : Coord5 h} (hc : Case47 h c) {s : G}
    (hs : s ∈ S) {r : G} (hr : r ∈ c.lift Rm) : s * r * s⁻¹ ∈ c.lift Rm := by
  have hsM : s ∈ Mh h := by rw [← S_eq_Mh hc]; exact hs
  have hsN : s ∈ normalizer ((Mh h : Subgroup G) : Set G) := Subgroup.le_normalizer hsM
  exact (mem_normalizer_iff.1 (R_char_M hc s hsN) r).1 hr

theorem cj_S_P
    {h : IsAConfig 5 x K T Q S a} {c : Coord5 h} (hc : Case47 h c) {s : G}
    (hs : s ∈ S) (hsT : s ∉ T) : cj s (T ⊓ K) = Q := by
  rcases (mem_S_iff hc).1 hs with h1 | ⟨t, ht, rfl⟩
  · exact absurd h1 hsT
  · exact cj_aT_P hc ht

theorem cj_S_Q
    {h : IsAConfig 5 x K T Q S a} {c : Coord5 h} (hc : Case47 h c) {s : G}
    (hs : s ∈ S) (hsT : s ∉ T) : cj s Q = T ⊓ K := by
  rcases (mem_S_iff hc).1 hs with h1 | ⟨t, ht, rfl⟩
  · exact absurd h1 hsT
  · exact cj_aT_Q hc ht

theorem relIndex_R_S
    {h : IsAConfig 5 x K T Q S a} {c : Coord5 h} (hc : Case47 h c) :
    (c.lift Rm).relIndex S = 4 := by
  have h1 := Subgroup.relIndex_mul_relIndex (c.lift Rm) T S (Coord5.Rg_le_T (c := c))
    h.T_lt_S.le
  rw [relIndex_R_T h c, relIndex_T_S hc] at h1
  omega

theorem PQ_unique
    (h : IsAConfig 5 x K T Q S a) (c : Coord5 h) {p p' q q' : G} (hp : p ∈ T ⊓ K)
    (hp' : p' ∈ T ⊓ K) (hq : q ∈ Q) (hq' : q' ∈ Q) (he : p * q = p' * q') : p = p' ∧ q = q' := by
  have h1 : p'⁻¹ * p = q' * q⁻¹ := by
    calc p'⁻¹ * p = p'⁻¹ * (p * q) * q⁻¹ := by group
      _ = p'⁻¹ * (p' * q') * q⁻¹ := by rw [he]
      _ = q' * q⁻¹ := by group
  have h2 : p'⁻¹ * p ∈ (T ⊓ K) ⊓ Q :=
    ⟨(T ⊓ K).mul_mem ((T ⊓ K).inv_mem hp') hp, h1 ▸ Q.mul_mem hq' (Q.inv_mem hq)⟩
  rw [P_inf_Q h c] at h2
  have h3 : p'⁻¹ * p = 1 := Subgroup.mem_bot.1 h2
  have hpp : p = p' := by
    calc p = p' * (p'⁻¹ * p) := by group
      _ = p' := by rw [h3, mul_one]
  refine ⟨hpp, ?_⟩
  rw [hpp] at he
  exact mul_left_cancel he

theorem cent_R_swap
    {h : IsAConfig 5 x K T Q S a} {c : Coord5 h} (hc : Case47 h c) {s : G}
    (hs : s ∈ S) (hsT : s ∉ T) {r : G} (hr : r ∈ c.lift Rm) (hsr : s * r * s⁻¹ = r) :
    ∃ p ∈ T ⊓ K, r = p * (s * p * s⁻¹) := by
  obtain ⟨p, hp, q, hq, rfl⟩ := R_prod_G c hr
  have hq' : s * p * s⁻¹ ∈ Q := by rw [← cj_S_P hc hs hsT]; exact mem_cj_self hp
  have hp' : s * q * s⁻¹ ∈ T ⊓ K := by rw [← cj_S_Q hc hs hsT]; exact mem_cj_self hq
  have hcomm : (s * q * s⁻¹) * (s * p * s⁻¹) = (s * p * s⁻¹) * (s * q * s⁻¹) :=
    PQ_comm_G h c _ hp' _ hq'
  have h1 : (s * q * s⁻¹) * (s * p * s⁻¹) = p * q := by
    calc (s * q * s⁻¹) * (s * p * s⁻¹) = (s * p * s⁻¹) * (s * q * s⁻¹) := hcomm
      _ = s * (p * q) * s⁻¹ := by group
      _ = p * q := hsr
  obtain ⟨_, e2⟩ := PQ_unique h c hp' hp hq' hq h1
  refine ⟨p, hp, ?_⟩
  rw [e2]

theorem exists_invol_aT
    {h : IsAConfig 5 x K T Q S a} {c : Coord5 h} (hc : Case47 h c)
    (haR : a * a ∈ c.lift Rm) : ∃ p ∈ T ⊓ K, (p * a) * (p * a) = 1 := by
  have hfix : a * (a * a) * a⁻¹ = a * a := by group
  obtain ⟨p, hp, hpr⟩ := cent_R_swap hc h.a_mem.1 h.a_mem.2.2.1 haR hfix
  refine ⟨p, hp, ?_⟩
  have hsq : (a * a) * (a * a) = 1 := Coord5.lift_sq (c := c) (M := Rm) (fun p hp => Rm_sq p hp) haR
  calc p * a * (p * a) = (p * (a * p * a⁻¹)) * (a * a) := by group
    _ = (a * a) * (a * a) := by rw [← hpr]
    _ = 1 := hsq

theorem IsAConfig.of_mul (h : IsAConfig 5 x K T Q S a) {t : G} (ht : t ∈ T) :
    IsAConfig 5 x K T Q S (t * a) := by
  refine { h with a_mem := ?_ }
  obtain ⟨haS, haN, haT, haa⟩ := h.a_mem
  refine ⟨S.mul_mem (h.T_lt_S.le ht) haS, mul_mem (Subgroup.le_normalizer ht) haN, ?_, ?_⟩
  · intro hta
    apply haT
    have : a = t⁻¹ * (t * a) := by group
    rw [this]
    exact T.mul_mem (T.inv_mem ht) hta
  · have h1 : a * t * a⁻¹ ∈ T := (mem_normalizer_iff.1 haN t).1 ht
    have e : (t * a) ^ 2 = t * (a * t * a⁻¹) * a ^ 2 := by rw [pow_two, pow_two]; group
    rw [e]
    exact T.mul_mem (T.mul_mem ht h1) haa

@[expose] def Coord5.ofEq {h : IsAConfig 5 x K T Q S a} (c : Coord5 h) {a' : G}
    (h' : IsAConfig 5 x K T Q S a') : Coord5 h' :=
  ⟨c.ι, c.hι1, c.hιQ, c.hιT⟩

theorem Case47.ofEq
    {h : IsAConfig 5 x K T Q S a} {c : Coord5 h} (hc : Case47 h c) {a' : G}
    (h' : IsAConfig 5 x K T Q S a') : Case47 h' (c.ofEq h') := hc

end CFSG.GH74.GLS.C3.Layer2.L5
