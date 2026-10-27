module

public import CFSG.GH74.GLS.C3.Layer2.L5B9

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Prop121
  CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

variable {G : Type} [Group G] [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}

section CaseI

variable {h : IsAConfig 5 x K T Q S a} {c : Coord5 h}

theorem R_sq_G
    (c : Coord5 h) {r : G} (hr : r ∈ c.lift Rm) : r * r = 1 :=
  Coord5.lift_sq (c := c) (M := Rm) (fun p hp => Rm_sq p hp) hr

theorem R_comm_G
    (c : Coord5 h) {r r' : G} (hr : r ∈ c.lift Rm) (hr' : r' ∈ c.lift Rm) :
    r * r' = r' * r :=
  Coord5.lift_comm (c := c) (M := Rm) (fun p hp q hq => Rm_comm p hp q hq) hr hr'

theorem R_le_S
    (_hc : Case47 h c) : c.lift Rm ≤ S := (Coord5.Rg_le_T (c := c)).trans h.T_lt_S.le

theorem sq_mem_R_of_aa
    (hc : Case47 h c) (haR : a * a ∈ c.lift Rm) :
    ∀ s ∈ S, s * s ∈ c.lift Rm := by
  intro s hs
  rcases (mem_S_iff hc).1 hs with h1 | ⟨t, ht, rfl⟩
  · exact T_sq_mem_R c h1
  · have e : a * t * (a * t) = (a * a) * ((a⁻¹ * t * a) * t) := by group
    rw [e]
    exact (c.lift Rm).mul_mem haR (wt_mem_R hc ht)

theorem hfree_S
    (hc : Case47 h c) {u : G} (huS : u ∈ S) (huR : u ∉ c.lift Rm) (huu : u * u = 1)
    {t : G} (_htS : t ∈ S) (htu : t * u ∈ c.lift Rm) (htt : t * t = 1) :
    ∃ g : G, g * u * g⁻¹ = t := by
  have hu1 : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  by_cases huT : u ∈ T
  · have hRT : c.lift Rm ≤ T := Coord5.Rg_le_T (c := c)
    have htT : t ∈ T := by
      have h1 : t * u * u⁻¹ ∈ T := T.mul_mem (hRT htu) (T.inv_mem huT)
      simpa using h1
    have htR : t ∉ c.lift Rm := fun hh => huR (by
      have := (c.lift Rm).mul_mem ((c.lift Rm).inv_mem hh) htu
      simpa using this)
    obtain ⟨r, _, hr⟩ := JR_conj_G c huT huR huu htT htR htt
    exact ⟨r, hr⟩
  · set r : G := t * u with hr
    have hrR : r ∈ c.lift Rm := htu
    have hur : u * r * u⁻¹ = r := by
      have h1 : r * (u * r * u⁻¹) = 1 := by
        calc r * (u * r * u⁻¹) = t * (u * u) * t := by rw [hr]; group
          _ = 1 := by rw [huu, mul_one]; exact htt
      have h3 : u * r * u⁻¹ = r⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [h3]
      exact inv_eq_of_mul_eq_one_right (R_sq_G c hrR)
    obtain ⟨p, hp, hpr⟩ := cent_R_swap hc huS huT hrR hur
    have hp2 : p * p = 1 := R_sq_G c (P_le_R h c hp)
    refine ⟨p, ?_⟩
    have ht' : t = r * u⁻¹ := by rw [hr]; group
    have hp1 : p⁻¹ = p := inv_eq_of_mul_eq_one_right hp2
    calc p * u * p⁻¹ = p * u * p := by rw [hp1]
      _ = p * (u * p * u⁻¹) * u⁻¹ := by
          have : u⁻¹ * u⁻¹ = 1 := by rw [hu1]; exact huu
          calc p * u * p = p * u * p * (u⁻¹ * u⁻¹) := by rw [this, mul_one]
            _ = p * (u * p * u⁻¹) * u⁻¹ := by group
      _ = t := by rw [← hpr]; exact ht'.symm

theorem cent_swap_conj_v
    (hc : Case47 h c) {s : G} (hs : s ∈ S) (hsT : s ∉ T) {r : G}
    (hr : r ∈ c.lift Rm) (hr1 : r ≠ 1) (hsr : s * r * s⁻¹ = r) :
    IsConj r (L4.vElt x a) := by
  obtain ⟨p, hp, hpr⟩ := cent_R_swap hc hs hsT hr hsr
  have hq : s * p * s⁻¹ ∈ Q := by rw [← cj_S_P hc hs hsT]; exact mem_cj_self hp
  have hp1 : p ≠ 1 := fun e => hr1 (by rw [hpr, e]; group)
  refine isConj_v_of_mixed hc hr (fun hP => ?_) (fun hQ => ?_)
  · have h1 : s * p * s⁻¹ ∈ T ⊓ K := by
      have e : s * p * s⁻¹ = p⁻¹ * r := by rw [hpr]; group
      rw [e]
      exact (T ⊓ K).mul_mem ((T ⊓ K).inv_mem hp) hP
    have h2 : s * p * s⁻¹ ∈ (T ⊓ K) ⊓ Q := ⟨h1, hq⟩
    rw [P_inf_Q h c] at h2
    have h3 : s * p * s⁻¹ = 1 := Subgroup.mem_bot.1 h2
    apply hp1
    calc p = s⁻¹ * (s * p * s⁻¹) * s := by group
      _ = 1 := by rw [h3]; group
  · have h1 : p ∈ Q := by
      have e : p = r * (s * p * s⁻¹)⁻¹ := by rw [hpr]; group
      rw [e]
      exact Q.mul_mem hQ (Q.inv_mem hq)
    have h2 : p ∈ (T ⊓ K) ⊓ Q := ⟨hp, h1⟩
    rw [P_inf_Q h c] at h2
    exact hp1 (Subgroup.mem_bot.1 h2)

theorem invol_conj_x_or_v
    (hsimple : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hc : Case47 h c) (haa : a * a = 1) :
    ∀ t : G, t * t = 1 → t ≠ 1 → IsConj t x ∨ IsConj t (L4.vElt x a) := by
  have hRS : c.lift Rm ≤ S := R_le_S hc
  have haR : a * a ∈ c.lift Rm := by rw [haa]; exact one_mem _
  have haR' : a ∉ c.lift Rm := fun hh => h.a_mem.2.2.1 (Coord5.Rg_le_T (c := c) hh)
  rcases iv2_3_3 hsimple hnab h.sylowS hRS (fun s hs r hr => S_norm_R hc hs hr)
    (relIndex_R_S hc) (sq_mem_R_of_aa hc haR)
    (fun u hu huR huu t ht htu htt => hfree_S hc hu huR huu ht htu htt) with hA | ⟨-, -, hB⟩
  · intro t ht2 ht1
    obtain ⟨g, hg⟩ := hA t ht2 ht1
    have hrsq : g * t * g⁻¹ * (g * t * g⁻¹) = 1 := by
      calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
        _ = 1 := by rw [ht2]; group
    have hr1 : g * t * g⁻¹ ≠ 1 := by
      intro e
      apply ht1
      calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
        _ = 1 := by rw [e]; group
    have hconj : IsConj t (g * t * g⁻¹) := isConj_conj g t
    by_cases hm : Mixm (c.rco (g * t * g⁻¹))
    · right
      exact hconj.trans (isConj_v_of_Mixm hc (Coord5.Rg_le_T (c := c) hg) hm)
    · left
      exact hconj.trans (isConj_x_of_R_nonmixed hc hg hr1 hm)
  · exfalso
    obtain ⟨y, hyT, hyo, -, q, hq, hyq⟩ := h.fiveCase rfl
    have hy2 : y * y = 1 := by
      have := pow_orderOf_eq_one y
      rwa [hyo, pow_two] at this
    have hyR : y ∉ c.lift Rm := by
      intro hy
      exact hyq (R_comm_G c hy (Q_le_R h c hq))
    obtain ⟨n, hn, hny⟩ := hB (fun r hr => R_sq_G c hr) (fun r hr r' hr' => R_comm_G c hr hr')
      a h.a_mem.1 y (h.T_lt_S.le hyT) haR' hyR haa hy2
    have hxR : x ∈ c.lift Rm := Q_le_R h c h.x_mem_Q
    have hr0R : n⁻¹ * x * n ∈ c.lift Rm := by
      have := (mem_normalizer_iff.1 (inv_mem hn) x).1 hxR
      simpa using this
    have hyx : y * x = x * y := mem_centralizer_singleton_iff.1 (h.T_le_C hyT)
    have ha : a = n⁻¹ * y * n := by rw [← hny]; group
    have hcent : a * (n⁻¹ * x * n) * a⁻¹ = n⁻¹ * x * n := by
      have h1 : a * (n⁻¹ * x * n) * a⁻¹ = n⁻¹ * (y * x * y⁻¹) * n := by rw [ha]; group
      have h2 : y * x * y⁻¹ = x := by rw [hyx]; group
      rw [h1, h2]
    have hr01 : n⁻¹ * x * n ≠ 1 := by
      intro e
      apply h.x_ne_one
      calc x = n * (n⁻¹ * x * n) * n⁻¹ := by group
        _ = 1 := by rw [e]; group
    have hv := cent_swap_conj_v hc h.a_mem.1 h.a_mem.2.2.1 hr0R hr01 hcent
    have hxr : IsConj x (n⁻¹ * x * n) := isConj_iff.2 ⟨n⁻¹, by simp⟩
    exact x_not_conj_v hc (hxr.trans hv)

end CaseI

end CFSG.GH74.GLS.C3.Layer2.L5
