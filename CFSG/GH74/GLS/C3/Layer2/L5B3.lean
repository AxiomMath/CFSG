module

public import CFSG.GH74.GLS.C3.Layer2.L5B1
public import CFSG.GH74.GLS.C3.Layer2.L4Setup

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Prop121
  CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

variable {G : Type} [Group G] [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}

theorem x_conj_mem_P
    {h : IsAConfig 5 x K T Q S a} {c : Coord5 h} (hc : Case47 h c) :
    a * x * a⁻¹ ∈ T ⊓ K := by
  rw [← cj_a_Q hc]
  exact mem_cj_self h.x_mem_Q

theorem conj_x_ne_one (h : IsAConfig 5 x K T Q S a) : a * x * a⁻¹ ≠ 1 := by
  intro h1
  apply h.x_ne_one
  have : x = a⁻¹ * (a * x * a⁻¹) * a := by group
  rw [this, h1]
  group

theorem zpowers_w_comm_Q
    {h : IsAConfig 5 x K T Q S a} {c : Coord5 h} {g : G}
    (hg : g ∈ zpowers (c.wC : G)) {q : G} (hq : q ∈ Q) : g * q = q * g := by
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hg
  have hq' : q ∈ c.lift Qm := (SetLike.ext_iff.1 (Coord5.Q_eq_lift (c := c)) q).1 hq
  have hcomm : Commute (c.wC : G) q := Coord5.wG_cent_Q hq'
  exact (hcomm.zpow_left n).eq

theorem cyc_P
    {h : IsAConfig 5 x K T Q S a} (c : Coord5 h) {p p' : G} (hp : p ∈ T ⊓ K)
    (hp1 : p ≠ 1) (hp' : p' ∈ T ⊓ K) (hp'1 : p' ≠ 1) :
    ∃ g ∈ zpowers (c.wC : G), g * p * g⁻¹ = p' := by
  have hpl : p ∈ c.lift Pm := (SetLike.ext_iff.1 (Coord5.P_eq_lift (c := c)) p).1 hp
  have hpl' : p' ∈ c.lift Pm := (SetLike.ext_iff.1 (Coord5.P_eq_lift (c := c)) p').1 hp'
  have hpC := Coord5.lift_mem_cent hpl
  have hpC' := Coord5.lift_mem_cent hpl'
  have hw : (c.wC : G) ∈ centralizer ({x} : Set G) := c.wC.2
  have hwp : (c.wC : G) * p * (c.wC : G)⁻¹ ∈ centralizer ({x} : Set G) :=
    mul_mem (mul_mem hw hpC) (inv_mem hw)
  have hm := wm_cycles_P (Coord5.rco_mem c hpl) (rco_ne_one c hpC hp1) (Coord5.rco_mem c hpl')
    (rco_ne_one c hpC' hp'1)
  rcases hm with h1 | h1 | h1
  · exact ⟨1, one_mem _, by rw [Coord5.rco_inj c hpC' hpC h1]; group⟩
  · refine ⟨c.wC, mem_zpowers _, ?_⟩
    rw [← Coord5.rco_conj_w c hpC] at h1
    exact (Coord5.rco_inj c hpC' hwp h1).symm
  · refine ⟨(c.wC : G) * c.wC, mul_mem (mem_zpowers _) (mem_zpowers _), ?_⟩
    have h2 : c.rco ((c.wC : G) * ((c.wC : G) * p * (c.wC : G)⁻¹) * (c.wC : G)⁻¹) =
        wm * (wm * c.rco p * wm⁻¹) * wm⁻¹ := by
      rw [Coord5.rco_conj_w c hwp, Coord5.rco_conj_w c hpC]
    have hww : (c.wC : G) * ((c.wC : G) * p * (c.wC : G)⁻¹) * (c.wC : G)⁻¹ ∈
        centralizer ({x} : Set G) := mul_mem (mul_mem hw hwp) (inv_mem hw)
    rw [← h2] at h1
    have h3 := (Coord5.rco_inj c hpC' hww h1).symm
    calc ((c.wC : G) * c.wC) * p * ((c.wC : G) * c.wC)⁻¹ =
        (c.wC : G) * ((c.wC : G) * p * (c.wC : G)⁻¹) * (c.wC : G)⁻¹ := by group
      _ = p' := h3

theorem zpowers_w'_comm_P
    {h : IsAConfig 5 x K T Q S a} {c : Coord5 h} (hc : Case47 h c) {g : G}
    (hg : g ∈ zpowers (a * (c.wC : G) * a⁻¹)) {p : G} (hp : p ∈ T ⊓ K) : g * p = p * g := by
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hg
  have hp' : p ∈ cj a Q := by rw [cj_a_Q hc]; exact hp
  obtain ⟨q, hq, rfl⟩ := mem_cj.1 hp'
  have hcomm : Commute (c.wC : G) q := by
    have hq' : q ∈ c.lift Qm := (SetLike.ext_iff.1 (Coord5.Q_eq_lift (c := c)) q).1 hq
    exact Coord5.wG_cent_Q hq'
  have h1 : Commute (a * (c.wC : G) * a⁻¹) (a * q * a⁻¹) := by
    show a * (c.wC : G) * a⁻¹ * (a * q * a⁻¹) = a * q * a⁻¹ * (a * (c.wC : G) * a⁻¹)
    calc a * (c.wC : G) * a⁻¹ * (a * q * a⁻¹) = a * ((c.wC : G) * q) * a⁻¹ := by group
      _ = a * (q * (c.wC : G)) * a⁻¹ := by rw [hcomm.eq]
      _ = a * q * a⁻¹ * (a * (c.wC : G) * a⁻¹) := by group
  exact (h1.zpow_left n).eq

theorem cyc_Q
    {h : IsAConfig 5 x K T Q S a} {c : Coord5 h} (hc : Case47 h c) {q q' : G}
    (hq : q ∈ Q) (hq1 : q ≠ 1) (hq' : q' ∈ Q) (hq'1 : q' ≠ 1) :
    ∃ g ∈ zpowers (a * (c.wC : G) * a⁻¹), g * q * g⁻¹ = q' := by
  have hmq : q ∈ cj a (T ⊓ K) := by rw [cj_a_P hc]; exact hq
  have hmq' : q' ∈ cj a (T ⊓ K) := by rw [cj_a_P hc]; exact hq'
  obtain ⟨p, hp, rfl⟩ := mem_cj.1 hmq
  obtain ⟨p', hp', rfl⟩ := mem_cj.1 hmq'
  have hp1 : p ≠ 1 := fun h1 => hq1 (by rw [h1]; group)
  have hp'1 : p' ≠ 1 := fun h1 => hq'1 (by rw [h1]; group)
  obtain ⟨g₀, hg₀, hgg⟩ := cyc_P c hp hp1 hp' hp'1
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hg₀
  refine ⟨(a * (c.wC : G) * a⁻¹) ^ n, mem_zpowers_iff.2 ⟨n, rfl⟩, ?_⟩
  have e : (a * (c.wC : G) * a⁻¹) ^ n = a * (c.wC : G) ^ n * a⁻¹ := by
    have := map_zpow (MulAut.conj a) (c.wC : G) n
    simp
  rw [e]
  calc a * (c.wC : G) ^ n * a⁻¹ * (a * p * a⁻¹) * (a * (c.wC : G) ^ n * a⁻¹)⁻¹
      = a * ((c.wC : G) ^ n * p * ((c.wC : G) ^ n)⁻¹) * a⁻¹ := by group
    _ = a * p' * a⁻¹ := by rw [hgg]

theorem isConj_x_of_PQ
    {h : IsAConfig 5 x K T Q S a} {c : Coord5 h} (hc : Case47 h c) {r : G}
    (hr : r ∈ T ⊓ K ∨ r ∈ Q) (hr1 : r ≠ 1) : IsConj r x := by
  rcases hr with hrP | hrQ
  · have hmr : r ∈ cj a Q := by rw [cj_a_Q hc]; exact hrP
    obtain ⟨q, hq, rfl⟩ := mem_cj.1 hmr
    have hq1 : q ≠ 1 := fun h1 => hr1 (by rw [h1]; group)
    obtain ⟨g, -, hg⟩ := cyc_Q hc hq hq1 h.x_mem_Q h.x_ne_one
    refine isConj_iff.2 ⟨g * a⁻¹, ?_⟩
    calc g * a⁻¹ * (a * q * a⁻¹) * (g * a⁻¹)⁻¹ = g * q * g⁻¹ := by group
      _ = x := hg
  · obtain ⟨g, -, hg⟩ := cyc_Q hc hrQ hr1 h.x_mem_Q h.x_ne_one
    exact isConj_iff.2 ⟨g, hg⟩

theorem isConj_v_of_mixed
    {h : IsAConfig 5 x K T Q S a} {c : Coord5 h} (hc : Case47 h c) {r : G}
    (hrR : r ∈ c.lift Rm) (hrP : r ∉ T ⊓ K) (hrQ : r ∉ Q) : IsConj r (L4.vElt x a) := by
  obtain ⟨p, hp, q, hq, rfl⟩ := R_prod_G c hrR
  have hp1 : p ≠ 1 := fun h1 => hrQ (by rw [h1, one_mul]; exact hq)
  have hq1 : q ≠ 1 := fun h1 => hrP (by rw [h1, mul_one]; exact hp)
  have hxa : a * x * a⁻¹ ∈ T ⊓ K := x_conj_mem_P hc
  obtain ⟨g₁, hg₁, hg₁p⟩ := cyc_P c hxa (conj_x_ne_one h) hp hp1
  obtain ⟨g₂, hg₂, hg₂q⟩ := cyc_Q hc h.x_mem_Q h.x_ne_one hq hq1
  have h1 : g₁ * q * g₁⁻¹ = q := by
    rw [zpowers_w_comm_Q hg₁ hq, mul_inv_cancel_right]
  have h2 : g₂ * (a * x * a⁻¹) * g₂⁻¹ = a * x * a⁻¹ := by
    rw [zpowers_w'_comm_P hc hg₂ hxa, mul_inv_cancel_right]
  have hcomm : p * q = q * p := PQ_comm_G h c p hp q hq
  have hv : (g₁ * g₂) * L4.vElt x a * (g₁ * g₂)⁻¹ = p * q := by
    show (g₁ * g₂) * (x * (a * x * a⁻¹)) * (g₁ * g₂)⁻¹ = p * q
    calc (g₁ * g₂) * (x * (a * x * a⁻¹)) * (g₁ * g₂)⁻¹
        = g₁ * ((g₂ * x * g₂⁻¹) * (g₂ * (a * x * a⁻¹) * g₂⁻¹)) * g₁⁻¹ := by group
      _ = g₁ * (q * (a * x * a⁻¹)) * g₁⁻¹ := by rw [hg₂q, h2]
      _ = (g₁ * q * g₁⁻¹) * (g₁ * (a * x * a⁻¹) * g₁⁻¹) := by group
      _ = q * p := by rw [h1, hg₁p]
      _ = p * q := hcomm.symm
  exact (isConj_iff.2 ⟨g₁ * g₂, hv⟩).symm

end CFSG.GH74.GLS.C3.Layer2.L5
