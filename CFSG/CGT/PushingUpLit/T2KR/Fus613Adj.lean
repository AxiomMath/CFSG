module

public import CFSG.CGT.PushingUpLit.T2KR.Fus613N0

public section

namespace CFSG.CGT.PushingUpLit.T2KR.P613

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.CGT.PushingUpLit.BHS
  CFSG.CGT.PushingUpLit.T2K CFSG.CGT.Timmesfeld75
open scoped commutatorElement
open MData (QM)

variable {G : Type} [Group G] [Finite G] {L M : Subgroup G} {n : ℕ}
  {H : MData G L M n} {T' : Subgroup G} {x r b : G} {e₁ e₂ : Fin 2 → Fq n} {ω : Fq n}

theorem det_ne_zero_of_span (bs : Basis H r b e₁ e₂ ω) : e₁ 0 * e₂ 1 - e₂ 0 * e₁ 1 ≠ 0 := by
  intro h
  obtain ⟨α₁, β₁, h1⟩ := bs.span ![1, 0]
  obtain ⟨α₂, β₂, h2⟩ := bs.span ![0, 1]
  have a1 := congrFun h1 0
  have a2 := congrFun h1 1
  have a3 := congrFun h2 0
  have a4 := congrFun h2 1
  simp at a1 a2 a3 a4
  have : (1 : Fq n) = 0 := by
    linear_combination (α₁ * β₂ - α₂ * β₁) * h - (α₁ * e₁ 1 + β₁ * e₂ 1) * a3 + a4 +
      (α₂ * e₁ 1 + β₂ * e₂ 1) * a1
  exact one_ne_zero this

theorem exists_torus_elt (bs : Basis H r b e₁ e₂ ω) {lam : Fq n} (hlam : lam ≠ 0) :
    ∃ h ∈ L, H.act h e₁ = lam • e₁ ∧ H.act h e₂ = lam⁻¹ • e₂ := by
  obtain ⟨g, hg1, hg2⟩ := exists_torus_matrix e₁ e₂ (det_ne_zero_of_span bs) hlam
  obtain ⟨l, hl⟩ := H.D.φ_surj g
  refine ⟨l, l.2, ?_, ?_⟩
  · rw [H.act_L l.2]
    have : (⟨(l : G), l.2⟩ : ↥L) = l := rfl
    rw [this, hl]
    exact hg1
  · rw [H.act_L l.2]
    have : (⟨(l : G), l.2⟩ : ↥L) = l := rfl
    rw [this, hl]
    exact hg2

section U

variable (c : Cfg H T' x r b) (bs : Basis H r b e₁ e₂ ω)

include c bs in
theorem Cfg.inv_mul_mem_blockU {a a' : G} {s : Fq n} (ha : a ∈ L) (ha' : a' ∈ L)
    (h : IsTv H e₁ e₂ a s) (h' : IsTv H e₁ e₂ a' s) : a⁻¹ * a' ∈ blockU L := by
  have hy : a⁻¹ * a' ∈ L := L.mul_mem (L.inv_mem ha) ha'
  have hyM : a⁻¹ * a' ∈ M := H.le hy
  have haM : a ∈ M := H.le ha
  have hact : ∀ w, H.act (a⁻¹ * a') w = w := by
    intro w
    obtain ⟨α, β, rfl⟩ := bs.span w
    have e1 : H.act a' (α • e₁ + β • e₂) = H.act a (α • e₁ + β • e₂) := by
      rw [h'.act_coord ha', h.act_coord ha]
    rw [H.act_mul (H.le ha'), e1, H.act_inv_act haM]
  rw [← c.hO]
  refine NatData.mem_oTwoIn_of_centralizes H.D hy fun v hv => ?_
  have h1 := H.conj_vec hyM (H.D.ψe v)
  rw [H.vec_ψe hv, hact] at h1
  rw [h1, H.vec_ψe hv]

include c bs in
theorem Cfg.mem_T'_of_isTv {u : G} {s : Fq n} (huL : u ∈ L) (hu : IsTv H e₁ e₂ u s) : u ∈ T' := by
  obtain ⟨m, hm, hms⟩ := c.exists_mem_N0_isTv bs s
  have hy := c.inv_mul_mem_blockU bs hm.2 huL hms hu
  have : u = m * (m⁻¹ * u) := by group
  rw [this]
  exact T'.mul_mem hm.1 (c.blockU_le_N0 hy).1

include c bs in
theorem Cfg.exists_u₀ : ∃ u₀ : G, u₀ ∈ L ∧ u₀ ∈ T' ∧ u₀ * u₀ = 1 ∧ r * u₀ = u₀ * r ∧
    IsTv H e₁ e₂ u₀ ω := by
  have hω := bs.ω_eq
  have hlam : (ω ^ 2) ^ 2 + ω ^ 2 + 1 = 0 := by
    linear_combination hω + ω * root_cube hω
  have hlam0 : ω ^ 2 ≠ 0 := pow_ne_zero 2 (root_ne_zero hω)
  obtain ⟨h, hhL, hh1, hh2⟩ := exists_torus_elt bs hlam0
  have hrtv : IsTv H e₁ e₂ r 1 := ⟨bs.r1, by rw [one_smul]; exact bs.r2⟩
  have hhM : h ∈ M := H.le hhL
  have hu₀L : h * r * h⁻¹ ∈ L := L.mul_mem (L.mul_mem hhL c.r_L) (L.inv_mem hhL)
  have hu₀tv : IsTv H e₁ e₂ (h * r * h⁻¹) ω := by
    have := hrtv.conj_torus c.r_L hhL hlam0 hh1 hh2
    have e : (ω ^ 2) ^ 2 * 1 = ω := by linear_combination ω * root_cube hω
    rwa [e] at this
  refine ⟨h * r * h⁻¹, hu₀L, c.mem_T'_of_isTv bs hu₀L hu₀tv, ?_, ?_, hu₀tv⟩
  · calc h * r * h⁻¹ * (h * r * h⁻¹) = h * (r * r) * h⁻¹ := by group
      _ = 1 := by rw [c.r_sq]; group
  · exact e13_core bs.span bs.e₁_ne hlam c.r_L c.r_sq hrtv hhL hh1 hh2 c.hO

include c bs in
theorem Cfg.isTv_conj_b {a : G} {s : Fq n} (haL : a ∈ L) (ha : IsTv H e₁ e₂ a s) :
    IsTv H e₁ e₂ (b * a * b⁻¹) (s ^ 2) := by
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right c.b_sq
  have hMa : a ∈ M := H.le haL
  refine ⟨?_, ?_⟩
  · rw [H.act_conj hMa c.b_M, hbinv, bs.b1, ha.fix, bs.b1]
  · rw [H.act_conj hMa c.b_M, hbinv, bs.b2, ha.shift, H.act_add c.b_M, bs.b_semi, bs.b2, bs.b1]

include c bs in
theorem Cfg.exists_u : ∃ u : G, u ∈ L ∧ u ∈ T' ∧ u * u = 1 ∧ r * u = u * r ∧
    IsTv H e₁ e₂ u ω ∧ b * u * b⁻¹ = r * u := by
  obtain ⟨u₀, hu₀L, hu₀T, hu₀2, hru₀, hu₀tv⟩ := c.exists_u₀ bs
  have hω := bs.ω_eq
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right c.b_sq
  have hrM : r ∈ M := H.le c.r_L
  have hu₀M : u₀ ∈ M := H.le hu₀L
  have hrtv : IsTv H e₁ e₂ r 1 := ⟨bs.r1, by rw [one_smul]; exact bs.r2⟩
  set X := b * u₀ * b⁻¹ with hXdef
  have hXtv : IsTv H e₁ e₂ X (ω ^ 2) := c.isTv_conj_b bs hu₀L hu₀tv
  have hXL : X ∈ L := (Subgroup.mem_normalizer_iff.1 (H.normal c.b_M) u₀).1 hu₀L
  have hrutv : IsTv H e₁ e₂ (r * u₀) (ω ^ 2) := by
    have := hrtv.mul hu₀tv c.r_L hu₀M
    rwa [show (1 : Fq n) + ω = ω ^ 2 by linear_combination -(root_sq hω)] at this
  set v := (r * u₀)⁻¹ * X with hv
  have hvV : v ∈ blockU L := c.inv_mul_mem_blockU bs (L.mul_mem c.r_L hu₀L) hXL hrutv hXtv
  have hXv : X = r * u₀ * v := by rw [hv]; group
  have hrbinv : r * b⁻¹ = b⁻¹ * r := by rw [hbinv]; exact c.rb
  have hrX : r * X = X * r := by
    calc r * (b * u₀ * b⁻¹) = (r * b) * u₀ * b⁻¹ := by group
      _ = (b * r) * u₀ * b⁻¹ := by rw [c.rb]
      _ = b * (r * u₀) * b⁻¹ := by group
      _ = b * (u₀ * r) * b⁻¹ := by rw [hru₀]
      _ = b * u₀ * (r * b⁻¹) := by group
      _ = b * u₀ * (b⁻¹ * r) := by rw [hrbinv]
      _ = X * r := by rw [hXdef]; group
  have hbr : b * r * b⁻¹ = r := by
    calc b * r * b⁻¹ = r * b * b⁻¹ := by rw [← c.rb]
      _ = r := by group
  have hr_v : r * v * r⁻¹ = v := by
    have e1 : r * (r * u₀ * v) * r⁻¹ = r * u₀ * (r * v * r⁻¹) := by
      calc r * (r * u₀ * v) * r⁻¹ = r * (r * u₀) * v * r⁻¹ := by group
        _ = r * (u₀ * r) * v * r⁻¹ := by rw [hru₀]
        _ = r * u₀ * (r * v * r⁻¹) := by group
    have e2 : r * (r * u₀ * v) * r⁻¹ = r * u₀ * v := by
      have h := hrX
      rw [hXv] at h
      calc r * (r * u₀ * v) * r⁻¹ = ((r * u₀ * v) * r) * r⁻¹ := by rw [h]
        _ = r * u₀ * v := by group
    exact mul_left_cancel (e1.symm.trans e2)
  have hb_v : v * (b * v * b⁻¹) = 1 := by
    have e1 : b * X * b⁻¹ = u₀ := by
      calc b * (b * u₀ * b⁻¹) * b⁻¹ = (b * b) * u₀ * (b⁻¹ * b⁻¹) := by group
        _ = u₀ := by
          rw [c.b_sq, hbinv, c.b_sq]
          group
    have e2 : b * X * b⁻¹ = u₀ * v * (b * v * b⁻¹) := by
      calc b * X * b⁻¹ = b * (r * u₀ * v) * b⁻¹ := by rw [← hXv]
        _ = (b * r * b⁻¹) * (b * u₀ * b⁻¹) * (b * v * b⁻¹) := by group
        _ = r * X * (b * v * b⁻¹) := by rw [hbr]
        _ = r * (r * u₀ * v) * (b * v * b⁻¹) := by rw [← hXv]
        _ = u₀ * v * (b * v * b⁻¹) := by
          calc r * (r * u₀ * v) * (b * v * b⁻¹) = (r * r) * u₀ * v * (b * v * b⁻¹) := by group
            _ = u₀ * v * (b * v * b⁻¹) := by rw [c.r_sq, one_mul]
    have e3 : u₀ * (v * (b * v * b⁻¹)) = u₀ * 1 := by
      calc u₀ * (v * (b * v * b⁻¹)) = u₀ * v * (b * v * b⁻¹) := by group
        _ = u₀ := by rw [← e2, e1]
        _ = u₀ * 1 := by rw [mul_one]
    exact mul_left_cancel e3
  have h2 : (2 : Fq n) = 0 := two_eq_zero
  have h3 : ∀ y : Fin 2 → Fq n, (2 : Fq n) • y = 0 := fun y => by rw [h2, zero_smul]
  obtain ⟨α', β', hw⟩ := bs.span (H.D.ψe v)
  have hvvec : v = H.vec (α' • e₁ + β' • e₂) := by rw [← hw, H.vec_ψe hvV]
  have hrw : H.act r (α' • e₁ + β' • e₂) = α' • e₁ + β' • e₂ := by
    have h1 := H.conj_vec hrM (α' • e₁ + β' • e₂)
    rw [hvvec] at hr_v
    exact H.vec_injective (h1.symm.trans hr_v)
  have hβ0 : β' = 0 := by
    rw [hrtv.act_coord c.r_L] at hrw
    have : β' • e₁ = 0 := by
      linear_combination (norm := module) hrw
    exact (smul_eq_zero.1 this).resolve_right bs.e₁_ne
  have hvvec' : v = H.vec (α' • e₁) := by rw [hvvec, hβ0, zero_smul, add_zero]
  have hα : α' + α' ^ 2 = 0 := by
    have h1 := H.conj_vec c.b_M (α' • e₁)
    rw [hvvec'] at hb_v
    rw [h1, ← H.vec_add] at hb_v
    have := H.vec_injective (hb_v.trans H.vec_zero.symm)
    have e2 : H.act b (α' • e₁) = α' ^ 2 • e₁ := by rw [bs.b_semi, bs.b1]
    rw [e2] at this
    have h4 : (α' + α' ^ 2) • e₁ = 0 := by
      linear_combination (norm := module) this
    exact (smul_eq_zero.1 h4).resolve_right bs.e₁_ne
  obtain ⟨a', ha'⟩ : ∃ a' : Fq n, a' + a' ^ 2 = α' := by
    have : α' * (1 + α') = 0 := by linear_combination hα
    rcases mul_eq_zero.1 this with h | h
    · exact ⟨0, by rw [h]; simp⟩
    · refine ⟨ω, ?_⟩
      have : α' = 1 := by linear_combination h - h2
      rw [this]
      linear_combination hω - h2
  set z : G := H.vec (a' • e₁) with hz
  have hzV : z ∈ blockU L := H.vec_mem _
  have hzL : z ∈ L := blockU_le L hzV
  have hzM : z ∈ M := H.le hzL
  have hzu : u₀ * z = z * u₀ := by
    have h1 := H.conj_vec hu₀M (a' • e₁)
    rw [H.act_smul_L hu₀L, hu₀tv.fix] at h1
    have : u₀ * z * u₀⁻¹ = z := h1
    calc u₀ * z = (u₀ * z * u₀⁻¹) * u₀ := by group
      _ = z * u₀ := by rw [this]
  have hzr : r * z = z * r := by
    have h1 := H.conj_vec hrM (a' • e₁)
    rw [H.act_smul_L c.r_L, bs.r1] at h1
    have : r * z * r⁻¹ = z := h1
    calc r * z = (r * z * r⁻¹) * r := by group
      _ = z * r := by rw [this]
  have hzz : z * z = 1 := by
    rw [hz, ← H.vec_add, ← H.vec_zero]
    congr 1
    linear_combination (norm := module) h3 (a' • e₁)
  refine ⟨u₀ * z, L.mul_mem hu₀L hzL, T'.mul_mem hu₀T (c.blockU_le_N0 hzV).1, ?_, ?_, ?_, ?_⟩
  · calc u₀ * z * (u₀ * z) = u₀ * (z * u₀) * z := by group
      _ = u₀ * (u₀ * z) * z := by rw [hzu]
      _ = (u₀ * u₀) * (z * z) := by group
      _ = 1 := by rw [hu₀2, hzz, one_mul]
  · calc r * (u₀ * z) = (r * u₀) * z := by group
      _ = (u₀ * r) * z := by rw [hru₀]
      _ = u₀ * (r * z) := by group
      _ = u₀ * (z * r) := by rw [hzr]
      _ = u₀ * z * r := by group
  · refine ⟨?_, ?_⟩
    · rw [H.act_mul hzM, MData.act_blockU H hzV, hu₀tv.fix]
    · rw [H.act_mul hzM, MData.act_blockU H hzV, hu₀tv.shift]
  · have e1 : b * (u₀ * z) * b⁻¹ = (b * u₀ * b⁻¹) * (b * z * b⁻¹) := by group
    have e2 : b * z * b⁻¹ = H.vec (a' ^ 2 • e₁) := by
      rw [hz, H.conj_vec c.b_M, bs.b_semi, bs.b1]
    have e3 : v * H.vec (a' ^ 2 • e₁) = z := by
      rw [hvvec', hz, ← H.vec_add]
      congr 1
      have : α' + a' ^ 2 = a' := by linear_combination (-1 : Fq n) * ha' + a' ^ 2 * h2
      rw [← add_smul, this]
    rw [e1, e2, show b * u₀ * b⁻¹ = r * u₀ * v from hXv]
    calc r * u₀ * v * H.vec (a' ^ 2 • e₁) = r * u₀ * (v * H.vec (a' ^ 2 • e₁)) := by group
      _ = r * u₀ * z := by rw [e3]
      _ = r * (u₀ * z) := by group

end U

end CFSG.CGT.PushingUpLit.T2KR.P613
