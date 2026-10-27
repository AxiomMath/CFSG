module

public import CFSG.GH74.GLS.C3.Layer2.L5B6
public import CFSG.GH74.GLS.C3.Layer2.L5B2
public import CFSG.GH74.GLS.C3.Layer2.ModelBridge

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Prop121
  CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

variable {G : Type} [Group G] [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}

section Coords

variable {h : IsAConfig 5 x K T Q S a} (c : Coord5 h)

theorem Coord5.rco_mem_T5 {t : G} (ht : t ∈ T) : c.rco t ∈ T5 :=
  Coord5.rco_mem c (by rw [Coord5.T_eq_lift (c := c)] at ht; exact ht)

theorem Coord5.exists_lift_rco {M : Subgroup (Amb 5)} (hM : M ≤ Fgrp 5) {m : Amb 5} (hm : m ∈ M) :
    ∃ g ∈ c.lift M, c.rco g = m := by
  obtain ⟨g, hg⟩ := c.co_surj (hM hm)
  have hgl : (g : G) ∈ c.lift M := (Coord5.mem_lift_iff g.2).2 (by
    show c.co g ∈ M
    rw [hg]; exact hm)
  exact ⟨g, hgl, by rw [Coord5.rco_of_mem c g.2]; exact hg⟩

theorem Coord5.exists_T_rco {m : Amb 5} (hm : m ∈ T5) : ∃ t ∈ T, c.rco t = m := by
  obtain ⟨g, hg, hgm⟩ := Coord5.exists_lift_rco c T5_le_Fgrp hm
  exact ⟨g, by rw [Coord5.T_eq_lift (c := c)]; exact hg, hgm⟩

theorem Coord5.rco_T_mul {t t' : G} (ht : t ∈ T) (ht' : t' ∈ T) :
    c.rco (t * t') = c.rco t * c.rco t' :=
  Coord5.rco_mul c (h.T_le_C ht) (h.T_le_C ht')

theorem Coord5.rco_T_inv {t : G} (ht : t ∈ T) : c.rco t⁻¹ = (c.rco t)⁻¹ :=
  Coord5.rco_inv c (h.T_le_C ht)

theorem Coord5.rco_T_inj {t t' : G} (ht : t ∈ T) (ht' : t' ∈ T) (hh : c.rco t = c.rco t') :
    t = t' := Coord5.rco_inj c (h.T_le_C ht) (h.T_le_C ht') hh

end Coords

open Classical in
@[expose] noncomputable def alphaG {h : IsAConfig 5 x K T Q S a} (c : Coord5 h) : Amb 5 → Amb 5 :=
  fun m => if hm : m ∈ T5 then c.rco (a * (c.exists_T_rco hm).choose * a⁻¹) else 1

theorem alphaG_rco {h : IsAConfig 5 x K T Q S a} (c : Coord5 h) {t : G} (ht : t ∈ T) :
    alphaG c (c.rco t) = c.rco (a * t * a⁻¹) := by
  have hm := c.rco_mem_T5 ht
  have hdef : alphaG c (c.rco t) = c.rco (a * (c.exists_T_rco hm).choose * a⁻¹) := by
    simp [alphaG, hm]
  rw [hdef]
  obtain ⟨hT', hr⟩ := (c.exists_T_rco hm).choose_spec
  rw [c.rco_T_inj hT' ht hr]

theorem a_conj_mem_T (h : IsAConfig 5 x K T Q S a) {t : G} (ht : t ∈ T) : a * t * a⁻¹ ∈ T :=
  (mem_normalizer_iff.1 h.a_mem.2.1 t).1 ht

theorem spair_of_config
    {h : IsAConfig 5 x K T Q S a} {c : Coord5 h} (hc : Case47 h c) :
    SPair (alphaG c) (c.rco (a * a)) where
  maps := by
    intro m hm
    obtain ⟨t, ht, rfl⟩ := c.exists_T_rco hm
    rw [alphaG_rco c ht]
    exact c.rco_mem_T5 (a_conj_mem_T h ht)
  mul := by
    intro m hm n hn
    obtain ⟨s, hs, rfl⟩ := c.exists_T_rco hm
    obtain ⟨t, ht, rfl⟩ := c.exists_T_rco hn
    rw [← c.rco_T_mul hs ht, alphaG_rco c (T.mul_mem hs ht), alphaG_rco c hs, alphaG_rco c ht,
      ← c.rco_T_mul (a_conj_mem_T h hs) (a_conj_mem_T h ht)]
    congr 1
    group
  surj := by
    intro m hm
    obtain ⟨t, ht, rfl⟩ := c.exists_T_rco hm
    refine ⟨c.rco (a⁻¹ * t * a), c.rco_mem_T5 (a_inv_conj_mem h ht), ?_⟩
    rw [alphaG_rco c (a_inv_conj_mem h ht)]
    congr 1
    group
  P_Q := by
    intro p hp
    obtain ⟨p₀, hp₀, rfl⟩ := Coord5.exists_lift_rco c Pm_le_Fgrp hp
    rw [← Coord5.P_eq_lift (c := c)] at hp₀
    have hpT : p₀ ∈ T := hp₀.1
    rw [alphaG_rco c hpT]
    have : a * p₀ * a⁻¹ ∈ c.lift Qm := by
      rw [← Coord5.Q_eq_lift (c := c), ← cj_a_P hc]
      exact mem_cj_self hp₀
    exact Coord5.rco_mem c this
  Q_P := by
    intro q hq
    obtain ⟨q₀, hq₀, rfl⟩ := Coord5.exists_lift_rco c Qm_le_Fgrp hq
    rw [← Coord5.Q_eq_lift (c := c)] at hq₀
    have hqT : q₀ ∈ T := h.Q_le_T hq₀
    rw [alphaG_rco c hqT]
    have : a * q₀ * a⁻¹ ∈ c.lift Pm := by
      rw [← Coord5.P_eq_lift (c := c), ← cj_a_Q hc]
      exact mem_cj_self hq₀
    exact Coord5.rco_mem c this
  u_mem := c.rco_mem_T5 (a_sq_mem h)
  sq := by
    intro m hm
    obtain ⟨t, ht, rfl⟩ := c.exists_T_rco hm
    rw [alphaG_rco c ht, alphaG_rco c (a_conj_mem_T h ht)]
    have haa := a_sq_mem h
    rw [← c.rco_T_inv haa, ← c.rco_T_mul haa ht, ← c.rco_T_mul (T.mul_mem haa ht) (T.inv_mem haa)]
    congr 1
    group
  fix := by
    rw [alphaG_rco c (a_sq_mem h)]
    congr 1
    group
  moves := by
    intro hf
    have hx : c.rco x = f1 := by
      rw [Coord5.rco_of_mem c (h.T_le_C h.x_mem_T)]
      exact Coord5.x_co (c := c)
    rw [← hx, alphaG_rco c h.x_mem_T] at hf
    exact h.a_conj_x_ne (c.rco_T_inj (a_conj_mem_T h h.x_mem_T) h.x_mem_T hf)

open Classical in
@[expose] noncomputable def psiFun {h : IsAConfig 5 x K T Q S a} (c : Coord5 h) (A : Perm (Fin 9))
    (s : G) : Perm (Fin 9) :=
  if s ∈ T then emb 5 (c.rco s) else emb 5 (c.rco (s * a⁻¹)) * A

theorem a_cosets
    {h : IsAConfig 5 x K T Q S a} {c : Coord5 h} (hc : Case47 h c) {s : G}
    (hs : s ∈ S) (hsT : s ∉ T) : s * a⁻¹ ∈ T := by
  have h2 := relIndex_T_S hc
  have := inv_mul_mem_of_relIndex_two h2 (S.inv_mem hs) (S.inv_mem h.a_mem.1)
    (fun hh => hsT (T.inv_mem_iff.1 hh)) (fun hh => h.a_mem.2.2.1 (T.inv_mem_iff.1 hh))
  simpa using this

theorem psiFun_T {h : IsAConfig 5 x K T Q S a} (c : Coord5 h) (A : Perm (Fin 9)) {t : G}
    (ht : t ∈ T) : psiFun c A t = emb 5 (c.rco t) := by
  simp [psiFun, ht]

theorem psiFun_nT {h : IsAConfig 5 x K T Q S a} (c : Coord5 h) (A : Perm (Fin 9)) {s : G}
    (hs : s ∉ T) : psiFun c A s = emb 5 (c.rco (s * a⁻¹)) * A := by
  simp [psiFun, hs]

theorem exists_psi
    {h : IsAConfig 5 x K T Q S a} {c : Coord5 h} (hc : Case47 h c)
    (haR : a * a ∈ c.lift Rm) :
    ∃ ψ : ↥S →* Perm (Fin 9), Function.Injective ψ ∧ (∀ s, ψ s ∈ S0) ∧
      (∀ p ∈ S0, ∃ s, ψ s = p) ∧
      (∀ (t : G) (ht : t ∈ T), ψ ⟨t, h.T_lt_S.le ht⟩ = emb 5 (c.rco t)) ∧
      (∀ (s : G) (hs : s ∈ S), s ∉ T → ∀ m ∈ T5, ψ ⟨s, hs⟩ ≠ emb 5 m) := by
  have hsp := spair_of_config hc
  have hu : c.rco (a * a) ∈ Rm := Coord5.rco_mem c haR
  obtain ⟨t₀, ht₀, hcl, hcu⟩ := classify_27_id hsp hu
  set A : Perm (Fin 9) := emb 5 t₀ * a0perm 5 with hA
  have hAinv : A⁻¹ = (a0perm 5)⁻¹ * (emb 5 t₀)⁻¹ := by rw [hA, mul_inv_rev]
  have hAconj : ∀ m ∈ T5, emb 5 (alphaG c m) = A * emb 5 m * A⁻¹ := by
    intro m hm
    rw [hcl m hm, hA, hAinv]
    group
  have hAsq : emb 5 (c.rco (a * a)) = A * A := by
    rw [hcu, hA]
    group
  have hT : T ≤ S := h.T_lt_S.le
  have hMul : ∀ s s' : G, s ∈ S → s' ∈ S →
      psiFun c A (s * s') = psiFun c A s * psiFun c A s' := by
    intro s s' hs hs'
    by_cases hsT : s ∈ T <;> by_cases hs'T : s' ∈ T
    · rw [psiFun_T c A hsT, psiFun_T c A hs'T, psiFun_T c A (T.mul_mem hsT hs'T),
        c.rco_T_mul hsT hs'T, map_mul]
    ·
      have hss' : s * s' ∉ T := fun hh => hs'T (by
        have := T.mul_mem (T.inv_mem hsT) hh
        simpa using this)
      have hs'a := a_cosets hc hs' hs'T
      rw [psiFun_T c A hsT, psiFun_nT c A hs'T, psiFun_nT c A hss']
      have e : s * s' * a⁻¹ = s * (s' * a⁻¹) := by group
      rw [e, c.rco_T_mul hsT hs'a, map_mul, mul_assoc]
    ·
      have hss' : s * s' ∉ T := fun hh => hsT (by
        have := T.mul_mem hh (T.inv_mem hs'T)
        simpa using this)
      have hsa := a_cosets hc hs hsT
      rw [psiFun_nT c A hsT, psiFun_T c A hs'T, psiFun_nT c A hss']
      have e : s * s' * a⁻¹ = (s * a⁻¹) * (a * s' * a⁻¹) := by group
      have hcj := a_conj_mem_T h hs'T
      rw [e, c.rco_T_mul hsa hcj, map_mul]
      have h1 : c.rco (a * s' * a⁻¹) = alphaG c (c.rco s') := (alphaG_rco c hs'T).symm
      have h2 := hAconj (c.rco s') (c.rco_mem_T5 hs'T)
      rw [h1, h2]
      group
    ·
      have hss' : s * s' ∈ T := by
        have h2 := relIndex_T_S hc
        have := inv_mul_mem_of_relIndex_two h2 (S.inv_mem hs) hs'
          (fun hh => hsT (T.inv_mem_iff.1 hh)) hs'T
        simpa using this
      have hsa := a_cosets hc hs hsT
      have hs'a := a_cosets hc hs' hs'T
      rw [psiFun_nT c A hsT, psiFun_nT c A hs'T, psiFun_T c A hss']
      have e : s * s' = (s * a⁻¹) * (a * (s' * a⁻¹) * a⁻¹) * (a * a) := by group
      have haa := a_sq_mem h
      have hcj := a_conj_mem_T h hs'a
      rw [e, c.rco_T_mul (T.mul_mem hsa hcj) haa, c.rco_T_mul hsa hcj, map_mul, map_mul]
      have h1 : c.rco (a * (s' * a⁻¹) * a⁻¹) = alphaG c (c.rco (s' * a⁻¹)) :=
        (alphaG_rco c hs'a).symm
      have h2 := hAconj (c.rco (s' * a⁻¹)) (c.rco_mem_T5 hs'a)
      rw [h1, h2, hAsq]
      group
  let ψ : ↥S →* Perm (Fin 9) :=
    { toFun := fun s => psiFun c A (s : G)
      map_one' := by
        rw [Subgroup.coe_one, psiFun_T c A T.one_mem, c.rco_one, map_one]
      map_mul' := fun s s' => by
        rw [Subgroup.coe_mul]
        exact hMul s s' s.2 s'.2 }
  have hpsiT : ∀ (t : G) (ht : t ∈ T), ψ ⟨t, hT ht⟩ = emb 5 (c.rco t) := fun t ht =>
    psiFun_T c A ht
  have hpsiN : ∀ (s : G) (hs : s ∈ S), s ∉ T →
      ψ ⟨s, hs⟩ = emb 5 (c.rco (s * a⁻¹)) * A := fun s hs hsT => psiFun_nT c A hsT
  have hAnot : ∀ m ∈ T5, ∀ m' ∈ T5, emb 5 m' * A ≠ emb 5 m := by
    intro m hm m' hm' hmm
    have : a0perm 5 = emb 5 (t₀⁻¹ * (m'⁻¹ * m)) := by
      rw [map_mul, map_mul, map_inv, map_inv, ← hmm, hA]
      group
    exact a0_notin_T5 _ (mem_allT5.2 (mul_mem (inv_mem ht₀) (mul_mem (inv_mem hm') hm)))
      this.symm
  have hmemS0 : ∀ m ∈ T5, emb 5 m ∈ S0 := fun m hm => R5_le_S0 (mem_R5.2 ⟨m, hm, rfl⟩)
  have hAS0 : A ∈ S0 := mul_mem (hmemS0 t₀ ht₀) a0_mem_S0
  refine ⟨ψ, ?_, ?_, ?_, hpsiT, ?_⟩
  ·
    intro s s' hss
    obtain ⟨s, hs⟩ := s
    obtain ⟨s', hs'⟩ := s'
    apply Subtype.ext
    show s = s'
    by_cases hsT : s ∈ T <;> by_cases hs'T : s' ∈ T
    · rw [hpsiT s hsT, hpsiT s' hs'T] at hss
      exact c.rco_T_inj hsT hs'T (emb_injective 5 hss)
    · rw [hpsiT s hsT, hpsiN s' hs' hs'T] at hss
      exact absurd hss.symm (hAnot _ (c.rco_mem_T5 hsT) _ (c.rco_mem_T5 (a_cosets hc hs' hs'T)))
    · rw [hpsiN s hs hsT, hpsiT s' hs'T] at hss
      exact absurd hss (hAnot _ (c.rco_mem_T5 hs'T) _ (c.rco_mem_T5 (a_cosets hc hs hsT)))
    · rw [hpsiN s hs hsT, hpsiN s' hs' hs'T] at hss
      have h1 := mul_right_cancel hss
      have h2 := c.rco_T_inj (a_cosets hc hs hsT) (a_cosets hc hs' hs'T) (emb_injective 5 h1)
      exact mul_right_cancel h2
  · intro s
    obtain ⟨s, hs⟩ := s
    by_cases hsT : s ∈ T
    · rw [hpsiT s hsT]
      exact hmemS0 _ (c.rco_mem_T5 hsT)
    · rw [hpsiN s hs hsT]
      exact mul_mem (hmemS0 _ (c.rco_mem_T5 (a_cosets hc hs hsT))) hAS0
  · intro p hp
    rcases mem_S0.1 hp with hpR | hpR
    · obtain ⟨m, hm, rfl⟩ := mem_R5.1 hpR
      obtain ⟨t, ht, hrt⟩ := c.exists_T_rco hm
      exact ⟨⟨t, hT ht⟩, by rw [hpsiT t ht, hrt]⟩
    · obtain ⟨m, hm, hmp⟩ := mem_R5.1 hpR
      have hpe : p = emb 5 (m * t₀⁻¹) * A := by
        rw [map_mul, map_inv, hA]
        calc p = p * a0perm 5 * a0perm 5 := by rw [mul_assoc, a0_sq, mul_one]
          _ = emb 5 m * a0perm 5 := by rw [← hmp]
          _ = emb 5 m * (emb 5 t₀)⁻¹ * (emb 5 t₀ * a0perm 5) := by group
      obtain ⟨t, ht, hrt⟩ := c.exists_T_rco (mul_mem hm (inv_mem ht₀))
      have hta : t * a ∈ S := S.mul_mem (hT ht) h.a_mem.1
      have htaT : t * a ∉ T := fun hh => h.a_mem.2.2.1 (by
        have := T.mul_mem (T.inv_mem ht) hh
        simpa using this)
      refine ⟨⟨t * a, hta⟩, ?_⟩
      rw [hpsiN _ hta htaT, hpe]
      have e : t * a * a⁻¹ = t := by group
      rw [e, hrt]
  · intro s hs hsT m hm hmm
    rw [hpsiN s hs hsT] at hmm
    exact hAnot m hm _ (c.rco_mem_T5 (a_cosets hc hs hsT)) hmm

end CFSG.GH74.GLS.C3.Layer2.L5
