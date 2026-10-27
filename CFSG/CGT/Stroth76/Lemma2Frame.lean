module

public import CFSG.CGT.Stroth76.Lemma7Two

public section

open scoped commutatorElement

namespace CFSG.CGT.Stroth76

open CFSG.CGT.Stroth77.Arch76

@[expose] def cmA (d : Dc) (e : Co) : Co := e - dact (dinv d) e

theorem frameA_dact_dinv_zero : ∀ e : Co, dact (dinv 0) e = e := by decide +kernel

theorem frameA_z3_gens : ∀ e ∈ ([(1, 0, 0), (0, 1, 1), (0, 0, 2)] : List Co),
    ∀ d₁ d₂ d₃ : Dc, cmA d₃ (cmA d₂ (cmA d₁ e)) = 0 := by
  decide +kernel

theorem frameA_fix_z3_gens : ∀ d : Dc, dact (dinv d) (1, 0, 0) = (1, 0, 0) →
    dact (dinv d) (0, 1, 1) = (0, 1, 1) → dact (dinv d) (0, 0, 2) = (0, 0, 2) → d = 0 := by
  decide +kernel

theorem frameA_z2_sq : ∀ (v : Co) (d₁ d₂ : Dc), cmA d₂ (cmA d₁ (v + v)) = 0 := by decide +kernel

theorem frameA_not_z2_csq : ∀ v : Co, ∃ d₁ d₂ : Dc, cmA d₂ (cmA d₁ ((1, 0, 0) + (v + v))) ≠ 0 := by
  decide +kernel

@[expose] def sig4 (p : Tc) : Tc :=
  subst ((1, 0, 0), 0) ((0, 1, 0), 0) ((0, 0, 1), 0) ((0, 1, 3), (1, 0, 0)) ((0, 1, 2), (0, 1, 0))
    ((1, 0, 0), (0, 0, 1)) p

theorem frameA_z3_fact3 : ∀ d : Dc, d ≠ 0 →
    (∃ (e : Co) (d₂ d₃ : Dc), cmA d₃ (cmA d₂ (dact (dinv d) e - e)) ≠ 0) ∨
      ((tmul (sig3 (0, d)) (0, dinv d)).2 = 0 ∧
        ∃ d₂ d₃ : Dc, cmA d₃ (cmA d₂ (tmul (sig3 (0, d)) (0, dinv d)).1) ≠ 0) := by
  decide +kernel

theorem frameA_z3_fact4 : ∀ d : Dc, d ≠ 0 →
    (∃ (e : Co) (d₂ d₃ : Dc), cmA d₃ (cmA d₂ (dact (dinv d) e - e)) ≠ 0) ∨
      ((tmul (sig4 (0, d)) (0, dinv d)).2 = 0 ∧
        ∃ d₂ d₃ : Dc, cmA d₃ (cmA d₂ (tmul (sig4 (0, d)) (0, dinv d)).1) ≠ 0) := by
  decide +kernel

section Comm

variable {X : Type*} [Group X] {K : Config X}

theorem conj_mul_mul_of_commute {a b q e f : X} (hq : q * e * q⁻¹ = f) (hb : b * f = f * b)
    (ha : a * f = f * a) : (a * (b * q)) * e * (a * (b * q))⁻¹ = f := by
  calc (a * (b * q)) * e * (a * (b * q))⁻¹ = a * (b * (q * e * q⁻¹) * b⁻¹) * a⁻¹ := by group
    _ = f := by rw [hq, hb, mul_inv_cancel_right, ha, mul_inv_cancel_right]

theorem dElt_mul_ev_mul_inv (d : Dc) (e : Co) :
    dElt K d * K.ev e * (dElt K d)⁻¹ = K.ev (dact (dinv d) e) := by
  rw [dElt_mul_ev, mul_inv_cancel_right]

theorem comm_ev_eq_cmA {q : X} {d : Dc}
    (h : ∀ e, q * K.ev e * q⁻¹ = K.ev (dact (dinv d) e)) (e : Co) :
    ⁅K.ev e, q⁆ = K.ev (cmA d e) := by
  rw [commutatorElement_def, cmA, K.ev_sub, ← h]
  group

theorem comm_ev_right_eq {q : X} {d : Dc}
    (h : ∀ e, q * K.ev e * q⁻¹ = K.ev (dact (dinv d) e)) (e : Co) :
    ⁅q, K.ev e⁆ = K.ev (dact (dinv d) e - e) := by
  rw [commutatorElement_def, h, K.ev_sub]

variable (D : IdxTwo K) (hcom : ∀ v, D.s * K.ev v = K.ev v * D.s)

theorem idxTwo_ev_mem (v : Co) : K.ev v ∈ D.Ssub :=
  Subgroup.mem_sup_left (Subgroup.mem_sup_left (K.ev_mem v))

theorem idxTwo_dElt_mem (d : Dc) : dElt K d ∈ D.Ssub :=
  Subgroup.mem_sup_left (Subgroup.mem_sup_right (dElt_mem_D K d))

theorem idxTwo_s_mem : D.s ∈ D.Ssub :=
  Subgroup.mem_sup_right (Subgroup.subset_closure rfl)

theorem tElt_eq_ev_of_snd {p : Tc} (h : p.2 = 0) : tElt K p = K.ev p.1 := by
  obtain ⟨v, d⟩ := p
  simp only at h
  subst h
  exact tElt_ev K v

include hcom

theorem idxTwo_s_pow_comm_ev (n : ℕ) (v : Co) : D.s ^ n * K.ev v = K.ev v * D.s ^ n :=
  ((show Commute D.s (K.ev v) from hcom v).pow_left n).eq

theorem idxTwo_conj_ev_sElt (ε : ZMod 2) (v : Co) (d : Dc) (e : Co) :
    D.sElt (ε, v, d) * K.ev e * (D.sElt (ε, v, d))⁻¹ = K.ev (dact (dinv d) e) :=
  conj_mul_mul_of_commute (dElt_mul_ev_mul_inv d e) (K.comm (K.ev_mem v) (K.ev_mem _))
    (idxTwo_s_pow_comm_ev D hcom _ _)

theorem idxTwo_exists_conj_ev {q : X} (hq : q ∈ D.Ssub) :
    ∃ d : Dc, ∀ e, q * K.ev e * q⁻¹ = K.ev (dact (dinv d) e) := by
  obtain ⟨⟨ε, v, d⟩, rfl⟩ := D.exists_sElt hq
  exact ⟨d, idxTwo_conj_ev_sElt D hcom ε v d⟩

theorem idxTwo_exists_comm3_ev {q₁ q₂ q₃ : X} (h₁ : q₁ ∈ D.Ssub) (h₂ : q₂ ∈ D.Ssub)
    (h₃ : q₃ ∈ D.Ssub) :
    ∃ d₁ d₂ d₃ : Dc, ∀ e, ⁅⁅⁅K.ev e, q₁⁆, q₂⁆, q₃⁆ = K.ev (cmA d₃ (cmA d₂ (cmA d₁ e))) := by
  obtain ⟨d₁, hd₁⟩ := idxTwo_exists_conj_ev D hcom h₁
  obtain ⟨d₂, hd₂⟩ := idxTwo_exists_conj_ev D hcom h₂
  obtain ⟨d₃, hd₃⟩ := idxTwo_exists_conj_ev D hcom h₃
  exact ⟨d₁, d₂, d₃, fun e => by
    rw [comm_ev_eq_cmA hd₁, comm_ev_eq_cmA hd₂, comm_ev_eq_cmA hd₃]⟩

theorem idxTwo_exists_comm2_ev {q₁ q₂ : X} (h₁ : q₁ ∈ D.Ssub) (h₂ : q₂ ∈ D.Ssub) :
    ∃ d₁ d₂ : Dc, ∀ e, ⁅⁅K.ev e, q₁⁆, q₂⁆ = K.ev (cmA d₂ (cmA d₁ e)) := by
  obtain ⟨d₁, hd₁⟩ := idxTwo_exists_conj_ev D hcom h₁
  obtain ⟨d₂, hd₂⟩ := idxTwo_exists_conj_ev D hcom h₂
  exact ⟨d₁, d₂, fun e => by rw [comm_ev_eq_cmA hd₁, comm_ev_eq_cmA hd₂]⟩

theorem idxTwo_comm_sElt_s (ε : ZMod 2) (v : Co) (d : Dc)
    (h0 : (tmul (D.σ (0, d)) (0, dinv d)).2 = 0) :
    ⁅D.sElt (ε, v, d), D.s⁆ = K.ev (tmul (D.σ (0, d)) (0, dinv d)).1 := by
  have hd : ∀ e : Dc, tElt K (0, e) = dElt K e := fun e => by simp [tElt]
  have h1 : dElt K d * D.s * (dElt K d)⁻¹ = D.s * K.ev (tmul (D.σ (0, d)) (0, dinv d)).1 := by
    have hs := D.s_mul_tElt (0, d)
    rw [hd] at hs
    rw [hs, dElt_inv, ← hd (dinv d), mul_assoc, ← tElt_mul, tElt_eq_ev_of_snd h0]
  have hb : Commute (K.ev v) (D.s * K.ev (tmul (D.σ (0, d)) (0, dinv d)).1) :=
    (show Commute (K.ev v) D.s from (hcom v).symm).mul_right
      (show Commute (K.ev v) (K.ev _) from K.comm (K.ev_mem v) (K.ev_mem _))
  have ha : Commute (D.s ^ ε.val) (D.s * K.ev (tmul (D.σ (0, d)) (0, dinv d)).1) :=
    (Commute.self_pow D.s _).symm.mul_right
      ((show Commute D.s (K.ev _) from hcom _).pow_left _)
  have h2 := conj_mul_mul_of_commute (a := D.s ^ ε.val) (b := K.ev v) h1 hb.eq ha.eq
  change D.sElt (ε, v, d) * D.s * (D.sElt (ε, v, d))⁻¹ = _ at h2
  rw [commutatorElement_def, h2, hcom, mul_inv_cancel_right]

end Comm

section Char

variable {X : Type*} [Group X] {K : Config X}

theorem charA_conj {S : Subgroup X} {g : X} (hg : g ∈ Subgroup.normalizer (S : Set X)) {a : X}
    (ha : a ∈ S ∧
      (∀ z ∈ S, (∀ q₁ ∈ S, ∀ q₂ ∈ S, ∀ q₃ ∈ S, ⁅⁅⁅z, q₁⁆, q₂⁆, q₃⁆ = 1) → a * z = z * a) ∧
      (∀ q₁ ∈ S, ∀ q₂ ∈ S, ⁅⁅a * a, q₁⁆, q₂⁆ = 1)) :
    g * a * g⁻¹ ∈ S ∧
      (∀ z ∈ S, (∀ q₁ ∈ S, ∀ q₂ ∈ S, ∀ q₃ ∈ S, ⁅⁅⁅z, q₁⁆, q₂⁆, q₃⁆ = 1) →
        g * a * g⁻¹ * z = z * (g * a * g⁻¹)) ∧
      (∀ q₁ ∈ S, ∀ q₂ ∈ S, ⁅⁅g * a * g⁻¹ * (g * a * g⁻¹), q₁⁆, q₂⁆ = 1) := by
  obtain ⟨haS, haZ, haZ2⟩ := ha
  have hS : ∀ h, h ∈ S ↔ g * h * g⁻¹ ∈ S := Subgroup.mem_normalizer_iff.mp hg
  have hS' : ∀ {h}, h ∈ S → g⁻¹ * h * g ∈ S := fun {h} hh =>
    (hS _).mpr (by rwa [show g * (g⁻¹ * h * g) * g⁻¹ = h by group])
  have hc : ∀ x y : X, ⁅g * x * g⁻¹, g * y * g⁻¹⁆ = g * ⁅x, y⁆ * g⁻¹ := fun x y => by
    simp only [commutatorElement_def]; group
  have hb : ∀ q, g * (g⁻¹ * q * g) * g⁻¹ = q := fun q => by group
  refine ⟨(hS a).mp haS, fun z hz hzZ => ?_, fun q₁ h₁ q₂ h₂ => ?_⟩
  · have hz' := haZ _ (hS' hz) fun q₁ h₁ q₂ h₂ q₃ h₃ => by
      have := hzZ _ ((hS _).mp h₁) _ ((hS _).mp h₂) _ ((hS _).mp h₃)
      rw [← hb z, hc, hc, hc] at this
      have h1 : g * ⁅⁅⁅g⁻¹ * z * g, q₁⁆, q₂⁆, q₃⁆ * g⁻¹ = g * 1 * g⁻¹ := by rw [this]; group
      exact mul_left_cancel (mul_right_cancel h1)
    calc g * a * g⁻¹ * z = g * (a * (g⁻¹ * z * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * z * g) * a) * g⁻¹ := by rw [hz']
      _ = z * (g * a * g⁻¹) := by group
  · have := haZ2 _ (hS' h₁) _ (hS' h₂)
    rw [show g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ by group, ← hb q₁, ← hb q₂, hc, hc,
      this]
    group

variable (D : IdxTwo K) (hcom : ∀ v, D.s * K.ev v = K.ev v * D.s) (hs2 : D.s * D.s = K.w)
  (hγ : ∀ d : Dc, d ≠ 0 →
    (∃ (e : Co) (d₂ d₃ : Dc), cmA d₃ (cmA d₂ (dact (dinv d) e - e)) ≠ 0) ∨
      ((tmul (D.σ (0, d)) (0, dinv d)).2 = 0 ∧
        ∃ d₂ d₃ : Dc, cmA d₃ (cmA d₂ (tmul (D.σ (0, d)) (0, dinv d)).1) ≠ 0))

include hcom hγ in
theorem idxTwo_comm_ev_of_z3 {z : X} (hz : z ∈ D.Ssub)
    (hZ : ∀ q₁ ∈ D.Ssub, ∀ q₂ ∈ D.Ssub, ∀ q₃ ∈ D.Ssub, ⁅⁅⁅z, q₁⁆, q₂⁆, q₃⁆ = 1) (e : Co) :
    z * K.ev e = K.ev e * z := by
  obtain ⟨⟨ε, v, d⟩, rfl⟩ := D.exists_sElt hz
  by_cases hd : d = 0
  · subst hd
    have h1 := idxTwo_conj_ev_sElt D hcom ε v 0 e
    rw [frameA_dact_dinv_zero] at h1
    calc D.sElt (ε, v, 0) * K.ev e
        = D.sElt (ε, v, 0) * K.ev e * (D.sElt (ε, v, 0))⁻¹ * D.sElt (ε, v, 0) := by group
      _ = K.ev e * D.sElt (ε, v, 0) := by rw [h1]
  · exfalso
    rcases hγ d hd with ⟨e', d₂, d₃, hne⟩ | ⟨h0, d₂, d₃, hne⟩
    · have h := hZ _ (idxTwo_ev_mem D e') _ (idxTwo_dElt_mem D d₂) _ (idxTwo_dElt_mem D d₃)
      rw [comm_ev_right_eq (idxTwo_conj_ev_sElt D hcom ε v d),
        comm_ev_eq_cmA (dElt_mul_ev_mul_inv d₂), comm_ev_eq_cmA (dElt_mul_ev_mul_inv d₃),
        K.ev_eq_one_iff] at h
      exact hne h
    · have h := hZ _ (idxTwo_s_mem D) _ (idxTwo_dElt_mem D d₂) _ (idxTwo_dElt_mem D d₃)
      rw [idxTwo_comm_sElt_s D hcom ε v d h0, comm_ev_eq_cmA (dElt_mul_ev_mul_inv d₂),
        comm_ev_eq_cmA (dElt_mul_ev_mul_inv d₃), K.ev_eq_one_iff] at h
      exact hne h

include hcom hs2 in
theorem idxTwo_mem_A_of_comm_z3_gens {a : X} (ha : a ∈ D.Ssub)
    (hc : ∀ e ∈ ([(1, 0, 0), (0, 1, 1), (0, 0, 2)] : List Co), a * K.ev e = K.ev e * a)
    (hZ2 : ∀ q₁ ∈ D.Ssub, ∀ q₂ ∈ D.Ssub, ⁅⁅a * a, q₁⁆, q₂⁆ = 1) : a ∈ K.A := by
  obtain ⟨⟨ε, v, d⟩, rfl⟩ := D.exists_sElt ha
  have hfix : ∀ e ∈ ([(1, 0, 0), (0, 1, 1), (0, 0, 2)] : List Co), dact (dinv d) e = e :=
    fun e he => K.ev_injective (by
      rw [← idxTwo_conj_ev_sElt D hcom ε v d e, hc e he, mul_inv_cancel_right])
  have hd : d = 0 := frameA_fix_z3_gens d (hfix _ (by simp)) (hfix _ (by simp)) (hfix _ (by simp))
  subst hd
  have hev : tElt K (v, 0) = K.ev v := tElt_ev K v
  rcases zmod2_cases ε with rfl | rfl
  · rw [D.sElt_zero_fst, hev]; exact K.ev_mem v
  · exfalso
    rw [D.sElt_one_fst, hev] at hZ2
    have hsq : D.s * K.ev v * (D.s * K.ev v) = K.ev ((1, 0, 0) + (v + v)) := by
      rw [K.ev_add, K.ev_add, K.ev_w, ← hs2]
      calc D.s * K.ev v * (D.s * K.ev v) = D.s * (K.ev v * D.s) * K.ev v := by group
        _ = D.s * D.s * (K.ev v * K.ev v) := by rw [← hcom]; group
    obtain ⟨d₁, d₂, hne⟩ := frameA_not_z2_csq v
    have h := hZ2 _ (idxTwo_dElt_mem D d₁) _ (idxTwo_dElt_mem D d₂)
    rw [hsq, comm_ev_eq_cmA (dElt_mul_ev_mul_inv d₁), comm_ev_eq_cmA (dElt_mul_ev_mul_inv d₂),
      K.ev_eq_one_iff] at h
    exact hne h

include hcom hs2 hγ in
theorem mem_A_iff_of_idxTwo (a : X) :
    a ∈ K.A ↔ a ∈ D.Ssub ∧
      (∀ z ∈ D.Ssub, (∀ q₁ ∈ D.Ssub, ∀ q₂ ∈ D.Ssub, ∀ q₃ ∈ D.Ssub, ⁅⁅⁅z, q₁⁆, q₂⁆, q₃⁆ = 1) →
        a * z = z * a) ∧
      (∀ q₁ ∈ D.Ssub, ∀ q₂ ∈ D.Ssub, ⁅⁅a * a, q₁⁆, q₂⁆ = 1) := by
  constructor
  · intro ha
    obtain ⟨v, rfl⟩ := K.exists_ev ha
    refine ⟨idxTwo_ev_mem D v, fun z hz hZ => (idxTwo_comm_ev_of_z3 D hcom hγ hz hZ v).symm,
      fun q₁ h₁ q₂ h₂ => ?_⟩
    obtain ⟨d₁, d₂, h⟩ := idxTwo_exists_comm2_ev D hcom h₁ h₂
    rw [← K.ev_add, h, frameA_z2_sq, K.ev_zero]
  · rintro ⟨haS, hZ, hZ2⟩
    refine idxTwo_mem_A_of_comm_z3_gens D hcom hs2 haS (fun e he => hZ _ (idxTwo_ev_mem D e) ?_) hZ2
    intro q₁ h₁ q₂ h₂ q₃ h₃
    obtain ⟨d₁, d₂, d₃, h⟩ := idxTwo_exists_comm3_ev D hcom h₁ h₂ h₃
    rw [h, frameA_z3_gens e he, K.ev_zero]

include hcom hs2 hγ in
theorem mem_normalizer_A_of_idxTwo {g : X} (hg : g ∈ Subgroup.normalizer (D.Ssub : Set X)) :
    g ∈ Subgroup.normalizer (K.A : Set X) := by
  have hchar := mem_A_iff_of_idxTwo D hcom hs2 hγ
  have hg' : g⁻¹ ∈ Subgroup.normalizer (D.Ssub : Set X) := inv_mem hg
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    exact (hchar _).mpr (charA_conj hg ((hchar a).mp ha))
  · intro ha
    have := charA_conj hg' ((hchar _).mp ha)
    rw [show g⁻¹ * (g * a * g⁻¹) * g⁻¹⁻¹ = a by group] at this
    exact (hchar a).mpr this

end Char

section Shapes

variable {X : Type*} [Group X] (K : Config X)

@[expose] def idxTwo4 {c : X} (hcx : c⁻¹ * K.x * c = K.x) (hcy : c⁻¹ * K.y * c = K.y)
    (hc2 : c ^ 2 = K.w) (huv : K.uv⁻¹ * c * K.uv = c * K.x * K.y⁻¹)
    (ht : K.t⁻¹ * c * K.t = c * K.x * K.y ^ 2) (hu : K.u⁻¹ * c * K.u = c⁻¹) (hcT : c ∉ Tsub K) :
    IdxTwo K where
  s := c
  iw := ((1, 0, 0), 0)
  ix := ((0, 1, 0), 0)
  iy := ((0, 0, 1), 0)
  iuv := ((0, 1, 3), (1, 0, 0))
  it := ((0, 1, 2), (0, 1, 0))
  iu := ((1, 0, 0), (0, 0, 1))
  z := ((1, 0, 0), 0)
  hw := by
    rw [tElt_w, ← hc2, pow_two]
    group
  hx := by rw [tElt_x, hcx]
  hy := by rw [tElt_y, hcy]
  huv := by
    have h1 : tElt K ((0, 1, 3), (1, 0, 0)) = K.x * K.y⁻¹ * K.uv := by
      rw [show ((0, 1, 3), (1, 0, 0)) = tmul ((0, 1, 3), 0) (0, (1, 0, 0)) from rfl, tElt_mul,
        tElt_ev, tElt_gen_uv]
      simp [Config.ev, K.y_inv_eq, show (1 : ZMod 4).val = 1 from rfl,
        show (3 : ZMod 4).val = 3 from rfl]
    rw [h1]
    calc c⁻¹ * K.uv * c = c⁻¹ * (K.uv * c * K.uv⁻¹) * K.uv := by group
      _ = c⁻¹ * (K.uv⁻¹ * c * K.uv) * K.uv := by rw [uv_inv K]
      _ = K.x * K.y⁻¹ * K.uv := by rw [huv]; group
  ht := by
    have h1 : tElt K ((0, 1, 2), (0, 1, 0)) = K.x * K.y ^ 2 * K.t := by
      rw [show ((0, 1, 2), (0, 1, 0)) = tmul ((0, 1, 2), 0) (0, (0, 1, 0)) from rfl, tElt_mul,
        tElt_ev, tElt_gen_t]
      simp [Config.ev, show (1 : ZMod 4).val = 1 from rfl, show (2 : ZMod 4).val = 2 from rfl]
    rw [h1]
    calc c⁻¹ * K.t * c = c⁻¹ * (K.t * c * K.t⁻¹) * K.t := by group
      _ = c⁻¹ * (K.t⁻¹ * c * K.t) * K.t := by rw [t_inv K]
      _ = K.x * K.y ^ 2 * K.t := by rw [ht]; group
  hu := by
    rw [tElt_wu, ← hc2, pow_two]
    calc c⁻¹ * K.u * c = c⁻¹ * (K.u * c * K.u⁻¹) * K.u := by group
      _ = c⁻¹ * (K.u⁻¹ * c * K.u) * K.u := by rw [u_inv K]
      _ = c * c * K.u := by
        rw [hu]
        have hc4 : c ^ 4 = 1 := by rw [show 4 = 2 * 2 by rfl, pow_mul, hc2, K.hw]
        calc c⁻¹ * c⁻¹ * K.u = (c ^ 4)⁻¹ * (c * c) * K.u := by group
          _ = c * c * K.u := by rw [hc4]; group
  hz := by rw [tElt_w, ← hc2, pow_two]
  hsT := hcT

theorem not_mem_Tsub_of_sq_eq_w {c : X} (hcx : c⁻¹ * K.x * c = K.x) (hcy : c⁻¹ * K.y * c = K.y)
    (hc2 : c ^ 2 = K.w) : c ∉ Tsub K := by
  intro hc
  obtain ⟨p, rfl⟩ := exists_tElt K hc
  have hx : tmul p ((0, 1, 0), 0) = tmul ((0, 1, 0), 0) p := tElt_injective K (by
    rw [tElt_mul, tElt_mul, tElt_x]
    calc tElt K p * K.x = tElt K p * ((tElt K p)⁻¹ * K.x * tElt K p) := by rw [hcx]
      _ = K.x * tElt K p := by group)
  have hy : tmul p ((0, 0, 1), 0) = tmul ((0, 0, 1), 0) p := tElt_injective K (by
    rw [tElt_mul, tElt_mul, tElt_y]
    calc tElt K p * K.y = tElt K p * ((tElt K p)⁻¹ * K.y * tElt K p) := by rw [hcy]
      _ = K.y * tElt K p := by group)
  exact tc_not_sqrt_w p ⟨hx, hy⟩ (tElt_injective K (by rw [tElt_mul, tElt_w, ← hc2, pow_two]))

theorem comm_ev_of_comm_xy {c : X} (hcx : c⁻¹ * K.x * c = K.x) (hcy : c⁻¹ * K.y * c = K.y)
    (hc2 : c ^ 2 = K.w) (v : Co) : c * K.ev v = K.ev v * c := by
  have hx : Commute c K.x := by
    show c * K.x = K.x * c
    calc c * K.x = c * (c⁻¹ * K.x * c) := by rw [hcx]
      _ = K.x * c := by group
  have hy : Commute c K.y := by
    show c * K.y = K.y * c
    calc c * K.y = c * (c⁻¹ * K.y * c) := by rw [hcy]
      _ = K.y * c := by group
  have hw : Commute c K.w := by rw [← hc2]; exact Commute.self_pow c 2
  exact (((hw.pow_right _).mul_right (hx.pow_right _)).mul_right (hy.pow_right _)).eq

theorem closure_cxy_sup_eq {c : X} (hc2 : c ^ 2 = K.w) :
    Subgroup.closure {c, K.x, K.y} ⊔ Subgroup.closure {K.uv, K.t, K.u} =
      Tsub K ⊔ Subgroup.closure {c} := by
  have hcR : c ∈ Tsub K ⊔ Subgroup.closure {c} :=
    Subgroup.mem_sup_right (Subgroup.subset_closure rfl)
  have hTR : Tsub K ≤ Tsub K ⊔ Subgroup.closure {c} := le_sup_left
  have hcL : c ∈ Subgroup.closure {c, K.x, K.y} ⊔ Subgroup.closure {K.uv, K.t, K.u} :=
    Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
  apply le_antisymm
  · refine sup_le ((Subgroup.closure_le _).mpr ?_) (le_sup_right.trans hTR)
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    exacts [hcR, hTR (Subgroup.mem_sup_left K.x_mem), hTR (Subgroup.mem_sup_left K.y_mem)]
  · refine sup_le (sup_le ?_ le_sup_right) ((Subgroup.closure_le _).mpr (by simpa using hcL))
    rw [K.hA, Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · rw [← hc2]; exact pow_mem hcL 2
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))

theorem card_closure_cxy_sup {c : X} (hcx : c⁻¹ * K.x * c = K.x) (hcy : c⁻¹ * K.y * c = K.y)
    (hc2 : c ^ 2 = K.w)
    (hcase : (K.uv⁻¹ * c * K.uv = c * K.x⁻¹ * K.y⁻¹ ∧ K.t⁻¹ * c * K.t = c * K.x ∧
        K.u⁻¹ * c * K.u = c) ∨
      (K.uv⁻¹ * c * K.uv = c * K.x * K.y⁻¹ ∧ K.t⁻¹ * c * K.t = c * K.x * K.y ^ 2 ∧
        K.u⁻¹ * c * K.u = c⁻¹)) :
    Nat.card (Subgroup.closure {c, K.x, K.y} ⊔ Subgroup.closure {K.uv, K.t, K.u} :
      Subgroup X) = 2 ^ 9 := by
  have hcT := not_mem_Tsub_of_sq_eq_w K hcx hcy hc2
  rw [closure_cxy_sup_eq K hc2]
  rcases hcase with ⟨huv, ht, hu⟩ | ⟨huv, ht, hu⟩
  · exact (idxTwo3 K hcx hcy hc2 huv ht hu hcT).card_Ssub
  · exact (idxTwo4 K hcx hcy hc2 huv ht hu hcT).card_Ssub

theorem normalizer_le_normalizer_A_of_shape {c : X} (hcx : c⁻¹ * K.x * c = K.x)
    (hcy : c⁻¹ * K.y * c = K.y) (hc2 : c ^ 2 = K.w)
    (hcase : (K.uv⁻¹ * c * K.uv = c * K.x⁻¹ * K.y⁻¹ ∧ K.t⁻¹ * c * K.t = c * K.x ∧
        K.u⁻¹ * c * K.u = c) ∨
      (K.uv⁻¹ * c * K.uv = c * K.x * K.y⁻¹ ∧ K.t⁻¹ * c * K.t = c * K.x * K.y ^ 2 ∧
        K.u⁻¹ * c * K.u = c⁻¹)) :
    Subgroup.normalizer ((Subgroup.closure {c, K.x, K.y} ⊔ Subgroup.closure {K.uv, K.t, K.u} :
      Subgroup X) : Set X) ≤ Subgroup.normalizer (K.A : Set X) := by
  have hcT := not_mem_Tsub_of_sq_eq_w K hcx hcy hc2
  have hcom := comm_ev_of_comm_xy K hcx hcy hc2
  have hs2 : c * c = K.w := by rw [← pow_two, hc2]
  intro g hg
  rw [closure_cxy_sup_eq K hc2] at hg
  rcases hcase with ⟨huv, ht, hu⟩ | ⟨huv, ht, hu⟩
  · exact mem_normalizer_A_of_idxTwo (idxTwo3 K hcx hcy hc2 huv ht hu hcT) hcom hs2
      frameA_z3_fact3 hg
  · exact mem_normalizer_A_of_idxTwo (idxTwo4 K hcx hcy hc2 huv ht hu hcT) hcom hs2
      frameA_z3_fact4 hg

end Shapes

end CFSG.CGT.Stroth76
