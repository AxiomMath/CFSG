module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneFinkelsteinNonabelianFourSetup

public section

namespace CFSG.SeitzReduction.RankOne

open CFSG.ComponentClassification.GMS78.Finkelstein
open scoped commutatorElement

namespace Finkelstein

theorem aux_cancel {G : Type} [Group G] {e1 e2 e3 e4 : G} (hc1 : ∀ g : G, g * e1 = e1 * g)
    (hc4 : ∀ g : G, g * e4 = e4 * g) (h0 : e1 * e2 * (e3 * e4) * (e1⁻¹ * e4⁻¹) = 1) :
    e2 * e3 = 1 := by
  calc e2 * e3 = e1 * (e2 * e3) * e1⁻¹ * (e4 * e4⁻¹) := by rw [← hc1 (e2 * e3)]; group
    _ = e1 * e2 * (e3 * e4) * (e1⁻¹ * e4⁻¹) := by
        rw [show e1 * (e2 * e3) * e1⁻¹ * (e4 * e4⁻¹) = e1 * (e2 * e3) * (e1⁻¹ * e4) * e4⁻¹ by
          group, hc4 e1⁻¹]
        group
    _ = 1 := h0

theorem aux_sq {G : Type} [Group G] {a d₁ d₂ : G} (ha : ∀ g : G, g * a = a * g)
    (ha2 : a * a = 1) (hc : d₂ * d₁ = d₁ * d₂) : (a * d₂ * d₁) ^ 2 = d₂ ^ 2 * d₁ ^ 2 := by
  simp only [pow_two]
  calc a * d₂ * d₁ * (a * d₂ * d₁) = a * (d₂ * d₁ * a) * (d₂ * d₁) := by group
    _ = a * a * (d₂ * (d₁ * d₂) * d₁) := by rw [ha (d₂ * d₁)]; group
    _ = d₂ * d₂ * (d₁ * d₁) := by rw [ha2, one_mul, ← hc]; group

end Finkelstein

namespace Finkelstein.Hyp

variable {U : Type} [Group U] [Finite U] {n : ℕ} {t y : MulAut U} (h : Finkelstein.Hyp U n t y)
include h

theorem trick_balanced (θ : U →* U) (hθA : ∀ u, θ u ∈ fixSubgroup t)
    (hθy : ∀ u, θ (y u) = y (θ u)) {β : U → U → U} (hβA : ∀ u v, β u v ∈ fixSubgroup t)
    (hβl : ∀ u v w, β (u * v) w = β u w * β v w) (hβr : ∀ u v w, β u (v * w) = β u v * β u w)
    (hβy : ∀ u v, β (y u) (y v) = y (β u v)) (hβθl : ∀ u v, θ u = 1 → β u v = 1)
    (hβθr : ∀ u v, θ v = 1 → β u v = 1) (j : ℕ) (u v : U) :
    β u ((y ^ j) v) = β v ((y ^ j) u) := by
  have hθ1 : ∀ u u', θ u = θ u' → θ (u⁻¹ * u') = 1 := fun u u' hu => by
    rw [map_mul, map_inv, hu, inv_mul_cancel]
  have hfib1 : ∀ u u' w, θ u = θ u' → β u w = β u' w := fun u u' w hu => by
    rw [show u' = u * (u⁻¹ * u') by group, hβl, hβθl _ _ (hθ1 u u' hu), mul_one]
  have hfib2 : ∀ u w w', θ w = θ w' → β u w = β u w' := fun u w w' hw => by
    rw [show w' = w * (w⁻¹ * w') by group, hβr, hβθr _ _ (hθ1 w w' hw), mul_one]
  have hyj : ∀ (j : ℕ) (u : U), (y ^ j) (y u) = y ((y ^ j) u) := fun j u => by
    have h1 := pow_pow_apply_comm y j 1 u
    rwa [pow_one] at h1
  have hm := h.trick_mul θ hθA hθy (f := fun u => β u ((y ^ j) u)) (fun u => hβA _ _)
    (fun u => by rw [hyj, hβy]) (fun u v huv => by
      rw [hfib1 u v _ huv]
      exact hfib2 v _ _ (by rw [map_pow_of_comm hθy, map_pow_of_comm hθy, huv])) u v
  simp only [map_mul, hβl, hβr] at hm
  have h2 : β u ((y ^ j) u) * ((β u ((y ^ j) v) * β v ((y ^ j) u)) * β v ((y ^ j) v)) =
      β u ((y ^ j) u) * (1 * β v ((y ^ j) v)) := by
    rw [one_mul, ← hm]
    group
  have h3 : β u ((y ^ j) v) * β v ((y ^ j) u) = 1 := mul_right_cancel (mul_left_cancel h2)
  have h4 : β v ((y ^ j) u) * β v ((y ^ j) u) = 1 := h.mul_self_eq_one_of_mem_fix (hβA _ _)
  exact mul_right_cancel (h3.trans h4.symm)

theorem trick_half (θ : U →* U) (hθA : ∀ u, θ u ∈ fixSubgroup t)
    (hθy : ∀ u, θ (y u) = y (θ u)) {β : U → U → U} (hβA : ∀ u v, β u v ∈ fixSubgroup t)
    (hβl : ∀ u v w, β (u * v) w = β u w * β v w) (hβr : ∀ u v w, β u (v * w) = β u v * β u w)
    (hβy : ∀ u v, β (y u) (y v) = y (β u v)) (hβθl : ∀ u v, θ u = 1 → β u v = 1)
    (hβθr : ∀ u v, θ v = 1 → β u v = 1) (w h' : U) :
    β w ((y ^ 2) h') = y (β w h') ∧ β ((y ^ 2) w) h' = y (β w h') := by
  have hbal := h.trick_balanced θ hθA hθy hβA hβl hβr hβy hβθl hβθr
  have hsymm : ∀ u v, β u v = β v u := fun u v => by
    have := hbal 0 u v
    simpa using this
  have hy2 : ∀ x : U, (y ^ 2) x = y (y x) := fun x => by rw [pow_two, MulAut.mul_apply]
  have h1 : ∀ w h' : U, β w ((y ^ 2) h') = y (β w h') := fun w h' => by
    have h2 := hbal 1 (y w) h'
    simp only [pow_one] at h2
    rw [hbal 2 w h', hy2, ← h2, hβy]
  refine ⟨h1 w h', ?_⟩
  rw [hsymm, h1, hsymm]

theorem commutator_inv_mem_bSub_of_psi_mem {x : U} (hx : psi t x ∈ h.bSub) (g : U) :
    ⁅x⁻¹, g⁆ ∈ h.bSub := by
  have e : ⁅x⁻¹, g⁆ = x⁻¹ * ⁅x, g⁆⁻¹ * x⁻¹⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact h.conj_mem_bSub (inv_mem (h.commutator_mem_bSub_of_psi_mem hx g)) _

omit h [Finite U] in
theorem psi_mul_eq (z z' : U) : psi t (z * z') = psi t z * ⁅(psi t z)⁻¹, z'⁻¹⁆ * psi t z' := by
  simp only [psi, commutatorElement_def, map_mul]
  group

section FourLayers

variable (hsqB : ∀ u : U, u ^ 2 ∈ h.bSub) (hncV : ∃ u v : U, ⁅u, v⁆ ∉ fixSubgroup t)
include hsqB hncV

theorem commutator_bSub_psi_eq_one {b : U} (hb : b ∈ h.bSub) (z : U) : ⁅b, psi t z⁆ = 1 := by
  have hA := fix_ne_top_of_commutator hncV
  have hcen := fun {a : U} (ha : a ∈ fixSubgroup t) => h.central_of_mem_fix ha
  have hBA : ∀ {b : U}, b ∈ h.bSub → ∀ g, ⁅b, g⁆ ∈ fixSubgroup t :=
    fun hb g => h.commutator_mem_fix_of_mem_bSub hb g
  have hpp := h.psi_psi_mem_bSub hsqB
  have key : ∀ w z : U, ⁅psi t (psi t w), psi t z⁆ = 1 := by
    refine h.trick_bilin (h.thetaHom hsqB hA) (h.thetaHom_mem hsqB hA) (h.thetaHom_y hsqB hA)
      (β := fun w z => ⁅psi t (psi t w), psi t z⁆) (fun w z => hBA (hpp w) _) ?_ ?_ ?_ ?_ ?_
    · intro w w' z
      have hm := h.psi_psi_mul_mod hsqB hA w w'
      rw [show psi t (psi t (w * w')) = psi t (psi t w) * psi t (psi t w') *
          ((psi t (psi t w) * psi t (psi t w'))⁻¹ * psi t (psi t (w * w'))) by group,
        commutator_mul_left_of_central (hcen (h.commutator_fix_left hm _ ▸ one_mem _)),
        h.commutator_fix_left hm, one_mul,
        commutator_mul_left_of_central (hcen (hBA (hpp w') _)), hcen (hBA (hpp w') _)]
    · intro w z z'
      have hc : ⁅(psi t z)⁻¹, z'⁻¹⁆ ∈ h.bSub :=
        h.commutator_inv_mem_bSub_of_psi_mem (hpp z) _
      have hc1 : ⁅psi t (psi t w), ⁅(psi t z)⁻¹, z'⁻¹⁆⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.mpr (h.bSub_comm hA (hpp w) hc)
      rw [psi_mul_eq z z', commutator_mul_right_of_central (hcen (hBA (hpp w) _)),
        commutator_mul_right_of_central (hc1 ▸ fun g => by rw [mul_one, one_mul]), hc1, mul_one]
    · intro w z
      simp only [psi_map_of_comm h.comm, map_commutatorElement]
    · intro w
      rw [psi_psi h.t_t, commutatorElement_eq_one_iff_mul_comm]
      group
    · intro w z hw
      exact h.commutator_fix_left (psi_eq_one_iff.mp hw) _
  obtain ⟨w, hw⟩ := h.exists_psi_psi_mod hsqB hncV hb
  rw [show b = psi t (psi t w) * ((psi t (psi t w))⁻¹ * b) by group,
    commutator_mul_left_of_central (hcen (h.commutator_fix_left hw _ ▸ one_mem _)),
    h.commutator_fix_left hw, one_mul, key]

theorem commutator_bSub_A3_eq_one {b x : U} (hb : b ∈ h.bSub) (hx : psi t x ∈ h.bSub) :
    ⁅b, x⁆ = 1 := by
  have hA := fix_ne_top_of_commutator hncV
  obtain ⟨z, hz⟩ := h.exists_psi_mod hsqB hncV hx
  have hc1 : ⁅b, (psi t z)⁻¹ * x⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (h.bSub_comm hA hb hz)
  rw [show x = psi t z * ((psi t z)⁻¹ * x) by group,
    commutator_mul_right_of_central (hc1 ▸ fun g => by rw [mul_one, one_mul]), hc1, mul_one,
    h.commutator_bSub_psi_eq_one hsqB hncV hb]

omit hsqB hncV in
theorem commutator_left_mem_bSub_of_psi_mem {x : U} (hx : psi t x ∈ h.bSub) (g : U) :
    ⁅g, x⁆ ∈ h.bSub := by
  rw [← commutatorElement_inv]
  exact inv_mem (h.commutator_mem_bSub_of_psi_mem hx g)

theorem dlt_id {x : U} (hx : psi t x ∈ h.bSub) (g : U) : ⁅g, ⁅g, x⁆⁆ * ⁅g, x⁆ ^ 2 = 1 := by
  have hg2 : g ^ 2 * x = x * g ^ 2 :=
    commutatorElement_eq_one_iff_mul_comm.mp (h.commutator_bSub_A3_eq_one hsqB hncV (hsqB g) hx)
  have e : g ^ 2 * x * (g ^ 2)⁻¹ = ⁅g, ⁅g, x⁆⁆ * ⁅g, x⁆ ^ 2 * x := by
    simp only [commutatorElement_def, pow_two]
    group
  rw [hg2, mul_inv_cancel_right] at e
  exact (mul_eq_right.mp e.symm)

theorem commutator_comm_A3 {x : U} (hx : psi t x ∈ h.bSub) (g k : U) :
    ⁅k, ⁅g, x⁆⁆ = ⁅g, ⁅k, x⁆⁆ := by
  have hA := fix_ne_top_of_commutator hncV
  have hcen := fun {a : U} (ha : a ∈ fixSubgroup t) => h.central_of_mem_fix ha
  have hBA : ∀ {b : U}, b ∈ h.bSub → ∀ m, ⁅m, b⁆ ∈ fixSubgroup t := fun hb m => by
    rw [← commutatorElement_inv]
    exact inv_mem (h.commutator_mem_fix_of_mem_bSub hb m)
  set d₁ := ⁅g, x⁆ with hd₁
  set d₂ := ⁅k, x⁆ with hd₂
  have hd₁B : d₁ ∈ h.bSub := h.commutator_left_mem_bSub_of_psi_mem hx g
  have hd₂B : d₂ ∈ h.bSub := h.commutator_left_mem_bSub_of_psi_mem hx k
  set a := ⁅g, d₂⁆ with ha
  have haA : a ∈ fixSubgroup t := hBA hd₂B g
  have hD : ⁅g * k, x⁆ = a * d₂ * d₁ := by
    simp only [ha, hd₁, hd₂, commutatorElement_def]
    group
  have hDB : a * d₂ * d₁ ∈ h.bSub := mul_mem (mul_mem (h.fix_le_bSub haA) hd₂B) hd₁B
  have hma : ∀ m : U, ⁅m, a⁆ = 1 := fun m => by
    rw [← commutatorElement_inv, h.commutator_fix_left haA, inv_one]
  have hexp : ∀ m : U, ⁅m, a * d₂ * d₁⁆ = ⁅m, d₂⁆ * ⁅m, d₁⁆ := fun m => by
    rw [commutator_mul_right_of_central (hcen (hBA hd₁B m)),
      commutator_mul_right_of_central (hcen (hBA hd₂B m)), hma, one_mul]
  have hsq : (a * d₂ * d₁) ^ 2 = d₂ ^ 2 * d₁ ^ 2 :=
    aux_sq (hcen haA) (h.mul_self_eq_one_of_mem_fix haA) (h.bSub_comm hA hd₂B hd₁B)
  have h0 := h.dlt_id hsqB hncV hx (g * k)
  rw [hD, commutator_mul_left_of_central (hcen (hBA hDB k)), hexp, hexp, hsq] at h0
  have h1 := h.dlt_id hsqB hncV hx k
  have h4 := h.dlt_id hsqB hncV hx g
  rw [← hd₂] at h1
  rw [← hd₁] at h4
  have key : ⁅k, d₁⁆ * ⁅g, d₂⁆ = 1 := by
    have hs2 : d₂ ^ 2 = ⁅k, d₂⁆⁻¹ := eq_inv_of_mul_eq_one_right h1
    have hs1 : d₁ ^ 2 = ⁅g, d₁⁆⁻¹ := eq_inv_of_mul_eq_one_right h4
    rw [hs2, hs1] at h0
    exact aux_cancel (hcen (hBA hd₂B k)) (hcen (hBA hd₁B g)) h0
  have h5 : ⁅g, d₂⁆ * ⁅g, d₂⁆ = 1 := h.mul_self_eq_one_of_mem_fix haA
  exact mul_right_cancel (key.trans h5.symm)

theorem commutator_mul_right_A3 {P Q : U} (hP : psi t P ∈ h.bSub) (g : U)
    (hQ : ⁅g, Q⁆ ∈ h.bSub) : ⁅g, P * Q⁆ = ⁅g, P⁆ * ⁅g, Q⁆ := by
  have hc : ⁅g, Q⁆ * P = P * ⁅g, Q⁆ :=
    commutatorElement_eq_one_iff_mul_comm.mp (h.commutator_bSub_A3_eq_one hsqB hncV hQ hP)
  calc ⁅g, P * Q⁆ = ⁅g, P⁆ * (P * ⁅g, Q⁆ * P⁻¹) := by
        simp only [commutatorElement_def]; group
    _ = ⁅g, P⁆ * ⁅g, Q⁆ := by rw [← hc, mul_inv_cancel_right]

theorem weight_UB {b : U} (hb : b ∈ h.bSub) (k : U) :
    ⁅(y ^ 2) k, b⁆ = y ⁅k, b⁆ ∧ ⁅k, (y ^ 2) b⁆ = y ⁅k, b⁆ := by
  have hA := fix_ne_top_of_commutator hncV
  have hcen := fun {a : U} (ha : a ∈ fixSubgroup t) => h.central_of_mem_fix ha
  have hBA : ∀ {b : U}, b ∈ h.bSub → ∀ m, ⁅m, b⁆ ∈ fixSubgroup t := fun hb m => by
    rw [← commutatorElement_inv]
    exact inv_mem (h.commutator_mem_fix_of_mem_bSub hb m)
  have hkill : ∀ {a : U}, a ∈ fixSubgroup t → ∀ m P : U, ⁅m, P * a⁆ = ⁅m, P⁆ := by
    intro a ha m P
    have h1 : ⁅m, a⁆ = 1 := by rw [← commutatorElement_inv, h.commutator_fix_left ha, inv_one]
    rw [commutator_mul_right_of_central (h1 ▸ fun g => by rw [mul_one, one_mul]), h1, mul_one]
  have hpp := h.psi_psi_mem_bSub hsqB
  have hhalf := h.trick_half (h.thetaHom hsqB hA) (h.thetaHom_mem hsqB hA)
    (h.thetaHom_y hsqB hA) (β := fun w k => ⁅k, psi t (psi t w)⁆) (fun w k => hBA (hpp w) k)
    (fun w w' k => by
      have hm := h.psi_psi_mul_mod hsqB hA w w'
      rw [show psi t (psi t (w * w')) = psi t (psi t w) * psi t (psi t w') *
          ((psi t (psi t w) * psi t (psi t w'))⁻¹ * psi t (psi t (w * w'))) by group,
        hkill hm, commutator_mul_right_of_central (hcen (hBA (hpp w') k))])
    (fun w k k' => by
      rw [commutator_mul_left_of_central (hcen (hBA (hpp w) k')), hcen (hBA (hpp w) k')])
    (fun w k => by simp only [psi_map_of_comm h.comm, map_commutatorElement])
    (fun w k hw => by
      rw [← commutatorElement_inv, h.commutator_fix_left (psi_eq_one_iff.mp hw), inv_one])
    (fun w k hk => by
      rw [← commutatorElement_inv,
        h.commutator_bSub_A3_eq_one hsqB hncV (hpp w) ((h.thetaHom_eq_one_iff hsqB hA k).mp hk),
        inv_one])
  obtain ⟨w, hw⟩ := h.exists_psi_psi_mod hsqB hncV hb
  have hb' : b = psi t (psi t w) * ((psi t (psi t w))⁻¹ * b) := by group
  obtain ⟨h1, h2⟩ := hhalf w k
  refine ⟨?_, ?_⟩
  · rw [hb', hkill hw, hkill hw]
    exact h1
  · have hyA : (y ^ 2) ((psi t (psi t w))⁻¹ * b) ∈ fixSubgroup t := h.pow_mem_fix 2 hw
    rw [hb', map_mul, hkill hyA, hkill hw, ← h2]
    simp only [map_pow_of_comm (fun u => psi_map_of_comm h.comm u)]

theorem weight_A3 (w g g'' : U) (j : ℕ) :
    ⁅g'', (y ^ j) ⁅(y ^ 2) g, psi t w⁆⁆ = ⁅g'', (y ^ j) (y ⁅g, psi t w⁆)⁆ := by
  have hA := fix_ne_top_of_commutator hncV
  have hpp := h.psi_psi_mem_bSub hsqB
  have hcB : ∀ g w : U, ⁅g, psi t w⁆ ∈ h.bSub := fun g w =>
    h.commutator_left_mem_bSub_of_psi_mem (hpp w) g
  have hBAl : ∀ {b : U}, b ∈ h.bSub → ∀ m, ⁅m, b⁆ ∈ fixSubgroup t := fun hb m => by
    rw [← commutatorElement_inv]
    exact inv_mem (h.commutator_mem_fix_of_mem_bSub hb m)
  have hψA : ∀ {a : U}, a ∈ fixSubgroup t → psi t a = 1 := fun ha => psi_eq_one_iff.mpr ha
  have hhalf := h.trick_half (h.thetaHom hsqB hA) (h.thetaHom_mem hsqB hA)
    (h.thetaHom_y hsqB hA) (β := fun w g => psi t ⁅g, psi t w⁆) (fun w g => hcB g w)
    (fun w w' g => by
      have hc : ⁅(psi t w)⁻¹, w'⁻¹⁆ ∈ h.bSub :=
        h.commutator_inv_mem_bSub_of_psi_mem (hpp w) _
      have hcψ : psi t (⁅(psi t w)⁻¹, w'⁻¹⁆ * psi t w') ∈ h.bSub := by
        rw [h.psi_mul_of_mem hc]
        exact mul_mem (h.fix_le_bSub hc) (hpp w')
      rw [psi_mul_eq w w', mul_assoc,
        h.commutator_mul_right_A3 hsqB hncV (hpp w) g
          (h.commutator_left_mem_bSub_of_psi_mem hcψ g),
        h.commutator_mul_right_A3 hsqB hncV (h.fix_le_bSub hc) g (hcB g w'),
        h.psi_mul_of_mem (hcB g w), h.psi_mul_of_mem (by
          rw [hψA (hBAl hc g)]; exact one_mem _), hψA (hBAl hc g), one_mul])
    (fun w g g' => by
      have e : ⁅g * g', psi t w⁆ = ⁅g, ⁅g', psi t w⁆⁆ * ⁅g', psi t w⁆ * ⁅g, psi t w⁆ := by
        simp only [commutatorElement_def]; group
      have ha : ⁅g, ⁅g', psi t w⁆⁆ ∈ fixSubgroup t := hBAl (hcB g' w) g
      rw [e, h.psi_mul_of_mem (by
          rw [h.psi_mul_of_mem (by rw [hψA ha]; exact one_mem _)]
          exact mul_mem (by rw [hψA ha]; exact one_mem _) (hcB g' w)),
        h.psi_mul_of_mem (by rw [hψA ha]; exact one_mem _), hψA ha, one_mul]
      exact h.mem_center_of_mem_fix (hcB g w) _)
    (fun w g => by rw [psi_map_of_comm h.comm w, ← map_commutatorElement, psi_map_of_comm h.comm])
    (fun w g hw => by
      exact hψA (hBAl ((h.thetaHom_eq_one_iff hsqB hA w).mp hw) g))
    (fun w g hg => by
      exact hψA (h.commutator_mem_fix_of_psi_mem ((h.thetaHom_eq_one_iff hsqB hA g).mp hg)
        (hpp w)))
  have h1 := (hhalf w g).1
  rw [← psi_map_of_comm h.comm] at h1
  have hyB : y ⁅g, psi t w⁆ ∈ h.bSub := by
    rw [mem_bSub, psi_map_of_comm h.comm]
    simpa using h.pow_mem_fix 1 (hcB g w)
  have hm := h.inv_mul_mem_fix_of_psi_eq hyB h1.symm
  have hkill : ∀ {a : U}, a ∈ fixSubgroup t → ∀ m P : U, ⁅m, P * a⁆ = ⁅m, P⁆ := by
    intro a ha m P
    have h1 : ⁅m, a⁆ = 1 := by rw [← commutatorElement_inv, h.commutator_fix_left ha, inv_one]
    rw [commutator_mul_right_of_central (h1 ▸ fun g => by rw [mul_one, one_mul]), h1, mul_one]
  rw [show ⁅(y ^ 2) g, psi t w⁆ = y ⁅g, psi t w⁆ * ((y ⁅g, psi t w⁆)⁻¹ * ⁅(y ^ 2) g, psi t w⁆)
    by group, map_mul, hkill (h.pow_mem_fix j hm)]

theorem T_eq_one (w g k : U) : ⁅k, ⁅g, psi t w⁆⁆ = 1 := by
  have hpp := h.psi_psi_mem_bSub hsqB
  have hcB : ∀ g : U, ⁅g, psi t w⁆ ∈ h.bSub := fun g =>
    h.commutator_left_mem_bSub_of_psi_mem (hpp w) g
  have hBAl : ∀ {b : U}, b ∈ h.bSub → ∀ m, ⁅m, b⁆ ∈ fixSubgroup t := fun hb m => by
    rw [← commutatorElement_inv]
    exact inv_mem (h.commutator_mem_fix_of_mem_bSub hb m)
  have hy4 : ∀ x : U, (y ^ 4) x = (y ^ 2) ((y ^ 2) x) := fun x => by
    rw [← MulAut.mul_apply, ← pow_add]
  have hy2 : ∀ x : U, (y ^ 2) x = y (y x) := fun x => by rw [pow_two, MulAut.mul_apply]
  have ha : ⁅(y ^ 4) k, ⁅g, psi t w⁆⁆ = y (y ⁅k, ⁅g, psi t w⁆⁆) := by
    rw [hy4, (h.weight_UB hsqB hncV (hcB g) _).1, (h.weight_UB hsqB hncV (hcB g) k).1]
  have hb : ∀ g' k' : U, ⁅k', ⁅(y ^ 4) g', psi t w⁆⁆ = y ⁅k', ⁅g', psi t w⁆⁆ := by
    intro g' k'
    have h1 := h.weight_A3 hsqB hncV w ((y ^ 2) g') k' 0
    have h2 := h.weight_A3 hsqB hncV w g' k' 1
    simp only [pow_zero, MulAut.one_apply, pow_one] at h1 h2
    rw [hy4, h1, h2, ← hy2, (h.weight_UB hsqB hncV (hcB g') k').2]
  have hc := h.commutator_comm_A3 hsqB hncV (hpp w)
  have h3 : y (y ⁅k, ⁅g, psi t w⁆⁆) = y ⁅k, ⁅g, psi t w⁆⁆ := by
    rw [← ha, hc, hb, ← hc]
  exact h.eq_one_of_y_fix (hBAl (hcB g) k) (y.injective h3)

theorem false_of_four : False := by
  have hA := fix_ne_top_of_commutator hncV
  obtain ⟨u, hu⟩ := h.exists_psi_not_mem_bSub hncV
  apply hu
  rw [← h.thetaHom_eq_one_iff hsqB hA, thetaHom_apply, psi_psi h.t_t, psi_psi h.t_t]
  have hpB : psi t (psi t u) ∈ h.bSub := h.psi_psi_mem_bSub hsqB u
  have hd := h.dlt_id hsqB hncV hpB u⁻¹
  rw [h.T_eq_one hsqB hncV u u⁻¹ u⁻¹, one_mul] at hd
  have htu : t u = u * psi t u := (mul_psi t u).symm
  have hcB : ⁅u⁻¹, psi t u⁆ ∈ h.bSub := h.commutator_left_mem_bSub_of_psi_mem hpB u⁻¹
  have hA2 : psi t (u ^ 2) ∈ fixSubgroup t := hsqB u
  have e : psi t (u ^ 2) = ⁅u⁻¹, psi t u⁆ * psi t u ^ 2 := by
    rw [psi, map_pow, htu]
    simp only [commutatorElement_def, pow_two]
    group
  rw [e] at hA2
  have h1 := h.mul_self_eq_one_of_mem_fix hA2
  generalize psi t u = p at hd hcB h1 ⊢
  have hcomm : ⁅u⁻¹, p⁆ * p ^ 2 = p ^ 2 * ⁅u⁻¹, p⁆ := h.bSub_comm hA hcB (hsqB p)
  rw [inv_pow, inv_inv, ← pow_mul]
  calc p ^ (2 * 2) = ⁅u⁻¹, p⁆ ^ 2 * p ^ (2 * 2) := by rw [hd, one_mul]
    _ = ⁅u⁻¹, p⁆ * p ^ 2 * (⁅u⁻¹, p⁆ * p ^ 2) := by
        rw [mul_assoc, ← mul_assoc (p ^ 2), ← hcomm, pow_mul, pow_two, pow_two, pow_two]
        group
    _ = 1 := h1



end FourLayers

end Finkelstein.Hyp

end CFSG.SeitzReduction.RankOne
