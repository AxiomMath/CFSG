module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneFinkelsteinNonabelianSpecial

public section

namespace CFSG.SeitzReduction.RankOne

open CFSG.ComponentClassification.GMS78.Finkelstein
open scoped commutatorElement

namespace Finkelstein

variable {G : Type} [Group G]

theorem commutator_mul_left_of_central {a b c : G} (hc : ∀ g : G, g * ⁅b, c⁆ = ⁅b, c⁆ * g) :
    ⁅a * b, c⁆ = ⁅b, c⁆ * ⁅a, c⁆ := by
  calc ⁅a * b, c⁆ = a * ⁅b, c⁆ * (c * a⁻¹ * c⁻¹) := by
        simp only [commutatorElement_def]; group
    _ = ⁅b, c⁆ * ⁅a, c⁆ := by rw [hc a, commutatorElement_def]; group

theorem commutator_mul_right_of_central {a b c : G} (hc : ∀ g : G, g * ⁅a, c⁆ = ⁅a, c⁆ * g) :
    ⁅a, b * c⁆ = ⁅a, b⁆ * ⁅a, c⁆ := by
  calc ⁅a, b * c⁆ = ⁅a, b⁆ * (b * ⁅a, c⁆ * b⁻¹) := by
        simp only [commutatorElement_def]; group
    _ = ⁅a, b⁆ * ⁅a, c⁆ := by rw [hc b, mul_inv_cancel_right]

namespace Hyp

variable {U : Type} [Group U] [Finite U] {n : ℕ} {t y : MulAut U} (h : Finkelstein.Hyp U n t y)
include h

theorem central_of_mem_fix {a : U} (ha : a ∈ fixSubgroup t) : ∀ g : U, g * a = a * g :=
  h.mem_center_of_mem_fix ha

theorem conj_mem_bSub {b : U} (hb : b ∈ h.bSub) (g : U) : g * b * g⁻¹ ∈ h.bSub := by
  have h1 : g * b * g⁻¹ = ⁅g, b⁆ * b := by simp only [commutatorElement_def]; group
  rw [h1]
  refine mul_mem (h.fix_le_bSub ?_) hb
  rw [← inv_mem_iff, commutatorElement_inv]
  exact h.commutator_mem_fix_of_mem_bSub hb g

theorem inv_mul_mem_fix_of_psi_eq {b b' : U} (hb : b ∈ h.bSub) (he : psi t b = psi t b') :
    b⁻¹ * b' ∈ fixSubgroup t := by
  rw [← psi_eq_one_iff, h.psi_mul_of_mem (by rw [h.psi_inv_of_mem hb]; exact inv_mem hb),
    h.psi_inv_of_mem hb, he, inv_mul_cancel]

section FourLayers

variable (hsqB : ∀ u : U, u ^ 2 ∈ h.bSub)
include hsqB

theorem psi_psi_mem_bSub (u : U) : psi t (psi t u) ∈ h.bSub := by
  rw [psi_psi h.t_t]
  exact inv_mem (hsqB _)

theorem quot_sq_mem_fix [(fixSubgroup t).Normal] (v : U ⧸ fixSubgroup t) :
    v ^ 2 ∈ fixSubgroup (quotAut t (map_fix_of_comm (s := t) rfl)) := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective v
  rw [← QuotientGroup.mk_pow, h.quot_mk_mem_fix_iff]
  exact hsqB u

theorem psi_psi_mul_mod (hA : fixSubgroup t ≠ ⊤) (u v : U) :
    (psi t (psi t u) * psi t (psi t v))⁻¹ * psi t (psi t (u * v)) ∈ fixSubgroup t := by
  have := h.fix_normal
  have hV := h.quot hA
  have h1 := hV.psi_psi_mul_of_sq (h.quot_sq_mem_fix hsqB) (u : U ⧸ fixSubgroup t) v
  rw [← QuotientGroup.mk_mul, psi_quot_mk, psi_quot_mk, psi_quot_mk, psi_quot_mk, psi_quot_mk,
    psi_quot_mk, ← QuotientGroup.mk_mul] at h1
  exact QuotientGroup.eq.mp h1.symm

@[expose] noncomputable def thetaHom (hA : fixSubgroup t ≠ ⊤) : U →* U where
  toFun u := psi t (psi t (psi t u))
  map_one' := by
    show psi t (psi t (psi t 1)) = 1
    simp only [psi_eq_one_iff.mpr (one_mem _)]
  map_mul' u v := by
    show psi t (psi t (psi t (u * v))) =
      psi t (psi t (psi t u)) * psi t (psi t (psi t v))
    rw [show psi t (psi t (u * v)) = psi t (psi t u) * psi t (psi t v) *
        ((psi t (psi t u) * psi t (psi t v))⁻¹ * psi t (psi t (u * v))) by group,
      h.psi_mul_fix (h.psi_psi_mul_mod hsqB hA u v),
      h.psi_mul_of_mem (h.psi_psi_mem_bSub hsqB u)]

theorem thetaHom_apply (hA : fixSubgroup t ≠ ⊤) (u : U) :
    h.thetaHom hsqB hA u = psi t (psi t (psi t u)) :=
  rfl

theorem thetaHom_mem (hA : fixSubgroup t ≠ ⊤) (u : U) :
    h.thetaHom hsqB hA u ∈ fixSubgroup t :=
  h.psi_psi_mem_bSub hsqB u

theorem thetaHom_y (hA : fixSubgroup t ≠ ⊤) (u : U) :
    h.thetaHom hsqB hA (y u) = y (h.thetaHom hsqB hA u) := by
  simp only [thetaHom_apply, psi_map_of_comm h.comm]

theorem thetaHom_eq_one_iff (hA : fixSubgroup t ≠ ⊤) (u : U) :
    h.thetaHom hsqB hA u = 1 ↔ psi t u ∈ h.bSub :=
  psi_eq_one_iff

omit h hsqB [Finite U] in
theorem fix_ne_top_of_commutator (hncV : ∃ u v : U, ⁅u, v⁆ ∉ fixSubgroup t) :
    fixSubgroup t ≠ ⊤ := by
  obtain ⟨u, v, huv⟩ := hncV
  intro hA
  exact huv (hA ▸ Subgroup.mem_top _)

omit hsqB in
theorem exists_psi_not_mem_bSub (hncV : ∃ u v : U, ⁅u, v⁆ ∉ fixSubgroup t) :
    ∃ u : U, psi t u ∉ h.bSub := by
  have hA := fix_ne_top_of_commutator hncV
  by_contra hall
  push Not at hall
  obtain ⟨u, v, huv⟩ := hncV
  apply huv
  have := h.fix_normal
  have hV := h.quot hA
  have hcV : (u : U ⧸ fixSubgroup t) * v = v * u := by
    have hu := (h.quot_mk_mem_bSub_iff hA u).mpr (hall u)
    have hv := (h.quot_mk_mem_bSub_iff hA v).mpr (hall v)
    by_cases hAV : fixSubgroup (quotAut t (map_fix_of_comm (s := t) rfl)) = ⊤
    · exact hV.mem_center_of_mem_fix (hAV ▸ Subgroup.mem_top _) _
    · exact hV.bSub_comm hAV hu hv
  rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
    commutatorElement_eq_one_iff_mul_comm]
  exact hcV

theorem exists_psi_psi_mod (hncV : ∃ u v : U, ⁅u, v⁆ ∉ fixSubgroup t) {b : U}
    (hb : b ∈ h.bSub) : ∃ w : U, (psi t (psi t w))⁻¹ * b ∈ fixSubgroup t := by
  have hA := fix_ne_top_of_commutator hncV
  have := h.fix_normal
  have hV := h.quot hA
  have hsqV := h.quot_sq_mem_fix hsqB
  set θV := hV.topHom hsqV with hθV
  have hθVmk : ∀ w : U, θV (w : U ⧸ fixSubgroup t) = ((psi t (psi t w) : U) : U ⧸ fixSubgroup t) :=
    fun w => by rw [hθV, topHom_apply, psi_quot_mk, psi_quot_mk]
  have hle : fixSubgroup (quotAut t (map_fix_of_comm (s := t) rfl)) ≤ θV.range := by
    refine hV.fix_le_of_invariant (fun x hx => ?_) (fun x hx => ?_) ?_
    · obtain ⟨v, rfl⟩ := hx
      rw [show (quotAut t (map_fix_of_comm (s := t) rfl)) (θV v) = θV v from
        hV.topHom_mem hsqV v]
      exact ⟨v, rfl⟩
    · obtain ⟨v, rfl⟩ := hx
      exact ⟨_, hV.topHom_y hsqV v⟩
    · obtain ⟨u₀, hu₀⟩ := h.exists_psi_not_mem_bSub hncV
      intro hbot
      have h1 : θV (u₀ : U ⧸ fixSubgroup t) ∈ θV.range := ⟨_, rfl⟩
      rw [hbot, Subgroup.mem_bot, hθVmk, QuotientGroup.eq_one_iff] at h1
      exact hu₀ h1
  obtain ⟨v, hv⟩ := hle ((h.quot_mk_mem_fix_iff b).mpr hb)
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective v
  rw [hθVmk] at hv
  exact ⟨w, QuotientGroup.eq.mp hv⟩

theorem exists_psi_mod (hncV : ∃ u v : U, ⁅u, v⁆ ∉ fixSubgroup t) {x : U}
    (hx : psi t x ∈ h.bSub) : ∃ w : U, (psi t w)⁻¹ * x ∈ h.bSub := by
  obtain ⟨w, hw⟩ := h.exists_psi_psi_mod hsqB hncV hx
  refine ⟨w, ?_⟩
  have hta : t (psi t w) = (psi t w)⁻¹ := t_psi h.t_t w
  have hpp : psi t (psi t w) = (psi t w * psi t w)⁻¹ := by rw [psi_psi h.t_t w, pow_two]
  have hbB : (psi t w * psi t w)⁻¹ ∈ h.bSub := hpp ▸ h.psi_psi_mem_bSub hsqB w
  rw [hpp, inv_inv] at hw
  generalize psi t w = a at hta hbB hw ⊢
  have e1 : psi t (a⁻¹ * x) = (a * a) * ⁅(a * a)⁻¹, x⁻¹⁆ * psi t x := by
    simp only [psi, map_mul, map_inv, hta, commutatorElement_def]
    group
    simp only [zpow_two, mul_assoc]
  have hc : ⁅(a * a)⁻¹, x⁻¹⁆ ∈ fixSubgroup t := h.commutator_mem_fix_of_mem_bSub hbB _
  rw [mem_bSub, e1, h.mem_center_of_mem_fix hc (a * a), mul_assoc]
  exact mul_mem hc hw

end FourLayers

end Hyp

end Finkelstein

end CFSG.SeitzReduction.RankOne
