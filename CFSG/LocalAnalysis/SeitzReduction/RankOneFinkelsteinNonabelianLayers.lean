module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneFinkelsteinLayer

public section

namespace CFSG.SeitzReduction.RankOne

open CFSG.ComponentClassification.GMS78.Finkelstein
open scoped commutatorElement

namespace Finkelstein

variable {U : Type} [Group U] {n : ℕ} {t y : MulAut U}

theorem t_psi (ht : ∀ u, t (t u) = u) (u : U) : t (psi t u) = (psi t u)⁻¹ := by
  unfold psi
  rw [map_mul, map_inv, ht, mul_inv_rev, inv_inv]

theorem psi_psi (ht : ∀ u, t (t u) = u) (u : U) : psi t (psi t u) = (psi t u ^ 2)⁻¹ := by
  rw [psi, t_psi ht, pow_two, mul_inv_rev]

namespace Hyp

variable [Finite U] (h : Hyp U n t y)
include h

omit h in
theorem psi_quot_mk [(fixSubgroup t).Normal] (u : U) :
    psi (quotAut t (map_fix_of_comm (s := t) rfl)) (u : U ⧸ fixSubgroup t) =
      ((psi t u : U) : U ⧸ fixSubgroup t) := by
  rw [psi, quotAut_mk, psi, QuotientGroup.mk_mul, QuotientGroup.mk_inv]

theorem quot_mk_mem_fix_iff [(fixSubgroup t).Normal] (u : U) :
    (u : U ⧸ fixSubgroup t) ∈ fixSubgroup (quotAut t (map_fix_of_comm (s := t) rfl)) ↔
      u ∈ h.bSub :=
  quotAut_mk_eq_iff u

theorem commutator_mem_fix_of_mem_bSub {b : U} (hb : b ∈ h.bSub) (g : U) :
    ⁅b, g⁆ ∈ fixSubgroup t := by
  by_cases hA : fixSubgroup t = ⊤
  · rw [hA]
    exact Subgroup.mem_top _
  have := h.fix_normal
  have hV := h.quot hA
  have hbV := (h.quot_mk_mem_fix_iff b).mpr hb
  have hc := hV.mem_center_of_mem_fix hbV (g : U ⧸ fixSubgroup t)
  rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
    commutatorElement_eq_one_iff_mul_comm]
  exact hc.symm

theorem quot_mk_mem_bSub_iff (hA : fixSubgroup t ≠ ⊤) [(fixSubgroup t).Normal] (u : U) :
    (u : U ⧸ fixSubgroup t) ∈ (h.quot hA).bSub ↔ psi t u ∈ h.bSub := by
  rw [(h.quot hA).mem_bSub, psi_quot_mk, h.quot_mk_mem_fix_iff]

theorem commutator_mem_bSub_of_psi_mem {x : U} (hx : psi t x ∈ h.bSub) (g : U) :
    ⁅x, g⁆ ∈ h.bSub := by
  by_cases hA : fixSubgroup t = ⊤
  · rw [mem_bSub, hA]
    exact Subgroup.mem_top _
  have := h.fix_normal
  have hV := h.quot hA
  have hxV := (h.quot_mk_mem_bSub_iff hA x).mpr hx
  have h1 := hV.commutator_mem_fix_of_mem_bSub hxV (g : U ⧸ fixSubgroup t)
  rw [← QuotientGroup.mk'_apply, ← QuotientGroup.mk'_apply, ← map_commutatorElement,
    QuotientGroup.mk'_apply] at h1
  exact (h.quot_mk_mem_fix_iff _).mp h1

theorem commutator_mem_fix_of_psi_mem {x x' : U} (hx : psi t x ∈ h.bSub)
    (hx' : psi t x' ∈ h.bSub) : ⁅x, x'⁆ ∈ fixSubgroup t := by
  by_cases hA : fixSubgroup t = ⊤
  · rw [hA]
    exact Subgroup.mem_top _
  have := h.fix_normal
  have hV := h.quot hA
  have hxV := (h.quot_mk_mem_bSub_iff hA x).mpr hx
  have hxV' := (h.quot_mk_mem_bSub_iff hA x').mpr hx'
  have hc : (x : U ⧸ fixSubgroup t) * x' = x' * x := by
    by_cases hAV : fixSubgroup (quotAut t (map_fix_of_comm (s := t) rfl)) = ⊤
    · exact hV.mem_center_of_mem_fix (hAV ▸ Subgroup.mem_top _) _
    · exact hV.bSub_comm hAV hxV hxV'
  rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
    commutatorElement_eq_one_iff_mul_comm]
  exact hc

end Hyp

end Finkelstein

end CFSG.SeitzReduction.RankOne
