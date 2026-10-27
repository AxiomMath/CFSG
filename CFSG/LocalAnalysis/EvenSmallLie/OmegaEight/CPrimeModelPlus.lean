module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.CPrimeModelPerm

public section

namespace CFSG.EvenSmallLie.OmegaEight.CPrimeModel

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.Stage1.Model
open OmegaEight (gen omegaT autT stab0 res0)

theorem sq_mem_iff {x w : Equiv.Perm (Fin 360)} (hw : w ∈ autT) (hxw : x * w⁻¹ ∈ omegaT) :
    x * x ∈ omegaT ↔ w * w ∈ omegaT := by
  have hc : w * (x * w⁻¹) * w⁻¹ ∈ omegaT := (OmegaEight.conj_mem_omegaT hw).1 hxw
  have hy := mul_mem hxw hc
  have e : x * x = x * w⁻¹ * (w * (x * w⁻¹) * w⁻¹) * (w * w) := by group
  rw [e]
  constructor
  · intro h
    rw [← inv_mul_cancel_left (x * w⁻¹ * (w * (x * w⁻¹) * w⁻¹)) (w * w)]
    exact mul_mem (inv_mem hy) h
  · intro h
    exact mul_mem hy h

theorem inv_mul_mem_of_conj {a w g : Equiv.Perm (Fin 360)} (ha : a ∈ autT)
    (haw : a * w * a⁻¹ = gen 9) (hgw : g * w⁻¹ ∈ omegaT) :
    (a * g * a⁻¹)⁻¹ * gen 9 ∈ omegaT := by
  have h9 : gen 9 ∈ autT := OmegaEight.gen_mem_autT (by norm_num)
  have h1 : a * (g * w⁻¹) * a⁻¹ ∈ omegaT := (OmegaEight.conj_mem_omegaT ha).1 hgw
  have e : (a * g * a⁻¹)⁻¹ * gen 9 =
      (gen 9)⁻¹ * (a * (g * w⁻¹) * a⁻¹)⁻¹ * (gen 9)⁻¹⁻¹ := by
    rw [← haw]
    group
  rw [e]
  exact (OmegaEight.conj_mem_omegaT (inv_mem h9)).1 (inv_mem h1)

theorem gen9_mul_self : gen 9 * gen 9 = 1 :=
  eq_of_eqA (rep_compA (OmegaEight.rep_gen (by norm_num)) (OmegaEight.rep_gen (by norm_num)))
    rep_idA coset_parts.2.2.2.2.2.2.1

theorem gen9_mem_stab0 : gen 9 ∈ stab0 := by
  intro p
  have h := coset_parts.2.2.2.2.2.1 p p.2
  rw [OmegaEight.rep_gen (by norm_num : 9 < 10) p] at h
  exact h.symm

theorem wPerm_zero : wPerm 0 = 1 := (rep_wPerm (by norm_num)).1.unique rep_idA

theorem wPerm_one : wPerm 1 = gen 9 :=
  (rep_wPerm (by norm_num)).1.unique (OmegaEight.rep_gen (by norm_num))

theorem exists_conj_outer_plus {g : Equiv.Perm (Fin 360)} (hgA : g ∈ autT) (hgΩ : g ∉ omegaT)
    (hg2 : g * g = 1) : ∃ a ∈ autT, (a * g * a⁻¹)⁻¹ * gen 9 ∈ omegaT := by
  obtain ⟨j, hj, hgw⟩ := exists_coset_plus hgA
  have hP := coset_parts
  have hsq : wPerm j * wPerm j ∈ omegaT :=
    (sq_mem_iff (wPerm_mem hj) hgw).1 (by rw [hg2]; exact one_mem _)
  have conj23 : wPerm 2 * wPerm 3 * (wPerm 2)⁻¹ = gen 9 :=
    eq_of_eqA (rep_compA (rep_compA (rep_wPerm (by norm_num)).1 (rep_wPerm (by norm_num)).1)
      (rep_wPerm (by norm_num)).2) (OmegaEight.rep_gen (by norm_num)) hP.2.2.2.2.2.2.2.1
  have conj45 : wPerm 4 * wPerm 5 * (wPerm 4)⁻¹ = gen 9 :=
    eq_of_eqA (rep_compA (rep_compA (rep_wPerm (by norm_num)).1 (rep_wPerm (by norm_num)).1)
      (rep_wPerm (by norm_num)).2) (OmegaEight.rep_gen (by norm_num)) hP.2.2.2.2.2.2.2.2
  interval_cases j
  · exact absurd (by simpa [wPerm_zero] using hgw) hgΩ
  · exact ⟨1, one_mem _, inv_mul_mem_of_conj (one_mem _) (by simp [wPerm_one]) hgw⟩
  · have h := (mem_omegaT_iff (rep_compA (rep_wPerm (by norm_num : 2 < 6)).1
      (rep_wPerm (by norm_num : 2 < 6)).1)).1 hsq
    rw [hP.2.2.1] at h
    exact absurd h (by decide)
  · exact ⟨wPerm 2, wPerm_mem (by norm_num), inv_mul_mem_of_conj (wPerm_mem (by norm_num))
      conj23 hgw⟩
  · have h := (mem_omegaT_iff (rep_compA (rep_wPerm (by norm_num : 4 < 6)).1
      (rep_wPerm (by norm_num : 4 < 6)).1)).1 hsq
    rw [hP.2.2.2.1] at h
    exact absurd h (by decide)
  · exact ⟨wPerm 4, wPerm_mem (by norm_num), inv_mul_mem_of_conj (wPerm_mem (by norm_num))
      conj45 hgw⟩

theorem mem_or_of_lt {x : Equiv.Perm (Fin 360)} (hxA : x ∈ autT)
    (hx0 : ((x ⟨0, by norm_num⟩ : Fin 360) : ℕ) < 120) :
    x ∈ omegaT ∨ x * (gen 9)⁻¹ ∈ omegaT := by
  obtain ⟨j, hj, hxw⟩ := exists_coset_plus hxA
  have hω := OmegaEight.omegaT_le_stab0 hxw
  have hw0 : ((wPerm j ⟨0, by norm_num⟩ : Fin 360) : ℕ) < 120 := by
    have h1 := (hω (wPerm j ⟨0, by norm_num⟩)).2
    have e : (x * (wPerm j)⁻¹) (wPerm j ⟨0, by norm_num⟩) = x ⟨0, by norm_num⟩ := by
      simp [Equiv.Perm.mul_apply]
    rw [e] at h1
    exact h1 hx0
  have hlt : j < 2 := by
    by_contra hge
    have h5 := coset_parts.2.2.2.2.1 (j - 2) (by omega)
    rw [show j - 2 + 2 = j by omega, (rep_wPerm hj).1.apply (by norm_num : 0 < 360)] at h5
    omega
  interval_cases j
  · left
    simpa [wPerm_zero] using hxw
  · right
    rwa [wPerm_one] at hxw

theorem psiTMp_zero : psiTMp (0 : V6) = 1 := by
  have h := psiTM_add (ε := .plus) 0 0
  rw [add_zero] at h
  exact (mul_eq_left.1 h.symm)

theorem psiTMp_injective : Function.Injective psiTMp := by
  intro v w e
  have h1 := restrict_psiTMp v
  have h2 := restrict_psiTMp w
  have h3 : (⟨psiTMp v, psiTMp_mem_omegaT v⟩ : omegaT) = ⟨psiTMp w, psiTMp_mem_omegaT w⟩ :=
    Subtype.ext e
  rw [h3, h2] at h1
  exact psiM_injective (congrArg Subtype.val h1).symm

theorem apply_zero_lt {x : Equiv.Perm (Fin 360)}
    (hx : ∀ v, ∃ w, x⁻¹ * psiTMp v * x = psiTMp w) :
    ((x ⟨0, by norm_num⟩ : Fin 360) : ℕ) < 120 := by
  have hz0 : (⟨0, by decide⟩ : Fin (aDeg .plus)) ∈ Rset .plus := aBase_mem_R zero_mem_aBase
  have hxR : x ⟨0, by norm_num⟩ ∈ Rset .plus := by
    intro v hv e
    obtain ⟨w, hw⟩ := hx v
    have hw0 : psiTM .plus w ⟨0, by decide⟩ = ⟨0, by decide⟩ := by
      change psiTMp w ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩
      rw [← hw, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
      change x⁻¹ (psiTM .plus v (x ⟨0, by norm_num⟩)) = ⟨0, by norm_num⟩
      rw [e]
      simp
    have hw' : w = 0 := by
      by_contra h
      exact hz0 w h hw0
    rw [hw', psiTMp_zero] at hw
    have hv1 : psiTMp v = 1 := by
      have := congrArg (fun g => x * g * x⁻¹) hw
      simpa [mul_assoc] using this
    exact hz0 v hv (by change psiTMp v ⟨0, by norm_num⟩ = _; rw [hv1]; rfl)
  obtain ⟨v, hv⟩ := exists_psiTM_apply hxR
  have hmem := OmegaEight.omegaT_le_stab0 (psiTMp_mem_omegaT v)
  have h1 := (hmem ⟨0, by norm_num⟩).1 (by norm_num)
  change ((psiTM .plus v ⟨0, by decide⟩ : Fin 360) : ℕ) < 120 at h1
  rw [hv] at h1
  exact h1

theorem mem_of_normalizes_plus {x : Equiv.Perm (Fin 360)} (hxA : x ∈ autT)
    (hx : ∀ v, ∃ w, x * psiTMp v * x⁻¹ = psiTMp w) : x ∈ omegaT ∨ x * (gen 9)⁻¹ ∈ omegaT := by
  refine mem_or_of_lt hxA (apply_zero_lt fun v => ?_)
  choose f hf using hx
  have hinj : Function.Injective f := fun v w e => psiTMp_injective (by
    have h1 := hf v
    rw [e, ← hf w] at h1
    exact mul_left_cancel (mul_right_cancel h1))
  obtain ⟨u, hu⟩ := Finite.surjective_of_injective hinj v
  refine ⟨u, ?_⟩
  rw [← hu, ← hf u]
  group

theorem not_normalizes_of_pow_three {a : Equiv.Perm (Fin 360)} (haA : a ∈ autT)
    (ha : a ∉ omegaT) (ha3 : a ^ 3 ∈ omegaT) :
    ¬ ∀ v, ∃ w, a * psiTMp v * a⁻¹ = psiTMp w := by
  intro h
  rcases mem_of_normalizes_plus haA h with h1 | h1
  · exact ha h1
  · apply ha
    have h2 : a * a ∈ omegaT := by
      rw [sq_mem_iff (OmegaEight.gen_mem_autT (by norm_num)) h1, gen9_mul_self]
      exact one_mem _
    have e : a = a ^ 3 * (a * a)⁻¹ := by group
    rw [e]
    exact mul_mem ha3 (inv_mem h2)

theorem rep_res0 {g : Equiv.Perm (Fin 360)} (hg : g ∈ stab0) {t : Array ℕ} (h : Rep 360 t g) :
    Rep 120 (OmegaEight.copy0Arr t) (res0 ⟨g, hg⟩) := by
  intro j
  rw [OmegaEight.copy0Arr_getElem! _ j.2, OmegaEight.res0_apply_val]
  exact h ⟨j, by omega⟩

theorem sig_plus_eq : sig .plus = res0 ⟨gen 9, gen9_mem_stab0⟩ :=
  (rep_sig (ε := .plus)).1.unique (rep_res0 gen9_mem_stab0 (OmegaEight.rep_gen (by norm_num)))

end CFSG.EvenSmallLie.OmegaEight.CPrimeModel
