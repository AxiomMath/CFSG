module

public import CFSG.CGT.Timmesfeld75.L2Swap
public import CFSG.CGT.Timmesfeld75.L2Real

public section

namespace CFSG.CGT.Timmesfeld75

open scoped MatrixGroups
open CFSG.Open

section Generic

theorem orderOf_conj_eq_orderOf {G : Type*} [Group G] (g z : G) :
    orderOf (g * z * g⁻¹) = orderOf z :=
  (SemiconjBy.orderOf_eq g (by unfold SemiconjBy; group)).symm

end Generic

section Matrix

variable {F : Type} [Field F] [CharP F 2]

theorem exists_involution_conj_utri_eq_ltri {s : F} (hs : s ≠ 0) :
    ∃ t : SL(2, F), t * t = 1 ∧ conjSubgroup t (utri F) = ltri F ∧ t 1 0 = s⁻¹ := by
  let a : Fˣ := Units.mk0 s⁻¹ (inv_ne_zero hs)
  have hτ : conjSubgroup (torusElt a) (utri F) = utri F :=
    mem_normalizer_iff_conjSubgroup_eq.1 (by rw [normalizer_utri]; exact torusElt_mem_borel a)
  refine ⟨wElt * torusElt a, ?_, ?_, ?_⟩
  · apply mul_self_eq_one_of_trace_eq_zero
    sl2_simp
    ring
  · rw [← conjSubgroup_conjSubgroup, hτ, conjSubgroup_wElt_utri]
  · sl2_simp
    simp [a]

theorem exists_swap_orderOf_three_utri {s : F} (hs : s ≠ 0) {g : SL(2, F)} (hg : g ∉ borel F) :
    ∃ t : SL(2, F), t * t = 1 ∧ conjSubgroup t (utri F) = conjSubgroup g (utri F) ∧
      orderOf (utriElt s * t) = 3 := by
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := exists_borel_mul_wElt_mul_borel hg
  have hbN : ∀ b ∈ borel F, conjSubgroup b (utri F) = utri F := fun b hb =>
    mem_normalizer_iff_conjSubgroup_eq.1 (by rw [normalizer_utri]; exact hb)
  have hmem : b₁⁻¹ * utriElt s * b₁ ∈ utri F := by
    simpa using conj_mem_utri_of_mem_borel ((borel F).inv_mem hb₁) (utriElt_mem_utri s)
  obtain ⟨s', hs'⟩ := mem_utri_iff.1 hmem
  have hs'0 : s' ≠ 0 := by
    rintro rfl
    rw [utriElt_zero] at hs'
    refine utriElt_ne_one hs ?_
    calc utriElt s = b₁ * (b₁⁻¹ * utriElt s * b₁) * b₁⁻¹ := by group
      _ = 1 := by rw [hs']; group
  obtain ⟨t₀, ht₀, hc₀, h10⟩ := exists_involution_conj_utri_eq_ltri hs'0
  refine ⟨b₁ * t₀ * b₁⁻¹, ?_, ?_, ?_⟩
  · calc b₁ * t₀ * b₁⁻¹ * (b₁ * t₀ * b₁⁻¹) = b₁ * (t₀ * t₀) * b₁⁻¹ := by group
      _ = 1 := by rw [ht₀]; group
  · rw [← conjSubgroup_conjSubgroup, ← conjSubgroup_conjSubgroup,
      hbN b₁⁻¹ ((borel F).inv_mem hb₁), hc₀, ← conjSubgroup_conjSubgroup,
      ← conjSubgroup_conjSubgroup, hbN b₂ hb₂, conjSubgroup_wElt_utri]
  · have e : utriElt s * (b₁ * t₀ * b₁⁻¹) = b₁ * (utriElt s' * t₀) * b₁⁻¹ := by
      rw [← hs']
      group
    have hc : t₀ 1 0 ≠ 0 := by
      rw [h10]
      exact inv_ne_zero hs'0
    have h3 := orderOf_utriElt_inv_mul_of_mul_self_eq_one ht₀ hc
    rw [h10, inv_inv] at h3
    rw [e, orderOf_conj_eq_orderOf, h3]

end Matrix

namespace IsL2Pair

variable {X : Type} [Group X] {S : Subgroup X} {q : ℕ}

theorem exists_swap_orderOf_three (h : IsL2Pair X S q) {b : X} (hb : b ∈ S) (hb1 : b ≠ 1) {g : X}
    (hg : conjSubgroup g S ≠ S) :
    ∃ t : X, t * t = 1 ∧ conjSubgroup t S = conjSubgroup g S ∧ orderOf (b * t) = 3 := by
  obtain ⟨F, _, _, _, e, -, hmap, -, hmemS, hmemN⟩ := h.exists_data
  obtain ⟨s, hs⟩ := mem_utri_iff.1 ((hmemS b).1 hb)
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [utriElt_zero] at hs
    exact hb1 (e.injective (hs.trans (map_one e).symm))
  have hge : e g ∉ borel F := fun hb' =>
    hg (mem_normalizer_iff_conjSubgroup_eq.1 ((hmemN g).2 hb'))
  obtain ⟨t', ht', hc', hord⟩ := exists_swap_orderOf_three_utri hs0 hge
  have hinj : Function.Injective e.toMonoidHom := e.injective
  refine ⟨e.symm t', e.injective ?_, Subgroup.map_injective hinj ?_, ?_⟩
  · rw [map_mul, MulEquiv.apply_symm_apply, ht', map_one]
  · rw [map_conjSubgroup_mulEquiv, map_conjSubgroup_mulEquiv, hmap, MulEquiv.apply_symm_apply, hc']
  · calc orderOf (b * e.symm t') = orderOf (e (b * e.symm t')) :=
          (orderOf_injective e.toMonoidHom hinj _).symm
      _ = orderOf (utriElt s * t') := by rw [map_mul, hs, MulEquiv.apply_symm_apply]
      _ = 3 := hord

end IsL2Pair

end CFSG.CGT.Timmesfeld75
