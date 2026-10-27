module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4L45

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec4_conj_tri [Finite G] (h36 : Asc82Lemma36) (h39 : Asc82Lemma39)
    (h42 : Asc82Lemma42) (h43 : Asc82Lemma43) (hf43c : Asc82Fact43Class)
    (hf214 : Asc82Fact214) (hin6 : Asc82FactInner6) (hk6 : Asc82FactK6)
    {t : G} {L S : Subgroup G} {z : G} (hctx : Sec4Ctx G t L S z) {s : G}
    (hs : ∃ h : G, s = h⁻¹ * t * h) (hsc : s ∈ centralizer ({t} : Set G)) (hst : s ≠ t) :
    (∃ h : G, h⁻¹ * t * h = t * z) ∨
      (∃ u : G, u ∈ L ∧ orderOf u = 2 ∧ InducesTypeSome L u 7 1 6 (-1) ∧ s = t * u) ∨
        InducesTypeSome L s 7 1 6 1 := by
  obtain ⟨hs2, hsN, hsnc⟩ := sec4_conj_data h36 h42 hctx.toSec4Setting hs hsc hst
  rcases hf214 G L (sec4_isOmega7Group hctx.toSec4Setting) s hs2 hsN hsnc with
    ⟨v, hv, hvs, hsv⟩ | ⟨α, hα⟩
  · exact Or.inl (sec4_case_i4 h43 hf43c hctx hs hsc hv hvs hsv)
  · rcases Int.units_eq_one_or α with rfl | rfl
    · exact Or.inr (Or.inr hα)
    · obtain ⟨u, c, huL, hu2, hu6, hcase, hsuc⟩ :=
        sec4_inner6_decomp h42 hin6 hctx.toSec4Setting hsc hs2 hsN hα
      rcases hcase with hc1 | hct
      · exfalso
        have hsL : s ∈ L := by rw [hsuc, hc1, mul_one]; exact huL
        exact sec4_conj_not_mem h36 h39 hk6 hctx.toSec4Setting hs hsL hs2 hα
      · refine Or.inr (Or.inl ⟨u, huL, hu2, hu6, ?_⟩)
        have hut : u * t = t * u :=
          (Subgroup.mem_centralizer_iff.mp (hctx.component.le huL) t
            (Set.mem_singleton t)).symm
        rw [hsuc, hct, hut]

theorem sec4_lemmaZ (h43 : Asc82Lemma43) {t : G} {L S : Subgroup G} {z : G} [Finite G]
    (hctx : Sec4Ctx G t L S z) (htz : ¬ ∃ h : G, h⁻¹ * t * h = t * z)
    {y w : G} (hy : ∃ h : G, y = h⁻¹ * t * h) (hw : ∃ h : G, w = h⁻¹ * z * h)
    (hwy : w ∈ centralizer ({y} : Set G)) (hyw : ∃ h : G, y * w = h⁻¹ * t * h) : False := by
  obtain ⟨h, rfl⟩ := hy
  obtain ⟨k, rfl⟩ := hw
  have hyC : (h⁻¹ * t * h) ∈ centralizer (CFSG.conjugate L h : Set G) :=
    sec4_t_mem_centralizer (hctx.conjugate h).toSec3Setting
  have hyy : (h⁻¹ * t * h) * (h⁻¹ * t * h) = 1 := by
    have h1 : orderOf (h⁻¹ * t * h) = 2 := by
      rw [orderOf_conjugate_eq, hctx.involution]
    have h2 := pow_orderOf_eq_one (h⁻¹ * t * h)
    rwa [h1, pow_two] at h2
  have hmem : (h⁻¹ * k)⁻¹ * (h⁻¹ * z * h) * (h⁻¹ * k) ∈
      centralizer ({h⁻¹ * t * h} : Set G) := by
    have he : (h⁻¹ * k)⁻¹ * (h⁻¹ * z * h) * (h⁻¹ * k) = k⁻¹ * z * k := by group
    rw [he]
    exact hwy
  have h43res := h43 G (h⁻¹ * t * h) (CFSG.conjugate L h) (CFSG.conjugate S h)
    (h⁻¹ * z * h) (hctx.conjugate h) (h⁻¹ * k) hmem
  rw [show (h⁻¹ * k)⁻¹ * (h⁻¹ * z * h) * (h⁻¹ * k) = k⁻¹ * z * k by group] at h43res
  rcases h43res with ⟨l, hl, hl_eq⟩ | ⟨l, hl, hl_eq⟩
  · obtain ⟨x, hx⟩ := hyw
    rw [hl_eq] at hx
    have hcomm : (h⁻¹ * t * h) * l = l * (h⁻¹ * t * h) :=
      (Subgroup.mem_centralizer_iff.mp hyC l hl).symm
    have hE' : l * (h⁻¹ * (t * z) * h) * l⁻¹ = x⁻¹ * t * x := by
      have h1 : (h⁻¹ * t * h) * (l * (h⁻¹ * z * h) * l⁻¹) =
          l * (h⁻¹ * (t * z) * h) * l⁻¹ := by
        rw [show (h⁻¹ * t * h) * (l * (h⁻¹ * z * h) * l⁻¹) =
            ((h⁻¹ * t * h) * l) * ((h⁻¹ * z * h) * l⁻¹) by group, hcomm]
        group
      rw [← h1]
      exact hx
    have hE : (h * l⁻¹)⁻¹ * (t * z) * (h * l⁻¹) = x⁻¹ * t * x := by
      rw [← hE']
      group
    exact htz ⟨x * (h * l⁻¹)⁻¹, sec4L45_conj_eq_mul_of_conj_eq hE⟩
  · obtain ⟨x, hx⟩ := hyw
    rw [hl_eq] at hx
    have hcomm : (h⁻¹ * t * h) * l = l * (h⁻¹ * t * h) :=
      (Subgroup.mem_centralizer_iff.mp hyC l hl).symm
    have hAs : l * (h⁻¹ * z * h) * l⁻¹ = x⁻¹ * t * x := by
      have h1 : (h⁻¹ * t * h) * (l * ((h⁻¹ * t * h) * (h⁻¹ * z * h)) * l⁻¹) =
          l * (h⁻¹ * z * h) * l⁻¹ := by
        rw [show (h⁻¹ * t * h) * (l * ((h⁻¹ * t * h) * (h⁻¹ * z * h)) * l⁻¹) =
            ((h⁻¹ * t * h) * l) * (((h⁻¹ * t * h) * (h⁻¹ * z * h)) * l⁻¹) by group,
          hcomm]
        rw [show (l * (h⁻¹ * t * h)) * (((h⁻¹ * t * h) * (h⁻¹ * z * h)) * l⁻¹) =
            l * (((h⁻¹ * t * h) * (h⁻¹ * t * h)) * (h⁻¹ * z * h)) * l⁻¹ by group]
        rw [hyy, one_mul]
      rw [← h1]
      exact hx
    have hEq : (h * l⁻¹ * x⁻¹)⁻¹ * z * (h * l⁻¹ * x⁻¹) = t := by
      have h2 : (h * l⁻¹ * x⁻¹)⁻¹ * z * (h * l⁻¹ * x⁻¹) =
          x * (l * (h⁻¹ * z * h) * l⁻¹) * x⁻¹ := by group
      rw [h2, hAs]
      group
    exact (sec4_t_not_conj_z h43 hctx (h * l⁻¹ * x⁻¹)) hEq

end CFSG.OddStandard.SmallF3.Omega
