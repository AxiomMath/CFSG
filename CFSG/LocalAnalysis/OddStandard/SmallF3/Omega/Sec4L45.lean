module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Conj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4NotConj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4L45Aux

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec4_conj_data [Finite G] (h36 : Asc82Lemma36) (h42 : Asc82Lemma42) {t : G}
    {L : Subgroup G} (hctx : Sec4Setting G t L) {s : G} (hs : ∃ h : G, s = h⁻¹ * t * h)
    (hsc : s ∈ centralizer ({t} : Set G)) (hst : s ≠ t) :
    orderOf s = 2 ∧ s ∈ normalizer (L : Set G) ∧ s ∉ centralizer (L : Set G) := by
  obtain ⟨h, rfl⟩ := hs
  refine ⟨?_, sec4_mem_normalizer h36 hctx.toSec3SettingLB (h⁻¹ * t * h) hsc, ?_⟩
  · rw [orderOf_conjugate_eq, hctx.involution]
  · intro hscL
    have hcomm : (h⁻¹ * t * h) * t = t * (h⁻¹ * t * h) :=
      (Subgroup.mem_centralizer_iff.mp hsc t (Set.mem_singleton t)).symm
    have hs2 : (h⁻¹ * t * h) * (h⁻¹ * t * h) = 1 := by
      have h1 : orderOf (h⁻¹ * t * h) = 2 := by
        rw [orderOf_conjugate_eq, hctx.involution]
      have h2 := pow_orderOf_eq_one (h⁻¹ * t * h)
      rwa [h1, pow_two] at h2
    have htC : t ∈ centralizer (L : Set G) := sec4_t_mem_centralizer hctx.toSec3Setting
    have hcyc : ∀ P : Sylow 2 (centralizer (L : Set G)),
        IsCyclic (P : Subgroup (centralizer (L : Set G))) := h42 G t L hctx
    have hcase := sec4_eq_of_commute (H := centralizer (L : Set G)) hcyc hscL htC
      hs2 hctx.involution hcomm
    rcases hcase with h1 | h1
    · have h' : orderOf (h⁻¹ * t * h) = 1 := by rw [h1, orderOf_one]
      rw [orderOf_conjugate_eq, hctx.involution] at h'
      exact absurd h' (by decide)
    · exact hst h1

theorem sec4_case_i4 [Finite G] (h43 : Asc82Lemma43) (hf43c : Asc82Fact43Class) {t : G}
    {L S : Subgroup G} {z : G} (hctx : Sec4Ctx G t L S z) {s : G}
    (hs : ∃ h : G, s = h⁻¹ * t * h) (hsc : s ∈ centralizer ({t} : Set G)) {v : G}
    (hv : IsI4PlusIn L v) (hvs : v ∈ centralizer ({s} : Set G))
    (hsv : s * v ∈ conjClassIn L s) : ∃ h : G, h⁻¹ * t * h = t * z := by
  obtain ⟨h, rfl⟩ := hs
  have hL : IsOmega7Group L := sec4_isOmega7Group hctx.toSec4Setting
  obtain ⟨k, hkL, hk_eq⟩ := hf43c G L hL z v hctx.pocket hv
  have hkey : (h⁻¹ * k⁻¹)⁻¹ * (h⁻¹ * z * h) * (h⁻¹ * k⁻¹) = v := by
    rw [hk_eq]
    group
  have h43res := h43 G (h⁻¹ * t * h) (CFSG.conjugate L h) (CFSG.conjugate S h)
    (h⁻¹ * z * h) (hctx.conjugate h) (h⁻¹ * k⁻¹) (by rw [hkey]; exact hvs)
  rw [hkey] at h43res
  obtain ⟨l, hl, hl_eq⟩ := hsv
  have hsc' : (h⁻¹ * t * h) ∈ centralizer (CFSG.conjugate L h : Set G) :=
    sec4_t_mem_centralizer (hctx.conjugate h).toSec3Setting
  have hs2 : (h⁻¹ * t * h) * (h⁻¹ * t * h) = 1 := by
    have h1 : orderOf (h⁻¹ * t * h) = 2 := by
      rw [orderOf_conjugate_eq, hctx.involution]
    have h2 := pow_orderOf_eq_one (h⁻¹ * t * h)
    rwa [h1, pow_two] at h2
  rcases h43res with ⟨l', hl', hl'eq⟩ | ⟨l', hl', hl'eq⟩
  · have hs_comm_l' : (h⁻¹ * t * h) * l' = l' * (h⁻¹ * t * h) :=
      (Subgroup.mem_centralizer_iff.mp hsc' l' hl').symm
    have hEraw : l' * ((h⁻¹ * t * h) * (h⁻¹ * z * h)) * l'⁻¹ =
        l * (h⁻¹ * t * h) * l⁻¹ := by
      have hsw : (h⁻¹ * t * h) * (l' * (h⁻¹ * z * h) * l'⁻¹) =
          l' * ((h⁻¹ * t * h) * (h⁻¹ * z * h)) * l'⁻¹ := by
        rw [show (h⁻¹ * t * h) * (l' * (h⁻¹ * z * h) * l'⁻¹) =
            ((h⁻¹ * t * h) * l') * ((h⁻¹ * z * h) * l'⁻¹) by group]
        rw [hs_comm_l']
        group
      rw [← hsw, ← hl'eq]
      exact hl_eq
    have hL' : l' * ((h⁻¹ * t * h) * (h⁻¹ * z * h)) * l'⁻¹ =
        (h * l'⁻¹)⁻¹ * (t * z) * (h * l'⁻¹) := by group
    have hR' : l * (h⁻¹ * t * h) * l⁻¹ = (h * l⁻¹)⁻¹ * t * (h * l⁻¹) := by group
    have hE : (h * l'⁻¹)⁻¹ * (t * z) * (h * l'⁻¹) =
        (h * l⁻¹)⁻¹ * t * (h * l⁻¹) := by
      rw [← hL', ← hR']
      exact hEraw
    exact ⟨(h * l⁻¹) * (h * l'⁻¹)⁻¹, sec4L45_conj_eq_mul_of_conj_eq hE⟩
  · have hs_comm_l' : (h⁻¹ * t * h) * l' = l' * (h⁻¹ * t * h) :=
      (Subgroup.mem_centralizer_iff.mp hsc' l' hl').symm
    have hsv_eq : (h⁻¹ * t * h) * v = l' * (h⁻¹ * z * h) * l'⁻¹ := by
      rw [hl'eq]
      calc (h⁻¹ * t * h) * (l' * ((h⁻¹ * t * h) * (h⁻¹ * z * h)) * l'⁻¹)
          = ((h⁻¹ * t * h) * l') * (((h⁻¹ * t * h) * (h⁻¹ * z * h)) * l'⁻¹) := by
            group
        _ = (l' * (h⁻¹ * t * h)) * (((h⁻¹ * t * h) * (h⁻¹ * z * h)) * l'⁻¹) := by
            rw [hs_comm_l']
        _ = l' * (((h⁻¹ * t * h) * (h⁻¹ * t * h)) * (h⁻¹ * z * h)) * l'⁻¹ := by
            group
        _ = l' * ((1 : G) * (h⁻¹ * z * h)) * l'⁻¹ := by rw [hs2]
        _ = l' * (h⁻¹ * z * h) * l'⁻¹ := by group
    have hAs : l' * (h⁻¹ * z * h) * l'⁻¹ = l * (h⁻¹ * t * h) * l⁻¹ := by
      rw [← hsv_eq]
      exact hl_eq
    have hz_eq := sec4L45_eq_conj_of_conj_eq hAs
    have hAeq : (h * l'⁻¹ * l * h⁻¹)⁻¹ * z * (h * l'⁻¹ * l * h⁻¹) = t := by
      rw [hz_eq]
      group
    exact absurd hAeq (sec4_t_not_conj_z h43 hctx (h * l'⁻¹ * l * h⁻¹))

theorem sec4_inner6_decomp [Finite G] (h42 : Asc82Lemma42) (hin6 : Asc82FactInner6) {t : G}
    {L : Subgroup G} (hctx : Sec4Setting G t L) {s : G} (hsc : s ∈ centralizer ({t} : Set G))
    (hs2 : orderOf s = 2) (hsN : s ∈ normalizer (L : Set G))
    (hs6 : InducesTypeSome L s 7 1 6 (-1)) :
    ∃ u c : G, u ∈ L ∧ orderOf u = 2 ∧ InducesTypeSome L u 7 1 6 (-1) ∧ (c = 1 ∨ c = t) ∧
      s = u * c := by
  obtain ⟨u, c, huL, hu2, hu6, hcC, hsuc⟩ :=
    hin6 G L (sec4_isOmega7Group hctx) s hs2 hsN hs6
  have huc : u * c = c * u := Subgroup.mem_centralizer_iff.mp hcC u huL
  have hs_sq : s * s = 1 := by
    have h' := pow_orderOf_eq_one s
    rw [hs2, pow_two] at h'
    exact h'
  have hu_sq : u * u = 1 := by
    have h' := pow_orderOf_eq_one u
    rw [hu2, pow_two] at h'
    exact h'
  have hcc : c * c = 1 := by
    have h' : s * s = (u * u) * (c * c) := by
      have huc_c : Commute u c := huc
      rw [hsuc]
      exact huc_c.symm.mul_mul_mul_comm u c
    rw [hs_sq, hu_sq, one_mul] at h'
    exact h'.symm
  have htC : t ∈ centralizer (L : Set G) := sec4_t_mem_centralizer hctx.toSec3Setting
  have hc_t : c ∈ centralizer ({t} : Set G) := by
    have hu_t : u ∈ centralizer ({t} : Set G) := hctx.component.le huL
    have hmem : u⁻¹ * s ∈ centralizer ({t} : Set G) :=
      (centralizer ({t} : Set G)).mul_mem
        ((centralizer ({t} : Set G)).inv_mem hu_t) hsc
    rwa [show u⁻¹ * s = c by rw [hsuc]; group] at hmem
  have hct : c * t = t * c :=
    (Subgroup.mem_centralizer_iff.mp hc_t t (Set.mem_singleton t)).symm
  have hcyc : ∀ P : Sylow 2 (centralizer (L : Set G)),
      IsCyclic (P : Subgroup (centralizer (L : Set G))) := h42 G t L hctx
  have hcase : c = 1 ∨ c = t :=
    sec4_eq_of_commute (H := centralizer (L : Set G)) hcyc hcC htC hcc hctx.involution hct
  exact ⟨u, c, huL, hu2, hu6, hcase, hsuc⟩

theorem sec4_conj_not_mem [Finite G] (h36 : Asc82Lemma36) (h39 : Asc82Lemma39)
    (hk6 : Asc82FactK6) {t : G} {L : Subgroup G} (hctx : Sec4Setting G t L) {s : G}
    (hs : ∃ h : G, s = h⁻¹ * t * h) (hsL : s ∈ L) (hs2 : orderOf s = 2)
    (hs6 : InducesTypeSome L s 7 1 6 (-1)) : False := by
  obtain ⟨h, rfl⟩ := hs
  have hL : IsOmega7Group L := sec4_isOmega7Group hctx
  obtain ⟨K, hK, hsK, hK43⟩ := hk6 G L hL (h⁻¹ * t * h) hsL hs2 hs6
  obtain ⟨-, -, huniq⟩ :=
    h39 G t L hctx.toSec3SettingLB (h⁻¹ * t * h) K hs2 hsL hsK hK hK43
  have hI : IsComponentIn (CFSG.conjugate L h) (centralizer ({h⁻¹ * t * h} : Set G)) :=
    (hctx.conjugate h).component
  have hFL0 : InFStar L := Or.inl hctx.inF
  have hFL : InFStar (CFSG.conjugate L h) := hFL0.conjugate h
  have hEq : CFSG.conjugate L h = K := huniq (CFSG.conjugate L h) hI hFL
  have hmodel : LieModel (K ⧸ oddCore K) .POmegaOdd 3 3 1 := by
    rw [← hEq]
    exact lieModel_quotient_oddCore_conjugate h hctx.omega7
  have h1 := ctrQ_of_omega7 hK.isQuasisimple hmodel
  have h2 := ctrQ_of_twoU43 hK.isQuasisimple hK43
  rw [h1] at h2
  norm_num at h2

end CFSG.OddStandard.SmallF3.Omega
