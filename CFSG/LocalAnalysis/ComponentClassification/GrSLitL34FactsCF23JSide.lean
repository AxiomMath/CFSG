module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23Cover
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsSylowPosition
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Real
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsRealB

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts.Real

open CFSG Subgroup CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit

variable {E : Type*} [Group E] {q : E →* Equiv.Perm (Fin 42)} {l : Cover →* E}

theorem exists_fixed_model
    (h : IsQSetting q l) {y : Equiv.Perm (Fin 42)} (hyR : y ∈ R)
    (hyN : ∀ t ∈ T0, y * t * y⁻¹ ∈ T0) (hy2 : y * y = 1) {β : E ≃* E}
    (hβ : ∀ e, q (β e) = y * q e * y⁻¹) :
    ∃ x : MElt, x.1 < 64 ∧ wordPerm (tg x.1) ≠ 1 ∧ mulM x x = oneM ∧ β (nfM l x) = nfM l x := by
  obtain ⟨i, hi, t, ht, rfl, hβt⟩ := exists_betaRep h hyR hyN hβ
  have hfix := invFixParts hi ht (sq1M_of hi hy2)
  simp only [invFixM, List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hfix
  obtain ⟨x, hxM, ⟨hne, hsq⟩, hbx⟩ := hfix
  have hx : x.1 < 64 := lt_of_mem_allM hxM
  refine ⟨x, hx, fun h1 => ?_, hsq, ?_⟩
  · have h2 := ((tabRep_wordTab (tg x.1)).beq_iff TabRep.idTab).2 h1
    rw [hne] at h2
    exact Bool.false_ne_true h2
  · rw [betaY_nfM h ht hi hβt hx, hbx]

end CFSG.ComponentClassification.GrSLit.L34Facts.Real

namespace CFSG.ComponentClassification.GSThmB.CF23L34

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers.L34 CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.L34Facts
  CFSG.ComponentClassification.GrSLit.L34Facts.Real

variable {H : Type} [Group H] [Finite H] (h : Hyp52 H)

theorem isSylowTwoIn_D : IsSylowTwoIn h.D h.J :=
  ⟨inf_le_right, UnbalancedGS.RankProjectiveAction.exists_sylow_inf_of_le_normalizer h.S_le
    h.S_sylow (le_inf h.J_le le_normalizer) inf_le_right⟩

theorem jq_mem_center {d : H} (hdJ : d ∈ h.J) (hdC : d ∈ coreActionKernel h.J) :
    jq h.J ⟨d, hdJ⟩ ∈ center (Jhat h.J) := by
  rw [mem_center_iff]
  intro e
  obtain ⟨j, rfl⟩ := jq_surjective h.J e
  have h1 := (mem_coreActionKernel.mp hdC).2 j j.2
  have h2 : jq h.J (j⁻¹ * (⟨d, hdJ⟩ : ↥h.J)⁻¹ * j * ⟨d, hdJ⟩) = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    obtain ⟨o, ho, hoe⟩ := h1
    have e : o = j⁻¹ * (⟨d, hdJ⟩ : ↥h.J)⁻¹ * j * ⟨d, hdJ⟩ := Subtype.ext hoe
    rw [← e]
    exact ho
  simp only [map_mul, map_inv] at h2
  calc jq h.J j * jq h.J ⟨d, hdJ⟩ = jq h.J ⟨d, hdJ⟩ * jq h.J j *
      ((jq h.J j)⁻¹ * (jq h.J ⟨d, hdJ⟩)⁻¹ * jq h.J j * jq h.J ⟨d, hdJ⟩) := by group
    _ = jq h.J ⟨d, hdJ⟩ * jq h.J j := by rw [h2, mul_one]

theorem exists_fixed_D
    (hL : Blueprint.LieModel (ZStarBar h.J) .PSL 3 2 2) :
    ∃ (q : Jhat h.J →* Equiv.Perm (Fin 42)) (l : Cover →* Jhat h.J) (x₀ : MElt) (d : H),
      IsQSetting q l ∧ x₀.1 < 64 ∧ mulM x₀ x₀ = oneM ∧ d ∈ h.D ∧
      (∃ hdJ : d ∈ h.J, jq h.J ⟨d, hdJ⟩ = nfM l x₀) ∧ d * d = 1 ∧ d * h.x = h.x * d ∧
      d ∉ h.P := by
  have hJ : ⁅h.J, h.J⁆ = h.J := Subgroup.isPerfect_iff.mp
    (B5a.isPerfect_of_isPComponent_subgroupOf h.J_le h.isPComponent_J)
  have hP := isSylowTwoIn_D h
  have hP2 : IsPGroup 2 h.D := h.isPGroup_S.to_le inf_le_left
  obtain ⟨q, l, hqS, hqsurj, hqker, h3, hql, hls, hT⟩ := exists_sylow_standard hJ hL hP
  have hQ : IsQSetting q l := ⟨hqS, hqsurj, hqker, h3, hql, hls⟩
  have hxN : h.x ∈ normalizer (h.J : Set H) := h.S_le_normalizer h.x_mem
  have hxD : ∀ p ∈ h.D, h.x⁻¹ * p * h.x ∈ h.D := fun p hp =>
    mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem h.x_mem) (h.D_le_S hp)) h.x_mem,
      L34Facts.conj_mem_of_mem_normalizer hxN (h.D_le_J hp)⟩
  obtain ⟨r, hrR, hr⟩ := GrS4.exists_realization_betaHat hxN hqS hqsurj hqker
  have hrN : ∀ t ∈ T0, r * t * r⁻¹ ∈ T0 := by
    intro t ht
    obtain ⟨e, rfl⟩ := hqsurj t (T0_le_S ht)
    obtain ⟨p, hpD, hpJ, rfl⟩ := (hT _).1 ht
    rw [← hr, betaHat_jq]
    exact (hT _).2 ⟨_, hxD p hpD, _, rfl⟩
  have hxK : h.x * h.x ∈ coreActionKernel h.J := by
    have := (mem_inf.mp (mem_inf.mp h.x_sq_mem).1).2
    rwa [pow_two] at this
  have hr2 : r * r = 1 := by
    refine GrS4.realization_eq_one_of_mem hxK hqsurj (R.mul_mem hrR hrR) fun e => ?_
    rw [show betaHat h.J (mem_coreActionKernel.mp hxK).1 e =
      betaHat h.J hxN (betaHat h.J hxN e) from GrS4.betaHat_mul_apply hxN hxN e, hr, hr]
    group
  obtain ⟨x₀, hx₀, hne, hsq, hfix⟩ := exists_fixed_model hQ hrR hrN hr2 hr
  have hqx : q (nfM l x₀) ∈ T0 := by
    rw [q_nfM hQ hx₀]
    exact tg_mem_T0 x₀.1 hx₀
  obtain ⟨d, hdD, hdJ, hd⟩ := (hT _).1 hqx
  refine ⟨q, l, x₀, d, hQ, hx₀, hsq, hdD, ⟨hdJ, hd⟩, ?_, ?_, ?_⟩
  · apply eq_one_of_jq_eq_one (h.D_le_J) hP2 (mul_mem hdD hdD)
    show jq h.J (⟨d, hdJ⟩ * ⟨d, hdJ⟩) = 1
    rw [map_mul, hd, nfM_mul hQ hx₀ hx₀, hsq, nfM_one]
  · have h1 : h.x⁻¹ * d * h.x = d := by
      apply eq_of_jq_eq (h.D_le_J) hP2 (hxD d hdD) hdD
      show jq h.J (conjJ h.J hxN ⟨d, hdJ⟩) = jq h.J ⟨d, hdJ⟩
      rw [← betaHat_jq, hd, hfix]
    calc d * h.x = h.x * (h.x⁻¹ * d * h.x) := by group
      _ = h.x * d := by rw [h1]
  · intro hdP
    have hc := jq_mem_center h hdJ (mem_inf.mp hdP).2
    rw [← hqker, MonoidHom.mem_ker, hd, q_nfM hQ hx₀] at hc
    exact hne hc

end CFSG.ComponentClassification.GSThmB.CF23L34
