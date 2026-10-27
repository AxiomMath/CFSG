
module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCenterBase

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsTransfer
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsParabolic
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Inputs46
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Inputs47
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Basic
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCover
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverAut

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.PSL3Four.Native

variable {G : Type} [Group G] [Finite G]

theorem exists_setting
    {J : Subgroup G}
    (hJ : ⁅J, J⁆ = J) (hL : IsL34Type (J ⧸ Open.fusionZStar J)) :
    ∃ (q : Jhat J →* Equiv.Perm (Fin 42)) (l : Cover →* Jhat J), (∀ e, q e ∈ S) ∧
      (∀ s ∈ S, ∃ e, q e = s) ∧ q.ker = center (Jhat J) ∧
      (∀ e ∈ q.ker, e ^ 3 = 1 → e = 1) ∧ q.comp l = sigma ∧ Function.Surjective l := by
  obtain ⟨q, hqS, hqsurj, hqker, h3⟩ := exists_jq hL
  obtain ⟨l, hl, hls⟩ := exists_lam (commutator_jhat hJ) q hqS hqsurj (hqker ▸ le_refl _)
  exact ⟨q, l, hqS, hqsurj, hqker, h3, hl, hls⟩

theorem exists_sq_eq_sq
    {E : Type*} [Group E]
    {q : E →* Equiv.Perm (Fin 42)} (hqS : ∀ e, q e ∈ S) (hqsurj : ∀ s ∈ S, ∃ e, q e = s)
    (hker : q.ker ≤ center E) {l : Cover →* E} (hl : q.comp l = sigma) (hl3 : l z₃ = 1) {e : E}
    (he : q e * q e = 1) : ∃ ζ ∈ center E, e * e = ζ * ζ := by
  obtain ⟨g, hgS, hgT⟩ := exists_conj_mem_T0 (hqS e) he
  obtain ⟨k, hk, hkt⟩ := exists_tg hgT
  obtain ⟨e₀, he₀⟩ := hqsurj g hgS
  set w := l (cv (tw k)) with hw
  have hqw : q w = wordPerm (tg k) := by rw [hw, ← MonoidHom.comp_apply, hl, sigma_tw k hk]
  set ξ := (e₀ * w * e₀⁻¹)⁻¹ * e with hξ
  have hξc : ξ ∈ center E := hker (by
    rw [MonoidHom.mem_ker, hξ, map_mul, map_inv, map_mul, map_mul, map_inv, hqw, hkt, he₀]
    group)
  have hee : e = e₀ * w * e₀⁻¹ * ξ := by rw [hξ]; group
  have hsq2 : (wordPerm (tg k)) * (wordPerm (tg k)) = 1 := by
    rw [hkt]
    calc g⁻¹ * q e * g * (g⁻¹ * q e * g) = g⁻¹ * (q e * q e) * g := by group
      _ = 1 := by rw [he]; group
  have hzc : ∀ c ∈ sigma.ker, l c ∈ center E := fun c hc => hker (by
    rw [MonoidHom.mem_ker, ← MonoidHom.comp_apply, hl]; exact hc)
  have hww : ∃ ζ ∈ center E, w * w = ζ * ζ := by
    have hinv := coverParts.invols k hk
    have h1 : TabRep (comp 42 (wordTab (tg k)) (wordTab (tg k)))
        (wordPerm (tg k) * wordPerm (tg k)) := (tabRep_wordTab _).comp (tabRep_wordTab _)
    rw [hsq2] at h1
    have htab : comp 42 (wordTab (tg k)) (wordTab (tg k)) = idTab 42 :=
      h1.tab_eq TabRep.idTab
    rw [htab, beq_self_eq_true] at hinv
    rcases Bool.or_eq_true _ _ ▸ hinv.symm with h0 | hmem
    · have h0' : k = 0 := by simpa using h0
      subst h0'
      have htw : tw 0 = [] := by decide
      refine ⟨1, one_mem _, ?_⟩
      rw [hw, htw, show cv ([] : List (Fin 2 × Bool)) = 1 from map_one _, map_one]
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp (List.elem_iff.mp hmem)
      set y := z₁ ^ d.2.1 * z₂ ^ d.2.2.1 with hy
      have hyk : y ∈ sigma.ker := by
        rw [MonoidHom.mem_ker, hy, map_mul, map_pow, map_pow, sigma_z₁, sigma_z₂]; simp
      refine ⟨l y, hzc _ hyk, ?_⟩
      have hcomm : Commute (z₁ ^ d.2.1) (z₂ ^ d.2.2.1) :=
        (mem_center_iff.mp (Subgroup.pow_mem _ z₁_mem_center _) _).symm
      have hsq : cv (tw d.1) * cv (tw d.1) = y * y * z₃ ^ d.2.2.2 := by
        rw [← pow_two, sq_spec hd, hy, ← pow_two, hcomm.mul_pow, ← pow_mul, ← pow_mul,
          mul_comm 2 d.2.1, mul_comm 2 d.2.2.1]
      rw [hw, ← map_mul, hsq, map_mul, map_mul, map_pow, hl3, one_pow, mul_one]
  obtain ⟨ζ, hζc, hζ⟩ := hww
  refine ⟨ζ * ξ, mul_mem hζc hξc, ?_⟩
  have hξ' := mem_center_iff.mp hξc
  have hζ' := mem_center_iff.mp hζc
  have e1 : e * e = e₀ * (w * w) * e₀⁻¹ * (ξ * ξ) := by
    rw [hee]
    have : ξ * (e₀ * w * e₀⁻¹) = e₀ * w * e₀⁻¹ * ξ := (hξ' _).symm
    calc e₀ * w * e₀⁻¹ * ξ * (e₀ * w * e₀⁻¹ * ξ)
        = e₀ * w * e₀⁻¹ * (ξ * (e₀ * w * e₀⁻¹)) * ξ := by group
      _ = e₀ * w * e₀⁻¹ * (e₀ * w * e₀⁻¹ * ξ) * ξ := by rw [this]
      _ = e₀ * (w * w) * e₀⁻¹ * (ξ * ξ) := by group
  rw [e1, hζ]
  have e2 : e₀ * (ζ * ζ) = ζ * ζ * e₀ := by
    calc e₀ * (ζ * ζ) = e₀ * ζ * ζ := by group
      _ = ζ * e₀ * ζ := by rw [hζ' e₀]
      _ = ζ * (e₀ * ζ) := by group
      _ = ζ * (ζ * e₀) := by rw [hζ' e₀]
      _ = ζ * ζ * e₀ := by group
  rw [e2]
  calc ζ * ζ * e₀ * e₀⁻¹ * (ξ * ξ) = ζ * (ζ * ξ) * ξ := by group
    _ = ζ * (ξ * ζ) * ξ := by rw [hξ' ζ]
    _ = ζ * ξ * (ζ * ξ) := by group

theorem lam_z_facts
    {E : Type*} [Group E] {q : E →* Equiv.Perm (Fin 42)} (hker : q.ker ≤ center E)
    {l : Cover →* E} (hl : q.comp l = sigma) :
    l z₁ ∈ center E ∧ l z₂ ∈ center E ∧ l z₁ ^ 4 = 1 ∧ l z₂ ^ 4 = 1 := by
  refine ⟨hker ?_, hker ?_, by rw [← map_pow, z₁_pow, map_one],
    by rw [← map_pow, z₂_pow, map_one]⟩
  · rw [MonoidHom.mem_ker, ← MonoidHom.comp_apply, hl, sigma_z₁]
  · rw [MonoidHom.mem_ker, ← MonoidHom.comp_apply, hl, sigma_z₂]

theorem l34CenterExponentFact :
    L34CenterExponentFact := by
  intro G _ _ J P hJ hL hP z hz
  obtain ⟨q, l, hqS, hqsurj, hqker, h3, hl, hls⟩ := exists_setting hJ hL
  obtain ⟨hzP, hzZ⟩ := mem_inf.mp hz
  have hzJ := hP.1 hzP
  have hc : jq J ⟨z, hzJ⟩ ∈ q.ker := by rw [hqker]; exact (mem_zStarIn_iff hzJ).1 hzZ
  obtain ⟨i, j, hij⟩ := (mem_ker_iff hl hls h3).1 hc
  obtain ⟨hc1, -, h1, h2⟩ := lam_z_facts (hqker ▸ le_refl _) hl
  have hcomm : Commute (l z₁ ^ i) (l z₂ ^ j) :=
    (mem_center_iff.mp (Subgroup.pow_mem _ hc1 _) _).symm
  have h4 : jq J ⟨z ^ 4, J.pow_mem hzJ 4⟩ = 1 := by
    rw [show (⟨z ^ 4, J.pow_mem hzJ 4⟩ : J) = ⟨z, hzJ⟩ ^ 4 from rfl, map_pow, hij, hcomm.mul_pow,
      ← pow_mul, ← pow_mul, mul_comm i 4, mul_comm j 4, pow_mul, pow_mul, h1, h2, one_pow,
      one_pow, one_mul]
  exact eq_one_of_jq_eq_one hP.1 (GrS4.isPGroup_of_isSylowTwoIn hP) (P.pow_mem hzP 4) h4

theorem l34SquareCenterFact :
    L34SquareCenterFact := by
  intro G _ _ J P hJ hL hP u hu hu2
  obtain ⟨q, l, hqS, hqsurj, hqker, h3, hl, hls⟩ := exists_setting hJ hL
  have huJ := hP.1 hu
  have hcen : jq J ⟨u, huJ⟩ * jq J ⟨u, huJ⟩ ∈ center (Jhat J) := by
    rw [← map_mul]
    exact (mem_zStarIn_iff (J.mul_mem huJ huJ)).1 hu2
  have hq2 : q (jq J ⟨u, huJ⟩) * q (jq J ⟨u, huJ⟩) = 1 := by
    rw [← map_mul]
    exact (hqker ▸ hcen : _ ∈ q.ker)
  obtain ⟨ζ, hζc, hζ⟩ := exists_sq_eq_sq hqS hqsurj (hqker ▸ le_refl _) hl
    (lam_z₃ hl h3) hq2
  obtain ⟨z, hzP, hzJ, hzζ⟩ := exists_mem_of_mem_center hP hζc
  refine ⟨z, mem_inf.mpr ⟨hzP, (mem_zStarIn_iff hzJ).2 (hzζ ▸ hζc)⟩, ?_⟩
  apply eq_of_jq_eq hP.1 (GrS4.isPGroup_of_isSylowTwoIn hP) (P.mul_mem hu hu)
    (P.mul_mem hzP hzP)
  show jq J (⟨u, huJ⟩ * ⟨u, huJ⟩) = jq J (⟨z, hzJ⟩ * ⟨z, hzJ⟩)
  rw [map_mul, map_mul, hζ, hzζ]

theorem l34NoSquareRootFact :
    L34NoSquareRootFact := by
  intro G _ _ J P hJ hL hP _ _ u hu hu2
  obtain ⟨z, hz, hzu⟩ := l34SquareCenterFact G J P hJ hL hP u hu hu2
  have h4 := l34CenterExponentFact G J P hJ hL hP z hz
  calc u ^ 4 = (u * u) * (u * u) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = z * z * (z * z) := by rw [hzu]
    _ = z ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = 1 := h4

end CFSG.ComponentClassification.GrSLit.L34Facts
