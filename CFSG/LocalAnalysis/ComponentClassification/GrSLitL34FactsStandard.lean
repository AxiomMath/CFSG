
module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsStandardBase

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsLocal
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverAut

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34
open CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G]

theorem exists_conj_T0_image
    [Finite G] {J P : Subgroup G} {x : G}
    (hxN : x ∈ normalizer (J : Set G)) (hP : IsSylowTwoIn P J) (hxP : x ∈ normalizer (P : Set G))
    {q : Jhat J →* Equiv.Perm (Fin 42)} (hqS : ∀ e, q e ∈ S) (hqsurj : ∀ s ∈ S, ∃ e, q e = s)
    (hβ : ∀ e, q (betaHat J hxN e) = r₄ * q e * r₄⁻¹) :
    ∃ c ∈ S, c * r₄ = r₄ * c ∧ (∀ p (hp : p ∈ J), p ∈ P → c⁻¹ * q (jq J ⟨p, hp⟩) * c ∈ T0) ∧
      ∀ t ∈ T0, ∃ p ∈ P, ∃ hp : p ∈ J, c⁻¹ * q (jq J ⟨p, hp⟩) * c = t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, T, hT⟩ := hP
  set φ : ↥J →* ↥S := (q.comp (jq J)).codRestrict S (fun j => hqS _) with hφ
  have hφs : Function.Surjective φ := by
    intro s
    obtain ⟨e, he⟩ := hqsurj s s.2
    obtain ⟨j, rfl⟩ := jq_surjective J e
    exact ⟨j, Subtype.ext he⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S sylowT0 (T.mapSurjective hφs)
  have hmem : ∀ y : Equiv.Perm (Fin 42), (y ∈ S ∧ ∃ p ∈ P, ∃ hp : p ∈ J, q (jq J ⟨p, hp⟩) = y) ↔
      (g : Equiv.Perm (Fin 42))⁻¹ * y * g ∈ T0 := by
    intro y
    constructor
    · rintro ⟨hyS, p, hpP, hpJ, rfl⟩
      have h1 : (⟨q (jq J ⟨p, hpJ⟩), hyS⟩ : S) ∈ ((g • sylowT0 : Sylow 2 S) : Subgroup S) := by
        rw [hg, Sylow.coe_mapSurjective]
        refine ⟨⟨p, hpJ⟩, ?_, rfl⟩
        rw [hT]
        exact mem_subgroupOf.mpr hpP
      exact (mem_smul_sylowT0_iff g _).1 h1
    · intro hy
      have hyS : y ∈ S := by
        have h1 := S.mul_mem (S.mul_mem g.2 (T0_le_S hy)) (S.inv_mem g.2)
        rwa [show (g : Equiv.Perm (Fin 42)) * ((g : Equiv.Perm (Fin 42))⁻¹ * y * g) *
          (g : Equiv.Perm (Fin 42))⁻¹ = y by group] at h1
      have h1 := (mem_smul_sylowT0_iff g ⟨y, hyS⟩).2 hy
      rw [hg, Sylow.coe_mapSurjective] at h1
      obtain ⟨j, hjT, hj⟩ := h1
      rw [hT] at hjT
      exact ⟨hyS, j, mem_subgroupOf.mp hjT, j.2, congrArg Subtype.val hj⟩
  have hr : ∀ t ∈ T0, (g : Equiv.Perm (Fin 42))⁻¹ * (r₄ * ((g : Equiv.Perm (Fin 42)) * t *
      (g : Equiv.Perm (Fin 42))⁻¹) * r₄⁻¹) * g ∈ T0 := by
    intro t ht
    have hgt : (g : Equiv.Perm (Fin 42))⁻¹ * ((g : Equiv.Perm (Fin 42)) * t *
        (g : Equiv.Perm (Fin 42))⁻¹) * g ∈ T0 := by
      rwa [show (g : Equiv.Perm (Fin 42))⁻¹ * ((g : Equiv.Perm (Fin 42)) * t *
        (g : Equiv.Perm (Fin 42))⁻¹) * g = t by group]
    obtain ⟨-, p, hpP, hpJ, hpe⟩ := (hmem _).2 hgt
    apply (hmem _).1
    refine ⟨?_, x⁻¹ * p * x, conj_mem_of_mem_normalizer hxP hpP,
      conj_mem_of_mem_normalizer hxN hpJ, ?_⟩
    · rw [← hpe, ← hβ]
      exact hqS _
    · rw [← hpe, ← hβ, betaHat_jq]
      rfl
  obtain ⟨c, hcS, hcr, hc⟩ := exists_conj_T0_of_r4 g.2 hr
  refine ⟨c, hcS, hcr, fun p hpJ hpP => (hc _).1 ((hmem _).1 ⟨hqS _, p, hpP, hpJ, rfl⟩),
    fun t ht => ?_⟩
  have h1 : c⁻¹ * (c * t * c⁻¹) * c ∈ T0 := by
    rwa [show c⁻¹ * (c * t * c⁻¹) * c = t by group]
  obtain ⟨-, p, hpP, hpJ, hpe⟩ := (hmem _).2 ((hc _).2 h1)
  refine ⟨p, hpP, hpJ, ?_⟩
  rw [hpe]
  group

theorem exists_standard
    [Finite G] {J P : Subgroup G} {x : G} (hJ : ⁅J, J⁆ = J)
    (hL : IsL34Type (J ⧸ Open.fusionZStar J)) (hx : IsL34Unitary J x) (hP : IsSylowTwoIn P J)
    (hxP : x ∈ normalizer (P : Set G)) :
    ∃ (q : Jhat J →* Equiv.Perm (Fin 42)) (l : Cover →* Jhat J), (∀ e, q e ∈ S) ∧
      (∀ s ∈ S, ∃ e, q e = s) ∧ q.ker = center (Jhat J) ∧ (∀ e ∈ q.ker, e ^ 3 = 1 → e = 1) ∧
      q.comp l = sigma ∧ Function.Surjective l ∧
      (∀ e, q (betaHat J hx.1 e) = r₄ * q e * r₄⁻¹) ∧
      ∀ e, q e ∈ T0 ↔ ∃ p ∈ P, ∃ hp : p ∈ J, jq J ⟨p, hp⟩ = e := by
  obtain ⟨q, hqS, hqsurj, hqker, h3, hβ⟩ := exists_unitary_realization hJ hL hx
  obtain ⟨c, hcS, hcr, hc1, hc2⟩ := exists_conj_T0_image hx.1 hP hxP hqS hqsurj hβ
  obtain ⟨hS', hsurj', hker'⟩ := conj_jq hqS hqsurj (R.inv_mem (S_le_R hcS))
  set q' := (MulAut.conj c⁻¹).toMonoidHom.comp q with hq'
  have hq'e : ∀ e, q' e = c⁻¹ * q e * c := fun e => by simp [hq']
  have hker'' : q'.ker = center (Jhat J) := by rw [hker', hqker]
  obtain ⟨l, hl, hls⟩ := exists_lam (commutator_jhat hJ) q' hS' hsurj' (hker'' ▸ le_refl _)
  refine ⟨q', l, hS', hsurj', hker'', by rw [hker']; exact h3, hl, hls, fun e => ?_, fun e => ?_⟩
  · have h₁ : c⁻¹ * r₄ = r₄ * c⁻¹ := by
      calc c⁻¹ * r₄ = c⁻¹ * (r₄ * c) * c⁻¹ := by group
        _ = c⁻¹ * (c * r₄) * c⁻¹ := by rw [hcr]
        _ = r₄ * c⁻¹ := by group
    have h₂ : r₄⁻¹ * c = c * r₄⁻¹ := by
      calc r₄⁻¹ * c = r₄⁻¹ * (c * r₄) * r₄⁻¹ := by group
        _ = r₄⁻¹ * (r₄ * c) * r₄⁻¹ := by rw [hcr]
        _ = c * r₄⁻¹ := by group
    rw [hq'e, hq'e, hβ]
    calc c⁻¹ * (r₄ * q e * r₄⁻¹) * c = (c⁻¹ * r₄) * q e * (r₄⁻¹ * c) := by group
      _ = (r₄ * c⁻¹) * q e * (c * r₄⁻¹) := by rw [h₁, h₂]
      _ = r₄ * (c⁻¹ * q e * c) * r₄⁻¹ := by group
  · rw [hq'e]
    constructor
    · intro he
      obtain ⟨p, hpP, hpJ, hpe⟩ := hc2 _ he
      have hqq : q (jq J ⟨p, hpJ⟩) = q e := mul_left_cancel (mul_right_cancel hpe)
      have hz : (jq J ⟨p, hpJ⟩)⁻¹ * e ∈ center (Jhat J) := by
        rw [← hqker, MonoidHom.mem_ker, map_mul, map_inv, hqq, inv_mul_cancel]
      obtain ⟨p', hp'P, hp'J, hp'e⟩ := exists_mem_of_mem_center hP hz
      refine ⟨p * p', P.mul_mem hpP hp'P, J.mul_mem hpJ hp'J, ?_⟩
      have e1 : (⟨p * p', J.mul_mem hpJ hp'J⟩ : J) = ⟨p, hpJ⟩ * ⟨p', hp'J⟩ := rfl
      rw [e1, map_mul, hp'e]
      group
    · rintro ⟨p, hpP, hpJ, rfl⟩
      exact hc1 p hpJ hpP

end CFSG.ComponentClassification.GrSLit.L34Facts
