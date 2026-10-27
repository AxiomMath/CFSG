module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsField
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsOuter
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Wit

public section

namespace CFSG.ComponentClassification.GrSLit.GrS4

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34
open CFSG.ComponentClassification.GrSLit.L34Facts

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_T0_image_rho
    {J P : Subgroup G} {x : G} (hxN : x ∈ normalizer (J : Set G)) (hP : IsSylowTwoIn P J)
    (hxP : x ∈ normalizer (P : Set G)) {q : Jhat J →* Equiv.Perm (Fin 42)} (hqS : ∀ e, q e ∈ S)
    (hqsurj : ∀ t ∈ S, ∃ e, q e = t) {ρ : Equiv.Perm (Fin 42)}
    (hρ : ∀ s ∈ S, (∀ t ∈ T0, s⁻¹ * (ρ * (s * t * s⁻¹) * ρ⁻¹) * s ∈ T0) →
      ∃ c ∈ S, c * ρ = ρ * c ∧ ∀ t, s⁻¹ * t * s ∈ T0 ↔ c⁻¹ * t * c ∈ T0)
    (hβ : ∀ e, q (betaHat J hxN e) = ρ * q e * ρ⁻¹) :
    ∃ c ∈ S, c * ρ = ρ * c ∧ (∀ p (hp : p ∈ J), p ∈ P → c⁻¹ * q (jq J ⟨p, hp⟩) * c ∈ T0) ∧
      ∀ t ∈ T0, ∃ p ∈ P, ∃ hp : p ∈ J, c⁻¹ * q (jq J ⟨p, hp⟩) * c = t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, T, hT⟩ := hP
  set φ : ↥J →* ↥S := (q.comp (jq J)).codRestrict S (fun j => hqS _) with hφ
  have hφs : Function.Surjective φ := by
    intro t
    obtain ⟨e, he⟩ := hqsurj t t.2
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
  have hr : ∀ t ∈ T0, (g : Equiv.Perm (Fin 42))⁻¹ * (ρ * ((g : Equiv.Perm (Fin 42)) * t *
      (g : Equiv.Perm (Fin 42))⁻¹) * ρ⁻¹) * g ∈ T0 := by
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
  obtain ⟨c, hcS, hcr, hc⟩ := hρ g g.2 hr
  refine ⟨c, hcS, hcr, fun p hpJ hpP => (hc _).1 ((hmem _).1 ⟨hqS _, p, hpP, hpJ, rfl⟩),
    fun t ht => ?_⟩
  have h1 : c⁻¹ * (c * t * c⁻¹) * c ∈ T0 := by
    rwa [show c⁻¹ * (c * t * c⁻¹) * c = t by group]
  obtain ⟨-, p, hpP, hpJ, hpe⟩ := (hmem _).2 ((hc _).2 h1)
  refine ⟨p, hpP, hpJ, ?_⟩
  rw [hpe]
  group

theorem exists_outer_standard
    {J P : Subgroup G} {s : G}
    (hJ : ⁅J, J⁆ = J) (hL : IsL34Type (J ⧸ Open.fusionZStar J))
    (hsN : s ∈ normalizer (J : Set G)) (hs2 : s * s = 1) (hsK : s ∉ withKernel J)
    (hP : IsSylowTwoIn P J) (hsP : s ∈ normalizer (P : Set G)) :
    ∃ (q : Jhat J →* Equiv.Perm (Fin 42)) (l : Cover →* Jhat J) (ρ : Equiv.Perm (Fin 42)),
      (ρ = r₂ ∨ ρ = r₃ ∨ ρ = r₄) ∧ IsQSetting q l ∧
      (∀ e, q (betaHat J hsN e) = ρ * q e * ρ⁻¹) ∧
      ∀ e, q e ∈ T0 ↔ ∃ p ∈ P, ∃ hp : p ∈ J, jq J ⟨p, hp⟩ = e := by
  obtain ⟨q, hqS, hqsurj, hqker, h3, ρ, hρ, hβ⟩ := exists_outer_realization hJ hL hsN hs2 hsK
  have hρT : ∀ t ∈ S, (∀ u ∈ T0, t⁻¹ * (ρ * (t * u * t⁻¹) * ρ⁻¹) * t ∈ T0) →
      ∃ c ∈ S, c * ρ = ρ * c ∧ ∀ u, t⁻¹ * u * t ∈ T0 ↔ c⁻¹ * u * c ∈ T0 := by
    rcases hρ with rfl | rfl | rfl
    · exact fun t ht hr => exists_conj_T0_of_r2 ht hr
    · exact fun t ht hr => exists_conj_T0_of_r3 ht hr
    · exact fun t ht hr => exists_conj_T0_of_r4 ht hr
  obtain ⟨c, hcS, hcr, hc1, hc2⟩ := exists_conj_T0_image_rho hsN hP hsP hqS hqsurj hρT hβ
  obtain ⟨hS', hsurj', hker'⟩ := conj_jq hqS hqsurj (R.inv_mem (S_le_R hcS))
  set q' := (MulAut.conj c⁻¹).toMonoidHom.comp q with hq'
  have hq'e : ∀ e, q' e = c⁻¹ * q e * c := fun e => by simp [hq']
  have hker'' : q'.ker = center (Jhat J) := by rw [hker', hqker]
  obtain ⟨l, hl, hls⟩ := exists_lam (commutator_jhat hJ) q' hS' hsurj' (hker'' ▸ le_refl _)
  refine ⟨q', l, ρ, hρ, ⟨hS', hsurj', hker'', by rw [hker']; exact h3, hl, hls⟩, fun e => ?_,
    fun e => ?_⟩
  · have h₁ : c⁻¹ * ρ = ρ * c⁻¹ := by
      calc c⁻¹ * ρ = c⁻¹ * (ρ * c) * c⁻¹ := by group
        _ = c⁻¹ * (c * ρ) * c⁻¹ := by rw [hcr]
        _ = ρ * c⁻¹ := by group
    have h₂ : ρ⁻¹ * c = c * ρ⁻¹ := by
      calc ρ⁻¹ * c = ρ⁻¹ * (c * ρ) * ρ⁻¹ := by group
        _ = ρ⁻¹ * (ρ * c) * ρ⁻¹ := by rw [hcr]
        _ = c * ρ⁻¹ := by group
    rw [hq'e, hq'e, hβ]
    calc c⁻¹ * (ρ * q e * ρ⁻¹) * c = (c⁻¹ * ρ) * q e * (ρ⁻¹ * c) := by group
      _ = (ρ * c⁻¹) * q e * (c * ρ⁻¹) := by rw [h₁, h₂]
      _ = ρ * (c⁻¹ * q e * c) * ρ⁻¹ := by group
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

end CFSG.ComponentClassification.GrSLit.GrS4
