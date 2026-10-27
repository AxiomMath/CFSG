module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsField
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsUnbalModel

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34

variable {G : Type} [Group G] [Finite G]

theorem exists_field_realization {J : Subgroup G}
    (hJ : ⁅J, J⁆ = J) (hL : IsL34Type (J ⧸ Open.fusionZStar J)) {s : G}
    (hsN : s ∈ normalizer (J : Set G)) (hs2 : s * s = 1) (hsK : s ∉ withKernel J)
    (hcount : Nat.card {j : J // (j : G)⁻¹ * s⁻¹ * j * s ∈ zStarIn J} =
      168 * Nat.card (zStarIn J)) :
    ∃ q : Jhat J →* Equiv.Perm (Fin 42), (∀ e, q e ∈ S) ∧ (∀ t ∈ S, ∃ e, q e = t) ∧
      q.ker = center (Jhat J) ∧ (∀ e ∈ q.ker, e ^ 3 = 1 → e = 1) ∧
      ∀ e, q (betaHat J hsN e) = r₂ * q e * r₂⁻¹ := by
  obtain ⟨q, hqS, hqsurj, hqker, h3⟩ := exists_jq hL
  obtain ⟨r, hrR, hr⟩ := exists_realization q hqS hqsurj (betaHat J hsN) (fun e => by
    rw [hqker]
    exact mulEquiv_mem_center_iff _ e)
  have hr2 : r * r = 1 := by
    have hc : r * r ∈ centralizer (S : Set (Equiv.Perm (Fin 42))) ⊓ R := by
      refine mem_inf.mpr ⟨mem_centralizer_iff.mpr fun t ht => ?_, R.mul_mem hrR hrR⟩
      obtain ⟨e, rfl⟩ := hqsurj t ht
      have h1 := hr (betaHat J hsN e)
      rw [betaHat_betaHat J hsN hs2, hr e] at h1
      calc q e * (r * r) = r * (r * q e * r⁻¹) * r⁻¹ * (r * r) := by rw [← h1]
        _ = r * r * q e := by group
    rw [centralizer_S_inf_R] at hc
    exact (mem_bot.mp hc)
  have hrS : r ∉ S := by
    intro hrS
    obtain ⟨e₀, he₀⟩ := hqsurj r hrS
    exact hsK (mem_withKernel_of_realization hJ hsN hqker (e₀ := e₀) fun e => by
      rw [hr e, he₀])
  have hcard : Nat.card ↥(centralizer ({r} : Set (Equiv.Perm (Fin 42))) ⊓ S) = 168 := by
    have h1 := card_set_eq_of_realization hsN hqS hqsurj hqker hr
    rw [hcount] at h1
    have hpos : 0 < Nat.card (zStarIn J) := Nat.card_pos
    exact (Nat.eq_of_mul_eq_mul_right hpos h1).symm
  have hord : orderOf (⟨r, hrR⟩ : R) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime (Subtype.ext ?_) fun h => hrS ?_
    · simp only [OneMemClass.coe_one, pow_two]
      exact hr2
    · have h' : r = 1 := congrArg Subtype.val h
      rw [h']
      exact S.one_mem
  have hconj : ∃ c ∈ R, r = c * r₂ * c⁻¹ := by
    rcases (PSL3Four.orderOf_eq_two_iff _).1 hord with h | h | h | h
    · exact absurd (mem_S_of_isConj₁ h) hrS
    · exact eq_conj_of_isConj h
    · have h1 := card_centralizer_S_of_isConj h
      have h2 : Nat.card C₃ = 60 := card_C₃
      rw [C₃] at h2
      rw [hcard] at h1
      exact absurd (h1.trans h2) (by norm_num)
    · have h1 := card_centralizer_S_of_isConj h
      have h2 : Nat.card C₄ = 72 := card_C₄
      rw [C₄] at h2
      rw [hcard] at h1
      exact absurd (h1.trans h2) (by norm_num)
  obtain ⟨c, hcR, hc⟩ := hconj
  obtain ⟨hS', hsurj', hker'⟩ := conj_jq hqS hqsurj (R.inv_mem hcR)
  refine ⟨(MulAut.conj c⁻¹).toMonoidHom.comp q, hS', hsurj', by rw [hker', hqker],
    by rw [hker']; exact h3, fun e => ?_⟩
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [hr e, hc]
  group

theorem exists_conj_T0_image_r2
    {J P : Subgroup G} {x : G}
    (hxN : x ∈ normalizer (J : Set G)) (hP : IsSylowTwoIn P J) (hxP : x ∈ normalizer (P : Set G))
    {q : Jhat J →* Equiv.Perm (Fin 42)} (hqS : ∀ e, q e ∈ S) (hqsurj : ∀ t ∈ S, ∃ e, q e = t)
    (hβ : ∀ e, q (betaHat J hxN e) = r₂ * q e * r₂⁻¹) :
    ∃ c ∈ S, c * r₂ = r₂ * c ∧ (∀ p (hp : p ∈ J), p ∈ P → c⁻¹ * q (jq J ⟨p, hp⟩) * c ∈ T0) ∧
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
  have hr : ∀ t ∈ T0, (g : Equiv.Perm (Fin 42))⁻¹ * (r₂ * ((g : Equiv.Perm (Fin 42)) * t *
      (g : Equiv.Perm (Fin 42))⁻¹) * r₂⁻¹) * g ∈ T0 := by
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
  obtain ⟨c, hcS, hcr, hc⟩ := exists_conj_T0_of_r2 g.2 hr
  refine ⟨c, hcS, hcr, fun p hpJ hpP => (hc _).1 ((hmem _).1 ⟨hqS _, p, hpP, hpJ, rfl⟩),
    fun t ht => ?_⟩
  have h1 : c⁻¹ * (c * t * c⁻¹) * c ∈ T0 := by
    rwa [show c⁻¹ * (c * t * c⁻¹) * c = t by group]
  obtain ⟨-, p, hpP, hpJ, hpe⟩ := (hmem _).2 ((hc _).2 h1)
  refine ⟨p, hpP, hpJ, ?_⟩
  rw [hpe]
  group

theorem exists_field_standard
    {J P : Subgroup G} {s : G}
    (hJ : ⁅J, J⁆ = J) (hL : IsL34Type (J ⧸ Open.fusionZStar J))
    (hsN : s ∈ normalizer (J : Set G)) (hs2 : s * s = 1) (hsK : s ∉ withKernel J)
    (hcount : Nat.card {j : J // (j : G)⁻¹ * s⁻¹ * j * s ∈ zStarIn J} =
      168 * Nat.card (zStarIn J)) (hP : IsSylowTwoIn P J) (hsP : s ∈ normalizer (P : Set G)) :
    ∃ (q : Jhat J →* Equiv.Perm (Fin 42)) (l : Cover →* Jhat J), IsQSetting q l ∧
      (∀ e, q (betaHat J hsN e) = r₂ * q e * r₂⁻¹) ∧
      ∀ e, q e ∈ T0 ↔ ∃ p ∈ P, ∃ hp : p ∈ J, jq J ⟨p, hp⟩ = e := by
  obtain ⟨q, hqS, hqsurj, hqker, h3, hβ⟩ :=
    exists_field_realization hJ hL hsN hs2 hsK hcount
  obtain ⟨c, hcS, hcr, hc1, hc2⟩ := exists_conj_T0_image_r2 hsN hP hsP hqS hqsurj hβ
  obtain ⟨hS', hsurj', hker'⟩ := conj_jq hqS hqsurj (R.inv_mem (S_le_R hcS))
  set q' := (MulAut.conj c⁻¹).toMonoidHom.comp q with hq'
  have hq'e : ∀ e, q' e = c⁻¹ * q e * c := fun e => by simp [hq']
  have hker'' : q'.ker = center (Jhat J) := by rw [hker', hqker]
  obtain ⟨l, hl, hls⟩ := exists_lam (commutator_jhat hJ) q' hS' hsurj' (hker'' ▸ le_refl _)
  refine ⟨q', l, ⟨hS', hsurj', hker'', by rw [hker']; exact h3, hl, hls⟩, fun e => ?_,
    fun e => ?_⟩
  · have h₁ : c⁻¹ * r₂ = r₂ * c⁻¹ := by
      calc c⁻¹ * r₂ = c⁻¹ * (r₂ * c) * c⁻¹ := by group
        _ = c⁻¹ * (c * r₂) * c⁻¹ := by rw [hcr]
        _ = r₂ * c⁻¹ := by group
    have h₂ : r₂⁻¹ * c = c * r₂⁻¹ := by
      calc r₂⁻¹ * c = r₂⁻¹ * (c * r₂) * r₂⁻¹ := by group
        _ = r₂⁻¹ * (r₂ * c) * r₂⁻¹ := by rw [hcr]
        _ = c * r₂⁻¹ := by group
    rw [hq'e, hq'e, hβ]
    calc c⁻¹ * (r₂ * q e * r₂⁻¹) * c = (c⁻¹ * r₂) * q e * (r₂⁻¹ * c) := by group
      _ = (r₂ * c⁻¹) * q e * (c * r₂⁻¹) := by rw [h₁, h₂]
      _ = r₂ * (c⁻¹ * q e * c) * r₂⁻¹ := by group
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
