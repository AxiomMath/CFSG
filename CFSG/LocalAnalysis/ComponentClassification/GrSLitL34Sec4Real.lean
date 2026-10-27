module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsStandardBase

public section

namespace CFSG.ComponentClassification.GrSLit.GrS4

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.GrSLit.L34Facts
open scoped Pointwise

variable {G : Type} [Group G]

theorem realization_unique {E : Type*} [Group E]
    {q : E →* Equiv.Perm (Fin 42)} (hqsurj : ∀ s ∈ S, ∃ e, q e = s) {β : E → E}
    {r r' : Equiv.Perm (Fin 42)} (hr : r ∈ R) (hr' : r' ∈ R)
    (h : ∀ e, q (β e) = r * q e * r⁻¹) (h' : ∀ e, q (β e) = r' * q e * r'⁻¹) : r = r' := by
  have hc : r⁻¹ * r' ∈ centralizer (S : Set (Equiv.Perm (Fin 42))) ⊓ R := by
    refine mem_inf.mpr ⟨mem_centralizer_iff.mpr fun s hs => ?_, R.mul_mem (R.inv_mem hr) hr'⟩
    obtain ⟨e, rfl⟩ := hqsurj s hs
    have h1 : r * q e * r⁻¹ = r' * q e * r'⁻¹ := by rw [← h, ← h']
    calc q e * (r⁻¹ * r') = r⁻¹ * (r * q e * r⁻¹) * r' := by group
      _ = r⁻¹ * (r' * q e * r'⁻¹) * r' := by rw [h1]
      _ = r⁻¹ * r' * q e := by group
  rw [centralizer_S_inf_R, mem_bot] at hc
  rw [← inv_mul_eq_one]
  exact hc

theorem exists_realization_betaHat {J : Subgroup G} {x : G}
    (hxN : x ∈ normalizer (J : Set G)) {q : Jhat J →* Equiv.Perm (Fin 42)}
    (hqS : ∀ e, q e ∈ S) (hqsurj : ∀ s ∈ S, ∃ e, q e = s) (hqker : q.ker = center (Jhat J)) :
    ∃ r ∈ R, ∀ e, q (betaHat J hxN e) = r * q e * r⁻¹ :=
  exists_realization q hqS hqsurj (betaHat J hxN) fun e => by
    rw [hqker]
    exact mulEquiv_mem_center_iff _ e

theorem betaHat_mul_apply {J : Subgroup G} {x y : G} (hx : x ∈ normalizer (J : Set G))
    (hy : y ∈ normalizer (J : Set G)) (e : Jhat J) :
    betaHat J (mul_mem hx hy) e = betaHat J hy (betaHat J hx e) := by
  obtain ⟨j, rfl⟩ := jq_surjective J e
  rw [betaHat_jq, betaHat_jq, betaHat_jq]
  congr 1
  apply Subtype.ext
  simp only [coe_conjJ]
  group

theorem exists_realization_hom {J H : Subgroup G}
    (hHN : H ≤ normalizer (J : Set G)) {q : Jhat J →* Equiv.Perm (Fin 42)}
    (hqS : ∀ e, q e ∈ S) (hqsurj : ∀ s ∈ S, ∃ e, q e = s) (hqker : q.ker = center (Jhat J)) :
    ∃ ψ : ↥H →* Equiv.Perm (Fin 42), (∀ h, ψ h ∈ R) ∧
      ∀ (h : ↥H) e, q (betaHat J (hHN h.2) e) = (ψ h)⁻¹ * q e * ψ h := by
  choose r hrR hr using fun h : ↥H => exists_realization_betaHat (hHN h.2) hqS hqsurj hqker
  have hmul : ∀ h k : ↥H, r (h * k) = r k * r h := by
    intro h k
    refine realization_unique hqsurj (hrR (h * k)) (R.mul_mem (hrR k) (hrR h)) (hr (h * k))
      fun e => ?_
    have e1 : betaHat J (hHN (h * k).2) e = betaHat J (hHN k.2) (betaHat J (hHN h.2) e) := by
      rw [← betaHat_mul_apply (hHN h.2) (hHN k.2)]
    rw [e1, hr k, hr h]
    group
  refine ⟨{ toFun := fun h => (r h)⁻¹
            map_one' := ?_
            map_mul' := fun h k => by simp only [hmul, mul_inv_rev] }, fun h => R.inv_mem (hrR h),
    fun h e => ?_⟩
  · have h1 : r 1 = 1 := by
      refine realization_unique hqsurj (hrR 1) R.one_mem (hr 1) fun e => ?_
      rw [show betaHat J (hHN (1 : ↥H).2) e = e from by
        obtain ⟨j, rfl⟩ := jq_surjective J e
        rw [betaHat_jq]
        congr 1
        apply Subtype.ext
        simp only [coe_conjJ, OneMemClass.coe_one, inv_one, one_mul, mul_one]]
      group
    simp only [h1, inv_one]
  · simp only [MonoidHom.coe_mk, OneHom.coe_mk, inv_inv]
    exact hr h e

theorem mem_coreActionKernel_of_realization_eq_one {J : Subgroup G} (hJ : ⁅J, J⁆ = J) {x : G}
    (hxN : x ∈ normalizer (J : Set G)) {q : Jhat J →* Equiv.Perm (Fin 42)}
    (hqker : q.ker = center (Jhat J)) (h : ∀ e, q (betaHat J hxN e) = q e) :
    x ∈ coreActionKernel J := by
  have hext : (betaHat J hxN).toMonoidHom = MonoidHom.id _ := by
    apply hom_ext_of_central (commutator_jhat hJ) q (hqker ▸ le_refl _)
    refine MonoidHom.ext fun e => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.id_apply]
    exact h e
  refine ⟨hxN, fun j hj => ?_⟩
  have hmem : j⁻¹ * x⁻¹ * j * x ∈ J := by
    have := conj_mem_of_mem_normalizer hxN hj
    rw [show j⁻¹ * x⁻¹ * j * x = j⁻¹ * (x⁻¹ * j * x) by group]
    exact J.mul_mem (J.inv_mem hj) this
  show _ ∈ oddIn J
  rw [mem_oddIn_iff hmem]
  have e1 : (⟨j⁻¹ * x⁻¹ * j * x, hmem⟩ : J) = (⟨j, hj⟩ : J)⁻¹ * conjJ J hxN ⟨j, hj⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjJ]
    group
  rw [e1, map_mul, map_inv, ← betaHat_jq]
  have h2 := DFunLike.congr_fun hext (jq J ⟨j, hj⟩)
  simp only [MulEquiv.coe_toMonoidHom, MonoidHom.id_apply] at h2
  rw [h2, inv_mul_cancel]

theorem realization_eq_one_of_mem {J : Subgroup G} {x : G}
    (hxK : x ∈ coreActionKernel J) {q : Jhat J →* Equiv.Perm (Fin 42)}
    (hqsurj : ∀ s ∈ S, ∃ e, q e = s) {r : Equiv.Perm (Fin 42)} (hr : r ∈ R)
    (h : ∀ e, q (betaHat J (mem_coreActionKernel.mp hxK).1 e) = r * q e * r⁻¹) : r = 1 := by
  refine realization_unique hqsurj hr R.one_mem h fun e => ?_
  have hβ : betaHat J (mem_coreActionKernel.mp hxK).1 e = e := by
    obtain ⟨j, rfl⟩ := jq_surjective J e
    rw [betaHat_jq, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have h1 := (mem_coreActionKernel.mp hxK).2 j j.2
    obtain ⟨o, ho, hoe⟩ := h1
    have hoe' : (o : G) = (j : G)⁻¹ * x⁻¹ * j * x := hoe
    have e1 : (conjJ J (mem_coreActionKernel.mp hxK).1 j)⁻¹ * j = o⁻¹ := by
      apply Subtype.ext
      show (x⁻¹ * (j : G) * x)⁻¹ * j = (o : G)⁻¹
      rw [hoe']
      group
    rw [e1]
    exact inv_mem ho
  rw [hβ]
  group

theorem realization_mem_S_of_mem_withKernel {J : Subgroup G}
    {x : G} (hxN : x ∈ normalizer (J : Set G)) (hxK : x ∈ withKernel J)
    {q : Jhat J →* Equiv.Perm (Fin 42)} (hqS : ∀ e, q e ∈ S) (hqsurj : ∀ s ∈ S, ∃ e, q e = s)
    {r : Equiv.Perm (Fin 42)} (hr : r ∈ R) (h : ∀ e, q (betaHat J hxN e) = r * q e * r⁻¹) :
    r ∈ S := by
  have hkN : coreActionKernel J ≤ normalizer (J : Set G) := fun k hk =>
    (mem_coreActionKernel.mp hk).1
  obtain ⟨j, hj, k, hk, rfl⟩ : ∃ j ∈ J, ∃ k ∈ coreActionKernel J, j * k = x := by
    have hset : ((withKernel J : Subgroup G) : Set G) = (J : Set G) * (coreActionKernel J : Set G)
        := coe_mul_of_right_le_normalizer_left J (coreActionKernel J) hkN
    have hx' : x ∈ (J : Set G) * (coreActionKernel J : Set G) := by
      rw [← hset]
      exact hxK
    obtain ⟨j, hj, k, hk, hjk⟩ := hx'
    exact ⟨j, hj, k, hk, hjk⟩
  have hβ : ∀ e, betaHat J hxN e = (jq J ⟨j, hj⟩)⁻¹ * e * jq J ⟨j, hj⟩ := by
    intro e
    have e1 := betaHat_mul_apply (le_normalizer hj) (hkN hk) e
    rw [show betaHat J hxN e = betaHat J (mul_mem (le_normalizer hj) (hkN hk)) e from rfl, e1]
    have hk1 : ∀ e', betaHat J (hkN hk) e' = e' := by
      intro e'
      obtain ⟨j', rfl⟩ := jq_surjective J e'
      rw [betaHat_jq, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      obtain ⟨o, ho, hoe⟩ := (mem_coreActionKernel.mp hk).2 j' j'.2
      have hoe' : (o : G) = (j' : G)⁻¹ * k⁻¹ * j' * k := hoe
      have e2 : (conjJ J (hkN hk) j')⁻¹ * j' = o⁻¹ := by
        apply Subtype.ext
        show (k⁻¹ * (j' : G) * k)⁻¹ * j' = (o : G)⁻¹
        rw [hoe']
        group
      rw [e2]
      exact inv_mem ho
    rw [hk1]
    obtain ⟨j', rfl⟩ := jq_surjective J e
    rw [betaHat_jq, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hr' : r = (q (jq J ⟨j, hj⟩))⁻¹ := by
    refine realization_unique hqsurj hr (R.inv_mem (S_le_R (hqS _))) h fun e => ?_
    rw [hβ, map_mul, map_mul, map_inv, inv_inv]
  rw [hr']
  exact S.inv_mem (hqS _)

theorem conj_eq_iff_betaHat [Finite G] {J P : Subgroup G} (hPJ : P ≤ J) (hP : IsPGroup 2 P)
    {x : G} (hxN : x ∈ normalizer (J : Set G)) (hxP : x ∈ normalizer (P : Set G)) {p : G}
    (hp : p ∈ P) : x⁻¹ * p * x = p ↔ betaHat J hxN (jq J ⟨p, hPJ hp⟩) = jq J ⟨p, hPJ hp⟩ := by
  rw [betaHat_jq]
  constructor
  · intro h
    congr 1
    apply Subtype.ext
    rw [coe_conjJ]
    exact h
  · intro h
    have hpx : x⁻¹ * p * x ∈ P := conj_mem_of_mem_normalizer hxP hp
    exact eq_of_jq_eq hPJ hP hpx hp (by rw [← h]; rfl)

end CFSG.ComponentClassification.GrSLit.GrS4
