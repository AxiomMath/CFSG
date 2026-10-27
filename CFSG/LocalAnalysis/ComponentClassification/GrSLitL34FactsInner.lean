
module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsStandardBase

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup
open CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G]

theorem betaHat_mul (J : Subgroup G) {g h : G} (hg : g ∈ normalizer (J : Set G))
    (hh : h ∈ normalizer (J : Set G)) (e : Jhat J) :
    betaHat J (mul_mem hg hh) e = betaHat J hh (betaHat J hg e) := by
  obtain ⟨j, rfl⟩ := jq_surjective J e
  rw [betaHat_jq, betaHat_jq, betaHat_jq]
  congr 1
  apply Subtype.ext
  simp only [coe_conjJ]
  group

theorem betaHat_eq_self (J : Subgroup G) {x : G} (hx : x ∈ normalizer (J : Set G)) (h : x = 1)
    (e : Jhat J) : betaHat J hx e = e := by
  subst h
  obtain ⟨j, rfl⟩ := jq_surjective J e
  rw [betaHat_jq]
  congr 1
  apply Subtype.ext
  simp [coe_conjJ]

theorem betaHat_of_mem_coreActionKernel {J : Subgroup G} {k : G}
    (hk : k ∈ coreActionKernel J) (hkN : k ∈ normalizer (J : Set G)) (e : Jhat J) :
    betaHat J hkN e = e := by
  obtain ⟨j, rfl⟩ := jq_surjective J e
  rw [betaHat_jq]
  have hmem : (j : G)⁻¹ * k⁻¹ * j * k ∈ J := by
    have := conj_mem_of_mem_normalizer hkN j.2
    rw [show (j : G)⁻¹ * k⁻¹ * j * k = (j : G)⁻¹ * (k⁻¹ * j * k) by group]
    exact J.mul_mem (J.inv_mem j.2) this
  have h1 := (mem_oddIn_iff hmem).1 ((mem_coreActionKernel.mp hk).2 j j.2)
  have e1 : (⟨(j : G)⁻¹ * k⁻¹ * j * k, hmem⟩ : J) = j⁻¹ * conjJ J hkN j := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjJ]
    group
  rw [e1, map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1.symm

@[expose] noncomputable def innerActing (J : Subgroup G) : Subgroup G where
  carrier := {g | ∃ hg : g ∈ normalizer (J : Set G), ∃ e₀ : Jhat J,
    ∀ e, betaHat J hg e = e₀⁻¹ * e * e₀}
  one_mem' := ⟨one_mem _, 1, fun e => by
    rw [betaHat_eq_self J _ rfl, inv_one, one_mul, mul_one]⟩
  mul_mem' := by
    rintro g h ⟨hg, a, ha⟩ ⟨hh, b, hb⟩
    refine ⟨mul_mem hg hh, a * b, fun e => ?_⟩
    rw [betaHat_mul J hg hh, ha, hb]
    group
  inv_mem' := by
    rintro g ⟨hg, a, ha⟩
    refine ⟨inv_mem hg, a⁻¹, fun e => ?_⟩
    have h1 : betaHat J hg (a * e * a⁻¹) = e := by
      rw [ha]
      group
    have h2 := betaHat_mul J hg (inv_mem hg) (a * e * a⁻¹)
    rw [betaHat_eq_self J _ (mul_inv_cancel g), h1] at h2
    rw [← h2, inv_inv]

theorem le_innerActing (J : Subgroup G) : J ≤ innerActing J := fun j hj =>
  ⟨le_normalizer hj, jq J ⟨j, hj⟩, fun e => by
    obtain ⟨i, rfl⟩ := jq_surjective J e
    rw [betaHat_jq, ← map_inv, ← map_mul, ← map_mul]
    congr 1⟩

theorem coreActionKernel_le_innerActing (J : Subgroup G) :
    coreActionKernel J ≤ innerActing J := fun k hk =>
  ⟨(mem_coreActionKernel.mp hk).1, 1, fun e => by
    rw [betaHat_of_mem_coreActionKernel hk, inv_one, one_mul, mul_one]⟩

theorem withKernel_le_innerActing (J : Subgroup G) : withKernel J ≤ innerActing J :=
  sup_le (le_innerActing J) (coreActionKernel_le_innerActing J)

theorem exists_inner {J : Subgroup G} {x : G} (hx : x ∈ withKernel J)
    (hxN : x ∈ normalizer (J : Set G)) : ∃ e₀ : Jhat J, ∀ e, betaHat J hxN e = e₀⁻¹ * e * e₀ := by
  obtain ⟨_, e₀, he₀⟩ := withKernel_le_innerActing J hx
  exact ⟨e₀, he₀⟩

end CFSG.ComponentClassification.GrSLit.L34Facts
