module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Lemma315SzR2

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G]

namespace Sec3

variable {L T R R₂ : Subgroup G} {a : ℕ} {y d : G}

namespace SzR

variable (hS : SzR G L T R a y d)
include hS

theorem commute_gmsA {r : G} (hr : r ∈ R) {b : G} (hb : b ∈ gmsA L T) : r * b = b * r :=
  commute_of_mem_gmsTrans (hS.isR.le_gmsTrans hr) hb

theorem mem_gmsA_of_forall_commute
    (hR₂ : IsR₂ L T R R₂ d) {z : G} (hz : z ∈ R) (hzc : ∀ r ∈ R, r * z = z * r) :
    z ∈ gmsA L T := by
  have hzT : z ∈ T := by
    rw [← hS.inf_centralizer_R]
    exact mem_inf.mpr ⟨hz, mem_centralizer_iff.mpr fun v hv => hzc v (hS.gmsV_le_R hv)⟩
  obtain ⟨t₁, ht₁, s, hs, rfl⟩ := hS.exists_mul_of_mem_T hzT
  have hst : ∀ x ∈ T ⊓ L, x * s = s * x := fun x hx =>
    mem_centralizer_iff.mp (mem_inf.mp hs).2 x (mem_inf.mp hx).2
  have ht₁A : t₁ ∈ gmsA L T := by
    refine mem_inf.mpr ⟨ht₁, mem_centralizer_iff.mpr fun x hx => ?_⟩
    have h1 := hzc x (hS.T_le (mem_inf.mp hx).1)
    have h2 := hst x hx
    calc x * t₁ = x * (t₁ * s) * s⁻¹ := by group
      _ = t₁ * s * x * s⁻¹ := by rw [h1]
      _ = t₁ * (s * x) * s⁻¹ := by group
      _ = t₁ * (x * s) * s⁻¹ := by rw [h2]
      _ = t₁ * x := by group
  by_cases hs1 : s = 1
  · rw [hs1, mul_one]
    exact ht₁A
  exfalso
  obtain ⟨r, hr, hrA⟩ := hS.exists_mem_isR₂_not_mem_gmsA hR₂
  apply hrA
  rw [← hS.commutator_eq_one_iff hR₂ hs hs1 hr]
  have h1 := hzc r (hR₂.le_R hr)
  have h2 := hS.commute_gmsA (hR₂.le_R hr) ht₁A
  have hrs : r * s = s * r := by
    calc r * s = t₁⁻¹ * (t₁ * r) * s := by group
      _ = t₁⁻¹ * (r * t₁) * s := by rw [← h2]
      _ = t₁⁻¹ * (r * (t₁ * s)) := by group
      _ = t₁⁻¹ * (t₁ * s * r) := by rw [h1]
      _ = s * r := by group
  rw [hrs]
  group

theorem rightConjugate_eq_or_inf_eq
    (hR₂ : IsR₂ L T R R₂ d) {g : G} (hg : g ∈ normalizer (R : Set G)) :
    rightConjugate (gmsV L T) g = gmsV L T ∨
      rightConjugate (gmsV L T) g ⊓ gmsV L T = gmsA L T := by
  obtain ⟨-, hVel, -, -, hΩ⟩ := hS.facts.vFacts hS.sec3 hS.foundation
  have hconjR : ∀ h ∈ normalizer (R : Set G), ∀ b ∈ gmsA L T, h * b * h⁻¹ ∈ gmsA L T := by
    intro h hh b hb
    refine hS.mem_gmsA_of_forall_commute hR₂
      ((mem_normalizer_iff.mp hh b).mp (hR₂.le_R (hR₂.gmsA_le hb))) fun r hr => ?_
    have hr' : h⁻¹ * r * h ∈ R := by
      have := (mem_normalizer_iff.mp (inv_mem hh) r).mp hr
      simpa using this
    have hc := hS.commute_gmsA hr' hb
    calc r * (h * b * h⁻¹) = h * (h⁻¹ * r * h * b) * h⁻¹ := by group
      _ = h * (b * (h⁻¹ * r * h)) * h⁻¹ := by rw [hc]
      _ = h * b * h⁻¹ * r := by group
  have hgA : g ∈ normalizer (gmsA L T : Set G) :=
    mem_normalizer_of_conj_mem_of_finite (hconjR g hg)
  have hgA' : g⁻¹ ∈ normalizer (gmsA L T : Set G) := inv_mem hgA
  have hAle : gmsA L T ≤ rightConjugate (gmsV L T) g ⊓ gmsV L T := by
    intro b hb
    refine mem_inf.mpr ⟨?_, mem_sup_left hb⟩
    rw [mem_rightConjugate_iff]
    exact mem_sup_left ((mem_normalizer_iff.mp hgA b).mp hb)
  by_cases hc : rightConjugate (gmsV L T) g ⊓ gmsV L T = gmsA L T
  · exact Or.inr hc
  left
  obtain ⟨x, hx, hxA⟩ : ∃ x ∈ rightConjugate (gmsV L T) g ⊓ gmsV L T, x ∉ gmsA L T := by
    by_contra hcon
    push Not at hcon
    exact hc (le_antisymm hcon hAle)
  obtain ⟨hxg, hxV⟩ := mem_inf.mp hx
  rw [mem_rightConjugate_iff] at hxg
  have hx'A : g * x * g⁻¹ ∉ gmsA L T := fun h => hxA (by
    have := (mem_normalizer_iff.mp hgA' _).mp h
    simpa [mul_assoc] using this)
  obtain ⟨Q, hQ, hx'Q, -⟩ := (hS.lemma313.cover _ hxg).mp hx'A
  have hQg : ∀ z, g * z * g⁻¹ ∈ Q → z ∈ gmsV L T := by
    intro z hz
    have hzR : z ∈ R := by
      have := (mem_normalizer_iff.mp (inv_mem hg) _).mp (hS.gmsV_le_R (hQ.2 hz))
      simpa [mul_assoc] using this
    have hcomm : z * x = x * z := by
      have hQab : g * z * g⁻¹ * (g * x * g⁻¹) = g * x * g⁻¹ * (g * z * g⁻¹) :=
        congrArg Subtype.val (hVel.1.is_comm.comm ⟨_, hQ.2 hz⟩ ⟨_, hQ.2 hx'Q⟩)
      have e1 : g * z * g⁻¹ * (g * x * g⁻¹) = g * (z * x) * g⁻¹ := by group
      have e2 : g * x * g⁻¹ * (g * z * g⁻¹) = g * (x * z) * g⁻¹ := by group
      rw [e1, e2] at hQab
      exact mul_left_cancel (mul_right_cancel hQab)
    have hzT : z ∈ T := by
      by_contra hzT
      have hzC : z ∉ centralizer (gmsV L T : Set G) := fun hzC => hzT (by
        rw [← hS.inf_centralizer_R]
        exact mem_inf.mpr ⟨hzR, hzC⟩)
      exact hxA (mem_gmsA_of_commute hS.lemma313 hS.facts hS.sec3 hS.foundation
        (hS.isR.le_gmsTrans hzR) hzC hxV hcomm)
    have hz2 : z ^ 2 = 1 := by
      have h1 := hVel.2 _ (hQ.2 hz)
      have e : (g * z * g⁻¹) ^ 2 = g * z ^ 2 * g⁻¹ := by rw [sq, sq]; group
      rw [e] at h1
      have := congrArg (fun w => g⁻¹ * w * g) h1
      simpa [mul_assoc] using this
    exact hΩ z (by rw [hS.eq_gmsW] at hzT; exact hzT) hz2
  have hle : rightConjugate (gmsV L T) g ≤ gmsV L T := by
    intro w hw
    rw [mem_rightConjugate_iff] at hw
    obtain ⟨b, hb, hbw⟩ := hS.lemma313.exists_mul_mem hS.facts hS.sec3 hS.foundation hQ hw
    have e : w = (g⁻¹ * b⁻¹ * g) * (g⁻¹ * (b * (g * w * g⁻¹)) * g) := by group
    rw [e]
    refine mul_mem (mem_sup_left ?_) (hQg _ (by simpa [mul_assoc] using hbw))
    have := (mem_normalizer_iff.mp hgA' _).mp (inv_mem hb)
    simpa [mul_assoc] using this
  exact eq_of_le_of_card_ge hle (by rw [rightConjugate_card])

end SzR

end Sec3

end CFSG.ComponentClassification.GMS78
