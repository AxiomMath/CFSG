module

public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem sec5pe8_restrict {Y : Type} [Group Y] [Finite Y] (J : Subgroup Y) [J.Normal]
    [IsSimpleGroup ↥J] (hc : centralizer (J : Set Y) = ⊥) (κ : MulAut Y) :
    ∃ κJ : MulAut ↥J, (∀ x : ↥J, ((κJ x : ↥J) : Y) = κ x) ∧ orderOf κJ ∣ orderOf κ ∧
      (κJ = 1 → κ = 1) := by
  have hmap_gen : ∀ ϕ : MulAut Y, J.map (ϕ : Y →* Y) = J := by
    intro ϕ
    let J' : Subgroup Y := J.map (ϕ : Y →* Y)
    have hJ'normal : J'.Normal :=
      Subgroup.Normal.map (inferInstance : J.Normal) (ϕ : Y →* Y) ϕ.surjective
    haveI : J'.Normal := hJ'normal
    have hcard : Nat.card J' = Nat.card J :=
      Subgroup.card_map_of_injective (K := J) (f := (ϕ : Y →* Y)) ϕ.injective
    have hK : (J ⊓ J').subgroupOf J = ⊥ ∨ (J ⊓ J').subgroupOf J = ⊤ :=
      Subgroup.Normal.eq_bot_or_eq_top _
    rcases hK with hbot | htop
    ·
      exfalso
      have hdisj : Disjoint (J ⊓ J') J := subgroupOf_eq_bot.mp hbot
      have hinf : J ⊓ J' = ⊥ := by
        have hle : J ⊓ J' ≤ (J ⊓ J') ⊓ J := le_inf le_rfl inf_le_left
        exact le_bot_iff.mp (hle.trans (disjoint_iff.mp hdisj).le)
      have hJ'le : J' ≤ centralizer (J : Set Y) := by
        intro b hb
        rw [mem_centralizer_iff]
        intro a ha
        have hmem : a * b * a⁻¹ * b⁻¹ ∈ J ⊓ J' := by
          rw [Subgroup.mem_inf]
          constructor
          · simpa only [mul_assoc] using
              J.mul_mem ha (Subgroup.Normal.conj_mem (inferInstance : J.Normal) (a⁻¹)
                (J.inv_mem ha) b)
          · simpa only [mul_assoc] using
              J'.mul_mem (Subgroup.Normal.conj_mem (inferInstance : J'.Normal) b hb a)
                (J'.inv_mem hb)
        have h1 : a * b * a⁻¹ * b⁻¹ = 1 := by
          have : a * b * a⁻¹ * b⁻¹ ∈ (⊥ : Subgroup Y) := hinf ▸ hmem
          simpa using this
        exact mul_inv_eq_one.mp (by simpa [mul_inv_rev, mul_assoc] using h1)
      have hJ'bot : J' = ⊥ := le_bot_iff.mp (hc ▸ hJ'le)
      haveI : Nontrivial ↥J' := (MulEquiv.subgroupMap ϕ J).symm.toEquiv.nontrivial
      exact (Subgroup.nontrivial_iff_ne_bot J').mp inferInstance hJ'bot
    ·
      have hle : J ≤ J' := fun x hx => (subgroupOf_eq_top.mp htop hx).2
      exact (Subgroup.eq_of_le_of_card_ge hle hcard.le).symm
  haveI : J.Characteristic := Subgroup.characteristic_iff_map_eq.mpr hmap_gen
  refine ⟨MulAut.characteristic J κ, ?_, ?_, ?_⟩
  · intro x
    exact MulAut.characteristic_apply_apply_coe J κ x
  · exact orderOf_map_dvd (MulAut.characteristic J) κ
  ·
    intro hκJ
    have hfix : ∀ g : Y, g ∈ J → κ g = g := by
      intro g hg
      have h := MulAut.characteristic_apply_apply_coe J κ ⟨g, hg⟩
      rw [hκJ] at h
      simpa using h.symm
    ext y
    have hcy : κ y = y := by
      have hmem : y⁻¹ * κ y ∈ centralizer (J : Set Y) := by
        rw [mem_centralizer_iff]
        intro f hf
        have hconj : κ y * f * (κ y)⁻¹ = y * f * y⁻¹ := by
          have hb : y * f * y⁻¹ ∈ J :=
            Subgroup.Normal.conj_mem (inferInstance : J.Normal) f hf y
          have h1 : κ (y * f * y⁻¹) = y * f * y⁻¹ := hfix _ hb
          have h3 : κ (y * f * y⁻¹) = κ y * f * (κ y)⁻¹ := by
            simp only [map_mul, map_inv, hfix f hf]
          rw [← h3, h1]
        have hright : y⁻¹ * (y * f * y⁻¹) * y = f := by
          simp [mul_assoc]
        have h2 : (y⁻¹ * κ y) * f * (y⁻¹ * κ y)⁻¹ = f := by
          have h' := congrArg (fun t => y⁻¹ * t * y) hconj
          rw [hright] at h'
          simpa only [mul_inv_rev, inv_inv, mul_assoc] using h'
        exact (mul_inv_eq_iff_eq_mul.mp h2).symm
      have h1 : y⁻¹ * κ y = 1 := by
        have h2 := hmem
        rw [hc] at h2
        simpa using h2
      exact (inv_mul_eq_one.mp h1).symm
    simpa using hcy

end CFSG.OddStandard.SmallF3.Omega
