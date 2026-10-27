module

public import Mathlib.GroupTheory.SpecificGroups.Quaternion

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec7.IV2

open Subgroup QuaternionGroup

variable {G : Type*} [Group G]

theorem q16_invol : ∀ g : QuaternionGroup 4, g * g = 1 → g = 1 ∨ g = a 4 := by decide

theorem q16_central_sq :
    ∀ g : QuaternionGroup 4, (∀ h : QuaternionGroup 4, g * h = h * g) → g * g = 1 := by decide

theorem q16_central_ex :
    ∃ g : QuaternionGroup 4, g ≠ 1 ∧ ∀ h : QuaternionGroup 4, g * h = h * g := by decide

theorem q8_invol : ∀ g : QuaternionGroup 2, g * g = 1 → g = 1 ∨ g = a 2 := by decide

theorem q8_sq : ∀ g : QuaternionGroup 2, g ≠ 1 → g ≠ a 2 → g * g = a 2 := by decide

theorem q8_a2 : (a 2 : QuaternionGroup 2) ≠ 1 ∧ (a 2 : QuaternionGroup 2) * a 2 = 1 ∧
    ∀ h : QuaternionGroup 2, (a 2 : QuaternionGroup 2) * h = h * a 2 := by decide

theorem quat16_facts {Q : Subgroup G} (e : ↥Q ≃* QuaternionGroup 4) {z : G}
    (hz : (center ↥Q).map Q.subtype = zpowers z) :
    z ∈ Q ∧ z ≠ 1 ∧ z * z = 1 ∧ (∀ g ∈ Q, z * g = g * z) ∧
      (∀ g ∈ Q, g * g = 1 → g = 1 ∨ g = z) ∧ Nat.card ↥Q = 16 := by
  have hzmem : z ∈ (center ↥Q).map Q.subtype := hz ▸ mem_zpowers z
  obtain ⟨c, hc, hcz⟩ := hzmem
  have hcz' : (c : G) = z := hcz
  have hcc : ∀ h : ↥Q, h * c = c * h := fun h => Subgroup.mem_center_iff.1 hc h
  have hec : ∀ h : QuaternionGroup 4, e c * h = h * e c := by
    intro h
    have := congrArg e (hcc (e.symm h))
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at this
    exact this.symm
  have hec2 : e c * e c = 1 := q16_central_sq _ hec
  have hcsq : c * c = 1 := e.injective (by rw [map_mul, hec2, map_one])
  obtain ⟨g₀, hg₀1, hg₀c⟩ := q16_central_ex
  have hc1 : c ≠ 1 := by
    intro hc1
    have hz1 : z = 1 := by rw [← hcz', hc1]; rfl
    have hg : (e.symm g₀ : ↥Q) ∈ center ↥Q := by
      rw [Subgroup.mem_center_iff]
      intro h
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact (hg₀c (e h)).symm
    have : ((e.symm g₀ : ↥Q) : G) ∈ (center ↥Q).map Q.subtype := ⟨_, hg, rfl⟩
    rw [hz, hz1, zpowers_one_eq_bot, Subgroup.mem_bot] at this
    apply hg₀1
    have h2 : e.symm g₀ = 1 := Subtype.ext this
    rw [← MulEquiv.apply_symm_apply e g₀, h2, map_one]
  have hz1 : z ≠ 1 := fun h => hc1 (Subtype.ext (hcz'.trans h))
  have hea4 : e c = a 4 := ((q16_invol _ hec2).resolve_left fun h => hc1 (e.injective (h.trans (map_one e).symm)))
  refine ⟨hcz' ▸ c.2, hz1, ?_, ?_, ?_, ?_⟩
  · rw [← hcz']
    exact congrArg Subtype.val hcsq
  · intro g hg
    rw [← hcz']
    exact (congrArg Subtype.val (hcc ⟨g, hg⟩)).symm
  · intro g hg hg2
    have h1 : e ⟨g, hg⟩ * e ⟨g, hg⟩ = 1 := by
      rw [← map_mul]
      have : (⟨g, hg⟩ : ↥Q) * ⟨g, hg⟩ = 1 := Subtype.ext hg2
      rw [this, map_one]
    rcases q16_invol _ h1 with h | h
    · left
      have := e.injective (h.trans (map_one e).symm)
      exact congrArg Subtype.val this
    · right
      have := e.injective (h.trans hea4.symm)
      rw [← hcz']
      exact congrArg Subtype.val this
  · rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem quat8_facts {P : Subgroup G} (f : ↥P ≃* QuaternionGroup 2) :
    ∃ z₀ ∈ P, z₀ ≠ 1 ∧ z₀ * z₀ = 1 ∧ (∀ g ∈ P, z₀ * g = g * z₀) ∧
      (∀ g ∈ P, g * g = 1 → g = 1 ∨ g = z₀) ∧ (∀ g ∈ P, g ≠ 1 → g ≠ z₀ → g * g = z₀) ∧
      Nat.card ↥P = 8 := by
  obtain ⟨h1, h2, h3⟩ := q8_a2
  have hf : ∀ g : ↥P, f g = a 2 ↔ g = f.symm (a 2) := fun g => (MulEquiv.eq_symm_apply f).symm
  refine ⟨((f.symm (a 2) : ↥P) : G), (f.symm (a 2)).2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    apply h1
    have : f.symm (a 2) = 1 := Subtype.ext h
    rw [← MulEquiv.apply_symm_apply f (a 2), this, map_one]
  · rw [← Subgroup.coe_mul]
    have : f.symm (a 2) * f.symm (a 2) = 1 := by rw [← map_mul, h2, map_one]
    rw [this]; rfl
  · intro g hg
    have := congrArg f.symm (h3 (f ⟨g, hg⟩))
    rw [map_mul, map_mul, MulEquiv.symm_apply_apply] at this
    exact congrArg Subtype.val this
  · intro g hg hg2
    have h1' : f ⟨g, hg⟩ * f ⟨g, hg⟩ = 1 := by
      rw [← map_mul]
      have : (⟨g, hg⟩ : ↥P) * ⟨g, hg⟩ = 1 := Subtype.ext hg2
      rw [this, map_one]
    rcases q8_invol _ h1' with h | h
    · left
      exact congrArg Subtype.val (f.injective (h.trans (map_one f).symm))
    · right
      exact congrArg Subtype.val ((hf ⟨g, hg⟩).1 h)
  · intro g hg hg1 hgz
    have hne1 : f ⟨g, hg⟩ ≠ 1 := fun h => hg1 (congrArg Subtype.val (f.injective (h.trans (map_one f).symm)))
    have hne2 : f ⟨g, hg⟩ ≠ a 2 := fun h => hgz (congrArg Subtype.val ((hf ⟨g, hg⟩).1 h))
    have := q8_sq _ hne1 hne2
    have h3' : f (⟨g, hg⟩ * ⟨g, hg⟩) = a 2 := by rw [map_mul]; exact this
    have h4 := (hf _).1 h3'
    exact congrArg Subtype.val h4
  · rw [Nat.card_congr f.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]

end CFSG.GH74.GLS.Stage1.Thm3.Sec7.IV2
