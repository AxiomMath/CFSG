module

public import CFSG.CGT.Timmesfeld75.Sec4CaseIIIKappa2

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T T₁ T₂ : Subgroup G} {a : G}

theorem Sec4Hyp.false_of_diag (h : Sec4Hyp T T₁ a T₂)
    (hq : Nat.card T = 2 * Nat.card (normIn T T₁)) {z s ℓ u : G} (hs : s ∈ T)
    (hzT : z ∈ Subgroup.normalizer (T : Set G))
    (hzL : ∀ l ∈ normIn T T₁, z * l * z⁻¹ ∈ normIn T T₁) (hℓ : ℓ ∈ normIn T T₁)
    (hzℓ : z * ℓ ≠ ℓ * z) (hu : u ∈ normIn T T₁)
    (hvals : ∀ r ∈ T, ⁅r, z⁆ = 1 ∨ ⁅r, z⁆ = u)
    (h₁ : conjSubgroup z T₁ = conjSubgroup s T₁) (h₂ : conjSubgroup z T₂ = conjSubgroup s T₂) :
    False := by
  have hT := h.pair.wc.1
  have hκT : s⁻¹ * z ∈ Subgroup.normalizer (T : Set G) :=
    (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).inv_mem (Subgroup.le_normalizer hs))
      hzT
  have hκ : ∀ V : Subgroup G, conjSubgroup z V = conjSubgroup s V →
      s⁻¹ * z ∈ Subgroup.normalizer (V : Set G) := by
    intro V hV
    apply mem_normalizer_of_conjSubgroup_eq
    rw [← conjSubgroup_conjSubgroup, hV, conjSubgroup_conjSubgroup, inv_mul_cancel,
      conjSubgroup_one]
  have hℓκ : (s⁻¹ * z) * ℓ ≠ ℓ * (s⁻¹ * z) := by
    intro hc
    apply hzℓ
    have hsℓ : s⁻¹ * ℓ = ℓ * s⁻¹ := elemAbelian_mul_comm hT (T.inv_mem hs) (normIn_le T T₁ hℓ)
    calc z * ℓ = s * (s⁻¹ * z * ℓ) := by group
      _ = s * (ℓ * (s⁻¹ * z)) := by rw [hc]
      _ = s * ((ℓ * s⁻¹) * z) := by group
      _ = s * ((s⁻¹ * ℓ) * z) := by rw [hsℓ]
      _ = ℓ * z := by group
  have hcomm : ∀ m ∈ normIn T T₁, ⁅s⁻¹ * z, m⁆ = ⁅z, m⁆ := by
    intro m hm
    have hw : z * m * z⁻¹ ∈ T := normIn_le T T₁ (hzL m hm)
    have hsw : s⁻¹ * (z * m * z⁻¹) = (z * m * z⁻¹) * s⁻¹ :=
      elemAbelian_mul_comm hT (T.inv_mem hs) hw
    calc ⁅s⁻¹ * z, m⁆ = (s⁻¹ * (z * m * z⁻¹)) * s * m⁻¹ := by
          simp only [commutatorElement_def]
          group
      _ = ((z * m * z⁻¹) * s⁻¹) * s * m⁻¹ := by rw [hsw]
      _ = ⁅z, m⁆ := by
          simp only [commutatorElement_def]
          group
  have hconst : ∀ l ∈ normIn T T₁, ∀ l' ∈ normIn T T₁, (s⁻¹ * z) * l ≠ l * (s⁻¹ * z) →
      (s⁻¹ * z) * l' ≠ l' * (s⁻¹ * z) → ⁅s⁻¹ * z, l⁆ = ⁅s⁻¹ * z, l'⁆ := by
    have key : ∀ m ∈ normIn T T₁, (s⁻¹ * z) * m ≠ m * (s⁻¹ * z) → ⁅s⁻¹ * z, m⁆ = u := by
      intro m hm hn
      rw [hcomm m hm]
      have hmT : m ∈ T := normIn_le T T₁ hm
      rcases hvals m hmT with h0 | h0
      · exfalso
        apply hn
        have hzm : z * m = m * z := by
          have := commutatorElement_eq_one_iff_mul_comm.1 h0
          exact this.symm
        have hsm : s⁻¹ * m = m * s⁻¹ := elemAbelian_mul_comm hT (T.inv_mem hs) hmT
        calc s⁻¹ * z * m = s⁻¹ * (z * m) := by group
          _ = s⁻¹ * (m * z) := by rw [hzm]
          _ = (m * s⁻¹) * z := by rw [← hsm]; group
          _ = m * (s⁻¹ * z) := by group
      · rw [← commutatorElement_inv, h0]
        exact elemAbelian_inv (isElemAbelian_of_le hT (normIn_le T T₁)) hu
    intro l hl l' hl' hn hn'
    rw [key l hl hn, key l' hl' hn']
  exact h.false_of_kappa hq hκT (hκ T₁ h₁) (hκ T₂ h₂) hℓ hℓκ hconst

end CFSG.CGT.Timmesfeld75
