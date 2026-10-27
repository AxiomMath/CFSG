module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxOutNFAltIIPerm
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxNFOrbFamily

public section

namespace CFSG.ComponentClassification.SolMax.NFOrb

open Equiv Subgroup

variable {α : Type*}

@[expose] def baseGroup (σ : Perm α) (hσ : σ * σ = 1) : Subgroup (Perm α) where
  carrier := {w | ∀ v, w v = v ∨ w v = σ v}
  mul_mem' := by
    intro w₁ w₂ h₁ h₂ v
    have hσσ : σ (σ v) = v := by rw [← Perm.mul_apply, hσ, Perm.one_apply]
    rcases h₂ v with h | h
    · rw [Perm.mul_apply, h]
      exact h₁ v
    · rw [Perm.mul_apply, h]
      rcases h₁ (σ v) with h' | h'
      · exact Or.inr h'
      · exact Or.inl (h'.trans hσσ)
  one_mem' := fun _ => Or.inl rfl
  inv_mem' := by
    intro w hw v
    have hwu : w (w⁻¹ v) = v := perm_apply_inv w v
    rcases hw (w⁻¹ v) with h | h
    · exact Or.inl (h.symm.trans hwu)
    · right
      have hσσ : σ (σ (w⁻¹ v)) = w⁻¹ v := by rw [← Perm.mul_apply, hσ, Perm.one_apply]
      have h1 : σ (w⁻¹ v) = v := h.symm.trans hwu
      rw [← hσσ, h1]

variable {σ : Perm α} {hσ : σ * σ = 1}

theorem commute_sigma_of_mem_baseGroup {u : Perm α} (hu : u ∈ baseGroup σ hσ) (v : α) :
    u (σ v) = σ (u v) := by
  have hσσ : σ (σ v) = v := by rw [← Perm.mul_apply, hσ, Perm.one_apply]
  rcases hu v with h | h <;> rcases hu (σ v) with h' | h'
  · rw [h, h']
  · have hv : σ v = v := u.injective (h'.trans (hσσ.trans h.symm))
    rw [h, h', hσσ, hv]
  · have hv : σ v = v := u.injective (h'.trans h.symm)
    rw [h, h', hσσ, hv]
  · rw [h, h']

theorem mul_self_of_mem_baseGroup {u : Perm α} (hu : u ∈ baseGroup σ hσ) : u * u = 1 := by
  ext v
  rw [Perm.mul_apply, Perm.one_apply]
  have hσσ : σ (σ v) = v := by rw [← Perm.mul_apply, hσ, Perm.one_apply]
  rcases hu v with h | h
  · rw [h, h]
  · rw [h, commute_sigma_of_mem_baseGroup hu, h, hσσ]

theorem baseGroup_commute {u₁ u₂ : Perm α} (h₁ : u₁ ∈ baseGroup σ hσ) (h₂ : u₂ ∈ baseGroup σ hσ) :
    u₁ * u₂ = u₂ * u₁ := by
  ext v
  rw [Perm.mul_apply, Perm.mul_apply]
  rcases h₂ v with h | h <;> rcases h₁ v with h' | h'
  · rw [h, h', h]
  · rw [h, h', commute_sigma_of_mem_baseGroup h₂, h]
  · rw [h, h', commute_sigma_of_mem_baseGroup h₁, h', h]
  · rw [h, h', commute_sigma_of_mem_baseGroup h₁, commute_sigma_of_mem_baseGroup h₂, h, h']

theorem conj_mem_baseGroup {w u : Perm α} (hw : w * σ = σ * w) (hu : u ∈ baseGroup σ hσ) :
    w * u * w⁻¹ ∈ baseGroup σ hσ := by
  intro v
  rw [Perm.mul_apply, Perm.mul_apply]
  rcases hu (w⁻¹ v) with h | h
  · left
    rw [h, perm_apply_inv]
  · right
    rw [h, ← Perm.mul_apply w σ, hw, Perm.mul_apply, perm_apply_inv]

variable [DecidableEq α]

theorem swap_mem_baseGroup {q : α} : swap q (σ q) ∈ baseGroup σ hσ := by
  intro v
  have hσσ : σ (σ q) = q := by rw [← Perm.mul_apply, hσ, Perm.one_apply]
  by_cases hvq : v = q
  · subst hvq
    exact Or.inr (swap_apply_left _ _)
  by_cases hvσ : v = σ q
  · subst hvσ
    right
    rw [swap_apply_right, hσσ]
  · exact Or.inl (swap_apply_of_ne_of_ne hvq hvσ)

variable [Fintype α]

theorem mem_baseGroup_of_mem_cycleFactorsFinset {c : Perm α} (hc : c ∈ σ.cycleFactorsFinset) :
    c ∈ baseGroup σ hσ := by
  obtain ⟨q, -, rfl⟩ := exists_swap_eq_of_mem_cycleFactorsFinset hσ hc
  exact swap_mem_baseGroup

theorem mul_mem_oddCentGen_of_mem_cycleFactorsFinset (hσ : σ * σ = 1) (h6 : 6 ≤ σ.support.card)
    {c d : Perm α}
    (hc : c ∈ σ.cycleFactorsFinset) (hd : d ∈ σ.cycleFactorsFinset) : c * d ∈ oddCentGen σ := by
  classical
  have hσσ : ∀ v, σ (σ v) = v := fun v => by rw [← Perm.mul_apply, hσ, Perm.one_apply]
  by_cases hcd : c = d
  · subst hcd
    rw [mul_self_of_mem_baseGroup (mem_baseGroup_of_mem_cycleFactorsFinset (hσ := hσ) hc)]
    exact one_mem _
  obtain ⟨q, hq, rfl⟩ := exists_swap_eq_of_mem_cycleFactorsFinset hσ hc
  obtain ⟨r, hr, rfl⟩ := exists_swap_eq_of_mem_cycleFactorsFinset hσ hd
  obtain ⟨p, hp, hpn⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({q, σ q, r, σ r} : Finset α)) (t := σ.support)
    (lt_of_le_of_lt Finset.card_le_four (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpn
  have hrq : r ≠ q := fun h => hcd (by rw [h])
  have hrσq : r ≠ σ q := fun h => hcd (by rw [h, hσσ, swap_comm])
  exact pair_mem_oddCentGen hσ (Perm.mem_support.mp hp) (Perm.mem_support.mp hq)
    (Perm.mem_support.mp hr) (Ne.symm hpn.1) (fun h => hpn.2.1 (by rw [h, hσσ]))
    (Ne.symm hpn.2.2.1) (fun h => hpn.2.2.2 (by rw [h, hσσ])) hrq hrσq

end CFSG.ComponentClassification.SolMax.NFOrb
