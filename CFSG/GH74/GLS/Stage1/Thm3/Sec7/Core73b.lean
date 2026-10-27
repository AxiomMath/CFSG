module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Core73
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Basic

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec7.C73

open Subgroup CFSG.GH74.GLS.Stage1.Thm3.Sec7

variable {G : Type*} [Group G]

namespace Ctx73

variable {z t : G} {S P₁ P₂ Q₁ Q₂ S₁ : Subgroup G} (c : Ctx73 z t S P₁ P₂ Q₁ Q₂ S₁)

include c

theorem four_mem (h4 : (P₁ ⊔ P₂).relIndex S₁ = 4) {s : G} (hs : s ∈ S) : s ^ 4 ∈ P₁ ⊔ P₂ := by
  have h1 : s * s ∈ S₁ := A.sq_mem_of_relIndex_two c.S₁idx hs
  have h2 := c.d₂ h4 _ h1
  have e : s ^ 4 = s * s * (s * s) := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
  rwa [e]

theorem relIdx8 (h4 : (P₁ ⊔ P₂).relIndex S₁ = 4) : (P₁ ⊔ P₂).relIndex S = 8 := by
  have := Subgroup.relIndex_mul_relIndex (P₁ ⊔ P₂) S₁ S c.P_le_S₁ c.S₁S
  rw [h4, c.S₁idx] at this
  omega

theorem card_P₁_eq_P₂ [Finite G] : Nat.card ↥P₁ = Nat.card ↥P₂ := by
  apply le_antisymm
  · refine Nat.card_le_card_of_injective (fun x : ↥P₁ => (⟨t * x * t⁻¹, c.tP₁ x x.2⟩ : ↥P₂)) ?_
    intro x y h
    have h1 := congrArg Subtype.val h
    simp only [mul_left_inj, mul_right_inj] at h1
    exact Subtype.ext h1
  · refine Nat.card_le_card_of_injective (fun x : ↥P₂ => (⟨t * x * t⁻¹, c.tP₂ x x.2⟩ : ↥P₁)) ?_
    intro x y h
    have h1 := congrArg Subtype.val h
    simp only [mul_left_inj, mul_right_inj] at h1
    exact Subtype.ext h1

theorem exists_Y_data [Finite G] (h4 : (P₁ ⊔ P₂).relIndex S₁ = 4) {v₂ : G} (hv₂ : v₂ ∈ Q₁)
    (hv₂P : v₂ ∉ P₂) :
    ∃ Y : Subgroup G, Y ≤ S ∧ Y.relIndex S = 2 ∧ P₁ ⊔ P₂ ≤ Y ∧ v₂ ∉ Y ∧
      ∀ y ∈ Y, (y ∈ P₁ ⊔ Q₁ → y ∈ P₂ ⊔ Q₂) ∧ (y ∈ P₂ ⊔ Q₂ → y ∈ P₁ ⊔ Q₁) := by
  have hv₂S₁ : v₂ ∈ S₁ := c.Q₁S₁ hv₂
  have hv₂S : v₂ ∈ S := c.S₁S hv₂S₁
  have haS : v₂ * t ∈ S := S.mul_mem hv₂S c.t_mem
  have haS₁ : v₂ * t ∉ S₁ := by
    intro h
    apply c.t_nS₁
    have := S₁.mul_mem (S₁.inv_mem hv₂S₁) h
    simpa using this
  have hc₂Q : t * v₂ * t⁻¹ ∈ Q₂ := c.tQ₁ v₂ hv₂
  have hc₂P : t * v₂ * t⁻¹ ∉ P₁ := fun h => hv₂P (c.mem_P₂_of_conj h)
  have hc₂S₁ : t * v₂ * t⁻¹ ∈ S₁ := c.Q₂S₁ hc₂Q
  have haa : (v₂ * t) * (v₂ * t) = v₂ * (t * v₂ * t⁻¹) := by
    calc (v₂ * t) * (v₂ * t) = v₂ * (t * v₂ * t⁻¹) * (t * t) := by group
      _ = v₂ * (t * v₂ * t⁻¹) := by rw [c.t_sq, mul_one]
  have hnotP : v₂ * (t * v₂ * t⁻¹) ∉ P₁ ⊔ P₂ := by
    intro h
    have h1 : t * v₂ * t⁻¹ ∈ P₁ ⊔ Q₁ := by
      have e : t * v₂ * t⁻¹ = v₂⁻¹ * (v₂ * (t * v₂ * t⁻¹)) := by group
      rw [e]
      exact (P₁ ⊔ Q₁).mul_mem ((P₁ ⊔ Q₁).inv_mem (mem_sup_right hv₂)) (c.P_le_PQ₁ h)
    exact hc₂P (c.Q₂_inf_PQ₁ ⟨h1, hc₂Q⟩)
  have h2 : ¬ ((v₂ * t) * (v₂ * t) ∈ P₁ ⊔ P₂) := by rw [haa]; exact hnotP
  obtain ⟨Y, hYS, hPY, haY, hYidx, hYel⟩ :=
    B.exists_Y c.P_le_S c.PnS (c.relIdx8 h4) haS (fun s hs => c.four_mem h4 hs) h2
  have htri : ∀ y ∈ Y, y ∈ P₁ ⊔ P₂ ∨ y ∉ S₁ ∨
      ∃ p ∈ P₁ ⊔ P₂, y = p * (v₂ * (t * v₂ * t⁻¹)) := by
    intro y hy
    obtain ⟨p, hp, k, hk, rfl⟩ := hYel y hy
    have hpS₁ : p ∈ S₁ := c.P_le_S₁ hp
    have haaS₁ : (v₂ * t) * (v₂ * t) ∈ S₁ := by rw [haa]; exact S₁.mul_mem hv₂S₁ hc₂S₁
    interval_cases k
    · left; simpa using hp
    · right; left
      intro h
      apply haS₁
      have := S₁.mul_mem (S₁.inv_mem hpS₁) h
      simpa using this
    · right; right
      exact ⟨p, hp, by rw [pow_two, haa]⟩
    · right; left
      intro h
      apply haS₁
      have h1 := S₁.mul_mem (S₁.inv_mem hpS₁) h
      have h2 : (v₂ * t) ^ 3 = (v₂ * t) * (v₂ * t) * (v₂ * t) := by rw [pow_succ, pow_two]
      have h3 : p⁻¹ * (p * (v₂ * t) ^ 3) = (v₂ * t) * (v₂ * t) * (v₂ * t) := by rw [← h2]; group
      rw [h3] at h1
      have h5 := S₁.mul_mem (S₁.inv_mem haaS₁) h1
      have e5 : ((v₂ * t) * (v₂ * t))⁻¹ * ((v₂ * t) * (v₂ * t) * (v₂ * t)) = v₂ * t := by group
      rw [e5] at h5
      exact h5
  refine ⟨Y, hYS, hYidx, hPY, ?_, ?_⟩
  · intro hvY
    rcases htri v₂ hvY with h | h | ⟨p, hp, hpe⟩
    · exact hv₂P (c.P_inf_Q₁ ⟨h, hv₂⟩)
    · exact h hv₂S₁
    · apply hc₂P
      have h1 : t * v₂ * t⁻¹ = v₂⁻¹ * p⁻¹ * v₂ := by
        have : v₂ = p * (v₂ * (t * v₂ * t⁻¹)) := hpe
        calc t * v₂ * t⁻¹ = v₂⁻¹ * p⁻¹ * (p * (v₂ * (t * v₂ * t⁻¹))) := by group
          _ = v₂⁻¹ * p⁻¹ * v₂ := by rw [← this]
      have h2 := c.PnS v₂⁻¹ (S.inv_mem hv₂S) p⁻¹ ((P₁ ⊔ P₂).inv_mem hp)
      rw [inv_inv] at h2
      have hmem : t * v₂ * t⁻¹ ∈ P₁ ⊔ P₂ := by rw [h1]; exact h2
      exact c.P_inf_Q₂ ⟨hmem, hc₂Q⟩
  · intro y hy
    rcases htri y hy with h | h | ⟨p, hp, hpe⟩
    · exact ⟨fun _ => c.P_le_PQ₂ h, fun _ => c.P_le_PQ₁ h⟩
    · exact ⟨fun h' => absurd (c.PQ₁_le h') h, fun h' => absurd (c.PQ₂_le h') h⟩
    · refine ⟨fun h' => ?_, fun h' => ?_⟩
      · exfalso
        have h1 : t * v₂ * t⁻¹ ∈ P₁ ⊔ Q₁ := by
          have e : t * v₂ * t⁻¹ = (p * v₂)⁻¹ * y := by rw [hpe]; group
          rw [e]
          exact (P₁ ⊔ Q₁).mul_mem ((P₁ ⊔ Q₁).inv_mem ((P₁ ⊔ Q₁).mul_mem (c.P_le_PQ₁ hp)
            (mem_sup_right hv₂))) h'
        exact hc₂P (c.Q₂_inf_PQ₁ ⟨h1, hc₂Q⟩)
      · exfalso
        have h1 : v₂ ∈ P₂ ⊔ Q₂ := by
          have e : v₂ = p⁻¹ * y * (t * v₂ * t⁻¹)⁻¹ := by rw [hpe]; group
          rw [e]
          exact (P₂ ⊔ Q₂).mul_mem ((P₂ ⊔ Q₂).mul_mem ((P₂ ⊔ Q₂).inv_mem (c.P_le_PQ₂ hp)) h')
            ((P₂ ⊔ Q₂).inv_mem (mem_sup_right hc₂Q))
        exact hv₂P (c.Q₁_inf_PQ₂ ⟨h1, hv₂⟩)

end Ctx73

end CFSG.GH74.GLS.Stage1.Thm3.Sec7.C73
