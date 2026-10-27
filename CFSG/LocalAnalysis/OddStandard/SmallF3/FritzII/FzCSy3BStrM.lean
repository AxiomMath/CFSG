module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSy3BStrH

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33
open scoped commutatorElement

variable {G : Type} [Group G]

namespace FzCSy3bStr

variable {x₁ x₂ t a b c : G} {Wp F P M₂ M₃ U : Subgroup G}

private theorem fzc_sy3_m_aU (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) : a ∈ U :=
  hs.chain.2.2.1 (hs.chain.2.1 (a_mem hs))

private theorem fzc_sy3_m_bU (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) : b ∈ U :=
  hs.chain.2.2.1 (b_mem hs)

private theorem fzc_sy3_m_b2t (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) :
    b * b * t ∈ Wp := by
  apply hs.E_le_Wp
  rw [show b * b * t = b ^ 2 * t by rw [pow_two]]
  exact hs.b_sq

theorem bc_sq (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) :
    ∃ w ∈ Wp, (b * c) * (b * c) = w * a := by
  have hct : c * c = t := by rw [← pow_two, hs.c_sq]
  have hw₁ : c * b * c⁻¹ * (a * b)⁻¹ ∈ Wp := hs.c_b
  have hw₂ : b * a * b⁻¹ * a⁻¹ ∈ Wp := hs.b_a
  have hw₄ : b * b * t ∈ Wp := fzc_sy3_m_b2t hs
  refine ⟨(b * (c * b * c⁻¹ * (a * b)⁻¹) * b⁻¹) * (b * a * b⁻¹ * a⁻¹)
      * (a * (b * b * t) * a⁻¹), ?_, ?_⟩
  · exact mul_mem (mul_mem (hs.nrm b (fzc_sy3_m_bU hs) _ hw₁) hw₂)
      (hs.nrm a (fzc_sy3_m_aU hs) _ hw₄)
  · rw [← hct]
    group

theorem bc_a (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) :
    (b * c) * a * (b * c)⁻¹ * a⁻¹ ∈ Wp := by
  have hca : c * a * c⁻¹ * a⁻¹ ∈ Wp := hs.c_a
  have hba : b * a * b⁻¹ * a⁻¹ ∈ Wp := hs.b_a
  have heq : (b * c) * a * (b * c)⁻¹ * a⁻¹ =
      (b * (c * a * c⁻¹ * a⁻¹) * b⁻¹) * (b * a * b⁻¹ * a⁻¹) := by group
  rw [heq]
  exact mul_mem (hs.nrm b (fzc_sy3_m_bU hs) _ hca) hba

theorem M₂_mem (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) {g : G} :
    g ∈ M₂ ↔ ∃ f ∈ F, g = f ∨ g = f * c := by
  rw [hs.M₂_eq]
  exact CFSG.GH74.GLS.Stage1.Thm6.Sec13.mem_sup_zpowers_sq
    (hs.chain.1 (sq_mem hs).2.2.1) (c_norm_F hs)

theorem M₃_mem (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) {g : G} :
    g ∈ M₃ ↔ ∃ f ∈ F, g = f ∨ g = f * (b * c) := by
  rw [hs.M₃_eq]
  refine CFSG.GH74.GLS.Stage1.Thm6.Sec13.mem_sup_zpowers_sq ?_ ?_
  · obtain ⟨w, hw, hbc⟩ := bc_sq hs
    rw [hbc]
    exact mul_mem (hs.chain.1 hw) (a_mem hs)
  · intro q hq
    have h1 : c * q * c⁻¹ ∈ F := c_norm_F hs q hq
    have h2 : b * (c * q * c⁻¹) * b⁻¹ ∈ F := b_norm_F hs _ h1
    have heq : (b * c) * q * (b * c)⁻¹ = b * (c * q * c⁻¹) * b⁻¹ := by group
    rw [heq]
    exact h2

theorem U_mem (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) {g : G} :
    g ∈ U ↔ ∃ p ∈ P, g = p ∨ g = p * c := by
  rw [hs.U_eq]
  exact CFSG.GH74.GLS.Stage1.Thm6.Sec13.mem_sup_zpowers_sq
    (hs.chain.2.1 (hs.chain.1 (sq_mem hs).2.2.1)) (c_norm_P hs)

private theorem fzc_sy3_m_card_F [Finite G]
    (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) :
    Nat.card F = 2 * Nat.card Wp := by
  rw [hs.F_eq]
  exact CFSG.GH74.GLS.Stage1.Thm6.Sec13.card_sup_zpowers_sq (sq_mem hs).1
    (fun q hq => hs.nrm a (fzc_sy3_m_aU hs) q hq) hs.a_notin

private theorem fzc_sy3_m_card_P [Finite G]
    (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) :
    Nat.card P = 2 * Nat.card F := by
  rw [hs.P_eq]
  exact CFSG.GH74.GLS.Stage1.Thm6.Sec13.card_sup_zpowers_sq (hs.chain.1 (sq_mem hs).2.1)
    (b_norm_F hs) hs.b_notin

private theorem fzc_sy3_m_card_M₂ [Finite G]
    (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) :
    Nat.card M₂ = 2 * Nat.card F := by
  rw [hs.M₂_eq]
  exact CFSG.GH74.GLS.Stage1.Thm6.Sec13.card_sup_zpowers_sq (hs.chain.1 (sq_mem hs).2.2.1)
    (c_norm_F hs) (fun hcF => hs.c_notin (hs.chain.2.1 hcF))

theorem card_P_M₂ [Finite G] (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) :
    Nat.card P = 4 * Nat.card Wp ∧ Nat.card M₂ = 4 * Nat.card Wp := by
  have hF : Nat.card F = 2 * Nat.card Wp := fzc_sy3_m_card_F hs
  have hP : Nat.card P = 2 * Nat.card F := fzc_sy3_m_card_P hs
  have hM : Nat.card M₂ = 2 * Nat.card F := fzc_sy3_m_card_M₂ hs
  exact ⟨by omega, by omega⟩

theorem norm_F (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) :
    ∀ u ∈ U, ∀ f ∈ F, u * f * u⁻¹ ∈ F := by
  intro u hu f hf
  rw [U_mem hs] at hu
  obtain ⟨p, hp, hu1 | hu1⟩ := hu
  · rw [hu1]
    rw [P_mem hs] at hp
    obtain ⟨f₁, hf₁, hp1 | hp1⟩ := hp
    · rw [hp1]
      exact F.mul_mem (F.mul_mem hf₁ hf) (F.inv_mem hf₁)
    · rw [hp1]
      have h1 : b * f * b⁻¹ ∈ F := b_norm_F hs f hf
      have heq : (f₁ * b) * f * (f₁ * b)⁻¹ = f₁ * (b * f * b⁻¹) * f₁⁻¹ := by group
      rw [heq]
      exact F.mul_mem (F.mul_mem hf₁ h1) (F.inv_mem hf₁)
  · rw [hu1]
    rw [P_mem hs] at hp
    obtain ⟨f₁, hf₁, hp1 | hp1⟩ := hp
    · rw [hp1]
      have h1 : c * f * c⁻¹ ∈ F := c_norm_F hs f hf
      have heq : (f₁ * c) * f * (f₁ * c)⁻¹ = f₁ * (c * f * c⁻¹) * f₁⁻¹ := by group
      rw [heq]
      exact F.mul_mem (F.mul_mem hf₁ h1) (F.inv_mem hf₁)
    · rw [hp1]
      have h1 : c * f * c⁻¹ ∈ F := c_norm_F hs f hf
      have h2 : b * (c * f * c⁻¹) * b⁻¹ ∈ F := b_norm_F hs _ h1
      have heq : (f₁ * b * c) * f * (f₁ * b * c)⁻¹ =
          f₁ * (b * (c * f * c⁻¹) * b⁻¹) * f₁⁻¹ := by group
      rw [heq]
      exact F.mul_mem (F.mul_mem hf₁ h2) (F.inv_mem hf₁)

end FzCSy3bStr

end CFSG.OddStandard.SmallF3.FritzII
