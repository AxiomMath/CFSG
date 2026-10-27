module

public import CFSG.ClassicalInvolution.Asc77.AscS16A
public import CFSG.ClassicalInvolution.Asc77.AscT7HC4

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace S16

set_option linter.unusedSectionVars false

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

section NotTrivial

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem commutator_left {R R' R₃ : Subgroup G} {j₁ j₂ : G}
    (d : InvData z u₁ u₂ j₁ j₂ R R' R₃) : ⁅u₁ * u₂, j₁⁆ = z := by
  have h1 : j₁ * u₂ = u₂ * j₁ := d.comm_j₁u₂
  have h2 : j₁ * u₁ * j₁⁻¹ = u₁⁻¹ := d.inv₁
  have h3 : j₁ * u₁⁻¹ * j₁⁻¹ = u₁ := by
    have := congrArg (fun t => t⁻¹) h2
    simp only [mul_inv_rev, inv_inv] at this
    calc j₁ * u₁⁻¹ * j₁⁻¹ = (j₁ * u₁ * j₁⁻¹)⁻¹ := by group
      _ = u₁ := by rw [h2, inv_inv]
  calc ⁅u₁ * u₂, j₁⁆ = u₁ * (u₂ * j₁ * u₂⁻¹) * u₁⁻¹ * j₁⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = u₁ * (j₁ * u₂ * u₂⁻¹) * u₁⁻¹ * j₁⁻¹ := by rw [← h1]
    _ = u₁ * (j₁ * u₁⁻¹ * j₁⁻¹) := by group
    _ = u₁ * u₁ := by rw [h3]
    _ = z := d.s₁

theorem commutator_right {R R' R₃ : Subgroup G} {j₁ j₂ : G}
    (d : InvData z u₁ u₂ j₁ j₂ R R' R₃) : ⁅u₁ * u₂, j₂⁆ = z := by
  have h1 : j₂ * u₁ = u₁ * j₂ := d.comm_j₂u₁
  have h2 : j₂ * u₂ * j₂⁻¹ = u₂⁻¹ := d.inv₂
  have h3 : j₂ * u₂⁻¹ * j₂⁻¹ = u₂ := by
    calc j₂ * u₂⁻¹ * j₂⁻¹ = (j₂ * u₂ * j₂⁻¹)⁻¹ := by group
      _ = u₂ := by rw [h2, inv_inv]
  have hc : u₁ * u₂ = u₂ * u₁ := d.comm_u₁u₂
  calc ⁅u₁ * u₂, j₂⁆ = ⁅u₂ * u₁, j₂⁆ := by rw [hc]
    _ = u₂ * (u₁ * j₂ * u₁⁻¹) * u₂⁻¹ * j₂⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = u₂ * (j₂ * u₁ * u₁⁻¹) * u₂⁻¹ * j₂⁻¹ := by rw [← h1]
    _ = u₂ * (j₂ * u₂⁻¹ * j₂⁻¹) := by group
    _ = u₂ * u₂ := by rw [h3]
    _ = z := d.s₂

theorem not_mem_of_sq {z : G} (hz1 : z ≠ 1) (hz : z * z = 1) {N : Subgroup G}
    (hN : Odd (Nat.card N)) : z ∉ N := fun hzN =>
  hz1 (T7H.eq_one_of_mem_odd_of_sq hN hzN hz)

theorem not_mem_trivialOnQuot_left {R R' R₃ : Subgroup G} {j₁ j₂ : G}
    (d : InvData z u₁ u₂ j₁ j₂ R R' R₃) (hz : IsUniqueInvolution K z) (hj₁ : j₁ ∈ K) :
    u₁ * u₂ ∉ trivialOnQuot K := by
  intro hmem
  have h1 : ⁅u₁ * u₂, j₁⁆ ∈ oddCoreIn K := hmem.2 j₁ hj₁
  rw [commutator_left d] at h1
  exact not_mem_of_sq hz.ne_one hz.sq (odd_card_oddCoreIn K) h1

theorem not_mem_trivialOnQuot_right {R R' R₃ : Subgroup G} {j₁ j₂ : G}
    (d : InvData z u₁ u₂ j₁ j₂ R R' R₃) (hz : IsUniqueInvolution K' z) (hj₂ : j₂ ∈ K') :
    u₁ * u₂ ∉ trivialOnQuot K' := by
  intro hmem
  have h1 : ⁅u₁ * u₂, j₂⁆ ∈ oddCoreIn K' := hmem.2 j₂ hj₂
  rw [commutator_right d] at h1
  exact not_mem_of_sq hz.ne_one hz.sq (odd_card_oddCoreIn K') h1

end NotTrivial

end S16

end CFSG.ClassicalInvolution.Asc77
