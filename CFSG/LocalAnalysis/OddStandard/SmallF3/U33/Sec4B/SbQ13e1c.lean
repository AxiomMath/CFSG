module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13e1b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13e0c

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

private theorem ncard_subset_union_smul_le (H : Subgroup G) (g : G) {X : Set G}
    (hX : X ⊆ (H : Set G) ∪ g • (H : Set G)) : X.ncard ≤ 2 * Nat.card H := by
  have hH : (H : Set G).ncard = Nat.card H := (Nat.card_coe_set_eq (H : Set G)).symm
  calc X.ncard ≤ ((H : Set G) ∪ g • (H : Set G)).ncard := Set.ncard_le_ncard hX
    _ ≤ (H : Set G).ncard + (g • (H : Set G)).ncard := Set.ncard_union_le _ _
    _ = Nat.card H + Nat.card H := by rw [Set.ncard_smul_set, hH]
    _ = 2 * Nat.card H := by ring

theorem q13e_ncard_fix_B (h : Q13Om t L S x₁ x₂ lam rho tau om) (hC : Q13C t x₁ x₂ lam tau om)
    (hD : Q13D t x₁ x₂ lam rho tau om) :
    ({b | b ∈ q13B t tau x₁ x₂ rho om ∧
      (t * lam) * b * (t * lam)⁻¹ * b⁻¹ ∈ q13P t tau x₁ x₂ rho om} : Set G).ncard ≤ 2 ^ 8 := by
  let X : Set G := {b | b ∈ q13B t tau x₁ x₂ rho om ∧
    (t * lam) * b * (t * lam)⁻¹ * b⁻¹ ∈ q13P t tau x₁ x₂ rho om}
  change X.ncard ≤ 2 ^ 8
  have key : ∀ b, b ∈ X →
      (∃ p ∈ q13P t tau x₁ x₂ rho om,
        (t * lam) * b * (t * lam)⁻¹ = b * p ∧
          (t * om)⁻¹ * p ∈ q13H1 t tau x₁ x₂ lam rho) ∨
        b ∈ q13E0 t tau x₁ x₂ rho om := by
    intro b hbX
    obtain ⟨hbB, hbP⟩ := hbX
    have hbL : b ∈ q13L t tau x₁ x₂ rho om := (Subgroup.mem_inf.mp hbB).1
    obtain ⟨p, hpP, hrep⟩ := q13e_fix_rep h hD hbL hbP
    have hcoc := q13e_cocycle h hrep
    rcases q13e_Z1_P h hC hD p hpP hcoc with hp | hp
    · exact Or.inr (q13e_class_one h hC hD hbB hp hrep)
    · exact Or.inl ⟨p, hpP, hrep, hp⟩
  by_cases hne : ∃ b₁, b₁ ∈ X ∧ ∃ p₁ ∈ q13P t tau x₁ x₂ rho om,
      (t * lam) * b₁ * (t * lam)⁻¹ = b₁ * p₁ ∧
        (t * om)⁻¹ * p₁ ∈ q13H1 t tau x₁ x₂ lam rho
  · obtain ⟨b₁, hb₁X, p₁, hp₁P, hrep₁, hc₁⟩ := hne
    have hsub : X ⊆ (q13E0 t tau x₁ x₂ rho om : Set G) ∪
        b₁ • (q13E0 t tau x₁ x₂ rho om : Set G) := by
      intro b hbX
      rcases key b hbX with ⟨p, hpP, hrep, hc⟩ | hbE0
      · obtain ⟨hb₁B, _⟩ := hb₁X
        obtain ⟨hbB, _⟩ := hbX
        have hmem : b₁⁻¹ * b ∈ q13E0 t tau x₁ x₂ rho om :=
          q13e_class_gam h hC hD hb₁B hbB hp₁P hpP hrep₁ hrep hc₁ hc
        refine Or.inr (Set.mem_smul_set.mpr ⟨b₁⁻¹ * b, hmem, ?_⟩)
        change b₁ * (b₁⁻¹ * b) = b
        group
      · exact Or.inl hbE0
    have hbound := ncard_subset_union_smul_le (q13E0 t tau x₁ x₂ rho om) b₁ hsub
    calc X.ncard ≤ 2 * Nat.card ↥(q13E0 t tau x₁ x₂ rho om) := hbound
      _ = 2 ^ 8 := by rw [q13d_card_E0 h]; norm_num
  · have hsub : X ⊆ (q13E0 t tau x₁ x₂ rho om : Set G) := by
      intro b hbX
      rcases key b hbX with ⟨p, hpP, hrep, hc⟩ | hbE0
      · exact absurd ⟨b, hbX, p, hpP, hrep, hc⟩ hne
      · exact hbE0
    calc X.ncard ≤ (q13E0 t tau x₁ x₂ rho om : Set G).ncard := Set.ncard_le_ncard hsub
      _ = Nat.card ↥(q13E0 t tau x₁ x₂ rho om) :=
            (Nat.card_coe_set_eq (q13E0 t tau x₁ x₂ rho om : Set G)).symm
      _ = 2 ^ 7 := q13d_card_E0 h
      _ ≤ 2 ^ 8 := by norm_num

theorem q13e_ncard_fix_CLP (h : Q13Om t L S x₁ x₂ lam rho tau om) (hC : Q13C t x₁ x₂ lam tau om)
    (hD : Q13D t x₁ x₂ lam rho tau om) :
    ({k | k ∈ q13CLP t tau x₁ x₂ rho om ∧
      (t * lam) * k * (t * lam)⁻¹ * k⁻¹ ∈ q13P t tau x₁ x₂ rho om} : Set G).ncard ≤ 2 ^ 7 := by
  let X : Set G := {k | k ∈ q13CLP t tau x₁ x₂ rho om ∧
    (t * lam) * k * (t * lam)⁻¹ * k⁻¹ ∈ q13P t tau x₁ x₂ rho om}
  change X.ncard ≤ 2 ^ 7
  have key : ∀ k, k ∈ X →
      (∃ p ∈ q13P t tau x₁ x₂ rho om,
        (t * lam) * k * (t * lam)⁻¹ = k * p ∧
          (t * om)⁻¹ * p ∈ q13H1 t tau x₁ x₂ lam rho) ∨
        k ∈ q13P t tau x₁ x₂ rho om := by
    intro k hkX
    obtain ⟨hkK, hkP⟩ := hkX
    have hkL : k ∈ q13L t tau x₁ x₂ rho om := (Subgroup.mem_inf.mp hkK).1
    have hkB : k ∈ q13B t tau x₁ x₂ rho om := q13e_CLP_le_B h hkK
    obtain ⟨p, hpP, hrep⟩ := q13e_fix_rep h hD hkL hkP
    have hcoc := q13e_cocycle h hrep
    rcases q13e_Z1_P h hC hD p hpP hcoc with hp | hp
    · exact Or.inr (q13e_CLP_inf_E0 h hD k hkK (q13e_class_one h hC hD hkB hp hrep))
    · exact Or.inl ⟨p, hpP, hrep, hp⟩
  by_cases hne : ∃ k₁, k₁ ∈ X ∧ ∃ p₁ ∈ q13P t tau x₁ x₂ rho om,
      (t * lam) * k₁ * (t * lam)⁻¹ = k₁ * p₁ ∧
        (t * om)⁻¹ * p₁ ∈ q13H1 t tau x₁ x₂ lam rho
  · obtain ⟨k₁, hk₁X, p₁, hp₁P, hrep₁, hc₁⟩ := hne
    have hsub : X ⊆ (q13P t tau x₁ x₂ rho om : Set G) ∪
        k₁ • (q13P t tau x₁ x₂ rho om : Set G) := by
      intro k hkX
      rcases key k hkX with ⟨p, hpP, hrep, hc⟩ | hkP
      · obtain ⟨hk₁K, _⟩ := hk₁X
        obtain ⟨hkK, _⟩ := hkX
        have hmemE0 : k₁⁻¹ * k ∈ q13E0 t tau x₁ x₂ rho om :=
          q13e_class_gam h hC hD (q13e_CLP_le_B h hk₁K) (q13e_CLP_le_B h hkK)
            hp₁P hpP hrep₁ hrep hc₁ hc
        have hmemK : k₁⁻¹ * k ∈ q13CLP t tau x₁ x₂ rho om :=
          (q13CLP t tau x₁ x₂ rho om).mul_mem
            ((q13CLP t tau x₁ x₂ rho om).inv_mem hk₁K) hkK
        have hmemP : k₁⁻¹ * k ∈ q13P t tau x₁ x₂ rho om :=
          q13e_CLP_inf_E0 h hD _ hmemK hmemE0
        refine Or.inr (Set.mem_smul_set.mpr ⟨k₁⁻¹ * k, hmemP, ?_⟩)
        change k₁ * (k₁⁻¹ * k) = k
        group
      · exact Or.inl hkP
    have hbound := ncard_subset_union_smul_le (q13P t tau x₁ x₂ rho om) k₁ hsub
    calc X.ncard ≤ 2 * Nat.card ↥(q13P t tau x₁ x₂ rho om) := hbound
      _ = 2 ^ 7 := by rw [q13d_card_P h hD.A_cent]; norm_num
  · have hsub : X ⊆ (q13P t tau x₁ x₂ rho om : Set G) := by
      intro k hkX
      rcases key k hkX with ⟨p, hpP, hrep, hc⟩ | hkP
      · exact absurd ⟨k, hkX, p, hpP, hrep, hc⟩ hne
      · exact hkP
    calc X.ncard ≤ (q13P t tau x₁ x₂ rho om : Set G).ncard := Set.ncard_le_ncard hsub
      _ = Nat.card ↥(q13P t tau x₁ x₂ rho om) :=
            (Nat.card_coe_set_eq (q13P t tau x₁ x₂ rho om : Set G)).symm
      _ = 2 ^ 6 := q13d_card_P h hD.A_cent
      _ ≤ 2 ^ 7 := by norm_num

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
