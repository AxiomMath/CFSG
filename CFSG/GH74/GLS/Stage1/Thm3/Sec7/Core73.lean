module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.GrpA
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Quat2

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec7.C73

open Subgroup CFSG.GH74.GLS.Stage1.Thm3.Sec7

variable {G : Type*} [Group G]

theorem relIndex_pos [Finite G] (H K : Subgroup G) : 0 < H.relIndex K := by
  have h := Subgroup.relIndex_mul_card H K
  have hK : 0 < Nat.card ↥K := Nat.card_pos
  rcases Nat.eq_zero_or_pos (H.relIndex K) with h0 | h0
  · rw [h0] at h; omega
  · exact h0

structure Ctx73 (z t : G) (S P₁ P₂ Q₁ Q₂ S₁ : Subgroup G) : Prop where
  S2 : IsPGroup 2 ↥S
  z_sq : z * z = 1
  z_ne : z ≠ 1
  zP₁ : z ∈ P₁
  zP₂ : z ∈ P₂
  P₁S : P₁ ≤ S
  P₂S : P₂ ≤ S
  S₁S : S₁ ≤ S
  P₁Q₂ : P₁ ≤ Q₂
  P₂Q₁ : P₂ ≤ Q₁
  Q₁S₁ : Q₁ ≤ S₁
  Q₂S₁ : Q₂ ≤ S₁
  P₁P₂ : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a
  Q₁P₁ : ∀ a ∈ Q₁, ∀ b ∈ P₁, a * b = b * a
  Q₂P₂ : ∀ a ∈ Q₂, ∀ b ∈ P₂, a * b = b * a
  P₁₂ : P₁ ⊓ P₂ ≤ zpowers z
  P₁Q₁ : P₁ ⊓ Q₁ ≤ zpowers z
  P₂Q₂ : P₂ ⊓ Q₂ ≤ zpowers z
  Q₁Q₂ : Q₁ ⊓ Q₂ = zpowers z
  S₁Q₁ : ∀ s ∈ S₁, ∀ q ∈ Q₁, s * q * s⁻¹ ∈ Q₁
  S₁Q₂ : ∀ s ∈ S₁, ∀ q ∈ Q₂, s * q * s⁻¹ ∈ Q₂
  PnS : ∀ s ∈ S, ∀ p ∈ P₁ ⊔ P₂, s * p * s⁻¹ ∈ P₁ ⊔ P₂
  t_mem : t ∈ S
  t_sq : t * t = 1
  t_nS₁ : t ∉ S₁
  S₁idx : S₁.relIndex S = 2
  tP₁ : ∀ x ∈ P₁, t * x * t⁻¹ ∈ P₂
  tP₂ : ∀ x ∈ P₂, t * x * t⁻¹ ∈ P₁
  tQ₁ : ∀ x ∈ Q₁, t * x * t⁻¹ ∈ Q₂
  tQ₂ : ∀ x ∈ Q₂, t * x * t⁻¹ ∈ Q₁
  Q₁idx : P₂.relIndex Q₁ ≤ 2
  Q₂idx : P₁.relIndex Q₂ ≤ 2
  S₁Pidx : (P₁ ⊔ P₂).relIndex S₁ ≤ 4
  d₁ : (P₁ ⊔ P₂).relIndex S₁ = 4 → S₁ = Q₁ ⊔ Q₂
  d₂ : (P₁ ⊔ P₂).relIndex S₁ = 4 → ∀ x ∈ S₁, x * x ∈ P₁ ⊔ P₂
  P₁card : 8 ≤ Nat.card ↥P₁
  P₂card : 8 ≤ Nat.card ↥P₂
  P₁q : ∃ N : ℕ, ∃ _ : NeZero N, Nonempty (↥P₁ ≃* QuaternionGroup N)
  P₂q : ∃ N : ℕ, ∃ _ : NeZero N, Nonempty (↥P₂ ≃* QuaternionGroup N)
  Q₁q : ∃ N : ℕ, ∃ _ : NeZero N, Nonempty (↥Q₁ ≃* QuaternionGroup N)
  Q₂q : ∃ N : ℕ, ∃ _ : NeZero N, Nonempty (↥Q₂ ≃* QuaternionGroup N)
  C₁ : ∀ x ∈ S₁, (∀ p ∈ P₁, x * p = p * x) → x ∈ Q₁
  C₂ : ∀ x ∈ S₁, (∀ p ∈ P₂, x * p = p * x) → x ∈ Q₂
  nf : ∀ u ∈ P₁ ⊔ P₂, IsConj z u → u = z
  tr : ∀ (Y : Subgroup G) (v : G), Y ≤ S → Y.relIndex S = 2 → v ∈ S → v ∉ Y → v * v = 1 →
    ∃ g : G, g⁻¹ * v * g ∈ Y ∧ ∀ x ∈ S, x * v = v * x → g⁻¹ * x * g ∈ S
  mix : ∀ x ∈ P₁ ⊔ Q₁, x ∉ P₂ ⊔ Q₂ → ∀ g : G, g⁻¹ * z * g = z → g⁻¹ * x * g ∈ S →
    ((g⁻¹ * x * g ∈ P₁ ⊔ Q₁ ∧ g⁻¹ * x * g ∉ P₂ ⊔ Q₂) ∨
      (g⁻¹ * x * g ∈ P₂ ⊔ Q₂ ∧ g⁻¹ * x * g ∉ P₁ ⊔ Q₁))
  h225 : ∀ (T R₁ R₂ X₁ X₂ U : Subgroup G), IsPGroup 2 ↥T → T = R₁ ⊔ R₂ ⊔ U → T = X₂ ⊔ X₁ →
    (∀ x ∈ T, ∀ y ∈ X₁, x * y * x⁻¹ ∈ X₁) → (∀ x ∈ T, ∀ y ∈ X₂, x * y * x⁻¹ ∈ X₂) →
    Nonempty (↥X₁ ≃* QuaternionGroup 4) → Nonempty (↥X₂ ≃* QuaternionGroup 4) →
    X₁ ⊓ X₂ = zpowers z → (center ↥X₁).map X₁.subtype = zpowers z →
    (center ↥X₂).map X₂.subtype = zpowers z →
    Nonempty (↥R₁ ≃* QuaternionGroup 2) → Nonempty (↥R₂ ≃* QuaternionGroup 2) →
    R₂ ≤ X₁ → R₁ ≤ X₂ → X₁ = T ⊓ centralizer (R₁ : Set G) → X₂ = T ⊓ centralizer (R₂ : Set G) →
    (∀ x ∈ U, x * x = 1) → Nat.card ↥U = 4 → (R₁ ⊔ R₂) ⊓ U = ⊥ →
    ∀ a ∈ X₁, ∀ b ∈ X₂, a * b = b * a

namespace Ctx73

variable {z t : G} {S P₁ P₂ Q₁ Q₂ S₁ : Subgroup G} (c : Ctx73 z t S P₁ P₂ Q₁ Q₂ S₁)

include c

theorem tt_conj (x : G) : t * (t * x * t⁻¹) * t⁻¹ = x := by
  have h1 : t⁻¹ * t⁻¹ = 1 := by rw [← mul_inv_rev, c.t_sq, inv_one]
  calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t⁻¹ * t⁻¹) := by group
    _ = x := by rw [c.t_sq, h1]; group

theorem mem_P₁_of_conj {x : G} (hx : t * x * t⁻¹ ∈ P₂) : x ∈ P₁ := by
  have := c.tP₂ _ hx
  rwa [c.tt_conj] at this

theorem mem_P₂_of_conj {x : G} (hx : t * x * t⁻¹ ∈ P₁) : x ∈ P₂ := by
  have := c.tP₁ _ hx
  rwa [c.tt_conj] at this

theorem Q₂_eq_of_Q₁ (h : Q₁ = P₂) : Q₂ = P₁ := by
  refine le_antisymm (fun x hx => c.mem_P₁_of_conj ?_) c.P₁Q₂
  have := c.tQ₂ x hx
  rwa [h] at this

theorem Q₁_eq_of_Q₂ (h : Q₂ = P₁) : Q₁ = P₂ := by
  refine le_antisymm (fun x hx => c.mem_P₂_of_conj ?_) c.P₂Q₁
  have := c.tQ₁ x hx
  rwa [h] at this

theorem P_le_S₁ : P₁ ⊔ P₂ ≤ S₁ := sup_le (c.P₁Q₂.trans c.Q₂S₁) (c.P₂Q₁.trans c.Q₁S₁)

theorem P_le_S : P₁ ⊔ P₂ ≤ S := c.P_le_S₁.trans c.S₁S

theorem PQ₁_le : P₁ ⊔ Q₁ ≤ S₁ := sup_le (c.P₁Q₂.trans c.Q₂S₁) c.Q₁S₁

theorem PQ₂_le : P₂ ⊔ Q₂ ≤ S₁ := sup_le (c.P₂Q₁.trans c.Q₁S₁) c.Q₂S₁

theorem P_le_PQ₁ : P₁ ⊔ P₂ ≤ P₁ ⊔ Q₁ := sup_le le_sup_left (c.P₂Q₁.trans le_sup_right)

theorem P_le_PQ₂ : P₁ ⊔ P₂ ≤ P₂ ⊔ Q₂ := sup_le (c.P₁Q₂.trans le_sup_right) le_sup_left

theorem P₁Q₁_le : P₁ ⊓ Q₁ ≤ P₂ := c.P₁Q₁.trans (zpowers_le.2 c.zP₂)

theorem P₂Q₂_le : P₂ ⊓ Q₂ ≤ P₁ := c.P₂Q₂.trans (zpowers_le.2 c.zP₁)

theorem Q₁Q₂_le_P₁ : Q₁ ⊓ Q₂ ≤ P₁ := c.Q₁Q₂.le.trans (zpowers_le.2 c.zP₁)

theorem Q₁Q₂_le_P₂ : Q₁ ⊓ Q₂ ≤ P₂ := c.Q₁Q₂.le.trans (zpowers_le.2 c.zP₂)

theorem P_inf_Q₁ : (P₁ ⊔ P₂) ⊓ Q₁ ≤ P₂ := by
  have := A.dedekind_le (A := P₂) (B := P₁) (C := Q₁) (fun a ha b hb => (c.P₁P₂ b hb a ha).symm)
    c.P₂Q₁ c.P₁Q₁_le
  rwa [sup_comm] at this

theorem P_inf_Q₂ : (P₁ ⊔ P₂) ⊓ Q₂ ≤ P₁ :=
  A.dedekind_le (A := P₁) (B := P₂) (C := Q₂) c.P₁P₂ c.P₁Q₂ c.P₂Q₂_le

theorem Q₂_inf_PQ₁ : (P₁ ⊔ Q₁) ⊓ Q₂ ≤ P₁ :=
  A.dedekind_le (A := P₁) (B := Q₁) (C := Q₂) (fun a ha b hb => (c.Q₁P₁ b hb a ha).symm) c.P₁Q₂
    c.Q₁Q₂_le_P₁

theorem Q₁_inf_PQ₂ : (P₂ ⊔ Q₂) ⊓ Q₁ ≤ P₂ :=
  A.dedekind_le (A := P₂) (B := Q₂) (C := Q₁) (fun a ha b hb => (c.Q₂P₂ b hb a ha).symm) c.P₂Q₁
    (by rw [inf_comm]; exact c.Q₁Q₂_le_P₂)

theorem S₁_pgroup : IsPGroup 2 ↥S₁ := c.S2.to_le c.S₁S

theorem card_zpowers_z : Nat.card ↥(zpowers z) = 2 := by
  have h2 : orderOf z = 2 := orderOf_eq_prime (by simpa [pow_two] using c.z_sq) c.z_ne
  rw [Nat.card_zpowers, h2]

theorem P₁₂_eq : P₁ ⊓ P₂ = zpowers z :=
  le_antisymm c.P₁₂ (le_inf (zpowers_le.2 c.zP₁) (zpowers_le.2 c.zP₂))

theorem card_P [Finite G] : Nat.card ↥(P₁ ⊔ P₂) * 2 = Nat.card ↥P₁ * Nat.card ↥P₂ := by
  have h := A.card_sup_mul_card_inf_of_commute c.P₁P₂
  rwa [c.P₁₂_eq, c.card_zpowers_z] at h

theorem Q₂_normalizes_Q₁ : Q₂ ≤ normalizer (Q₁ : Set G) := by
  intro x hx
  have hxS : x ∈ S₁ := c.Q₂S₁ hx
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh; exact c.S₁Q₁ x hxS h hh
  · intro hh
    have := c.S₁Q₁ x⁻¹ (S₁.inv_mem hxS) _ hh
    simpa [mul_assoc] using this

theorem card_Q [Finite G] : Nat.card ↥(Q₁ ⊔ Q₂) * 2 = Nat.card ↥Q₁ * Nat.card ↥Q₂ := by
  have h := A.card_sup_mul_card_inf c.Q₂_normalizes_Q₁
  rwa [c.Q₁Q₂, c.card_zpowers_z] at h

theorem not_concl73 [Finite G] (hn : ¬ ((P₁ ⊔ P₂).relIndex S₁ ≤ 2 ∧ Q₁ = P₂ ∧ Q₂ = P₁)) :
    (P₁ ⊔ P₂).relIndex S₁ = 4 ∧ Q₁ ≠ P₂ ∧ Q₂ ≠ P₁ ∧ P₂.relIndex Q₁ = 2 ∧ P₁.relIndex Q₂ = 2 := by
  have hQ₁ : Q₁ ≠ P₂ := by
    intro h
    apply hn
    refine ⟨?_, h, c.Q₂_eq_of_Q₁ h⟩
    rcases A.relIndex_cases c.S₁_pgroup c.P_le_S₁ c.S₁Pidx with h1 | h2 | h4
    · omega
    · omega
    · exfalso
      have hS := c.d₁ h4
      rw [h, c.Q₂_eq_of_Q₁ h, sup_comm] at hS
      have : (P₁ ⊔ P₂).relIndex S₁ = 1 := Subgroup.relIndex_eq_one.2 hS.le
      omega
  have hQ₂ : Q₂ ≠ P₁ := fun h => hQ₁ (c.Q₁_eq_of_Q₂ h)
  have idx₁ : P₂.relIndex Q₁ = 2 := by
    have h1 : P₂.relIndex Q₁ ≠ 1 := fun h =>
      hQ₁ (le_antisymm (Subgroup.relIndex_eq_one.1 h) c.P₂Q₁)
    have h0 := relIndex_pos P₂ Q₁
    have := c.Q₁idx
    omega
  have idx₂ : P₁.relIndex Q₂ = 2 := by
    have h1 : P₁.relIndex Q₂ ≠ 1 := fun h =>
      hQ₂ (le_antisymm (Subgroup.relIndex_eq_one.1 h) c.P₁Q₂)
    have h0 := relIndex_pos P₁ Q₂
    have := c.Q₂idx
    omega
  refine ⟨?_, hQ₁, hQ₂, idx₁, idx₂⟩
  have cQ₁ := A.card_eq_two_mul_of_relIndex_two c.P₂Q₁ idx₁
  have cQ₂ := A.card_eq_two_mul_of_relIndex_two c.P₁Q₂ idx₂
  have hP := c.card_P
  have hQ := c.card_Q
  have hle : Nat.card ↥(Q₁ ⊔ Q₂) ≤ Nat.card ↥S₁ := Subgroup.card_le_of_le (sup_le c.Q₁S₁ c.Q₂S₁)
  have hS := Subgroup.relIndex_mul_card (P₁ ⊔ P₂) S₁
  rw [inf_eq_left.2 c.P_le_S₁] at hS
  have hpos : 0 < Nat.card ↥(P₁ ⊔ P₂) := Nat.card_pos
  have h4 : 4 ≤ (P₁ ⊔ P₂).relIndex S₁ := by
    by_contra hcon
    have hlt : (P₁ ⊔ P₂).relIndex S₁ ≤ 3 := by omega
    have : Nat.card ↥S₁ ≤ 3 * Nat.card ↥(P₁ ⊔ P₂) := by
      rw [← hS]; exact Nat.mul_le_mul_right _ hlt
    have e1 : Nat.card ↥(Q₁ ⊔ Q₂) * 2 = 4 * (Nat.card ↥P₁ * Nat.card ↥P₂) := by
      rw [hQ, cQ₁, cQ₂]; ring
    have e2 : Nat.card ↥P₁ * Nat.card ↥P₂ = Nat.card ↥(P₁ ⊔ P₂) * 2 := hP.symm
    rw [e2] at e1
    have : Nat.card ↥(Q₁ ⊔ Q₂) = 4 * Nat.card ↥(P₁ ⊔ P₂) := by omega
    omega
  have := c.S₁Pidx
  omega

theorem exists_v₂ (hne : Q₁ ≠ P₂) : ∃ v₂ ∈ Q₁, v₂ ∉ P₂ ∧ v₂ * v₂ = z := by
  obtain ⟨N, hNZ, ⟨e⟩⟩ := c.Q₁q
  obtain ⟨a, b, haQ, hbQ, hQG, hgen⟩ := Q.quat_gens e
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.2 hNZ.out
  have hzQ : z ∈ Q₁ := c.P₂Q₁ c.zP₂
  have hzaN : z = a ^ N := hQG.eq_aN_of_involution hN1 hgen hzQ c.z_sq c.z_ne
  by_contra hcon
  push Not at hcon
  have hb : ∀ j : ℕ, a ^ j * b ∈ P₂ := by
    intro j
    by_contra hj
    exact hcon _ (Q₁.mul_mem (Q₁.pow_mem haQ j) hbQ) hj (by rw [hQG.akb_sq, hzaN])
  apply hne
  apply le_antisymm _ c.P₂Q₁
  intro x hx
  obtain ⟨k, hk | hk⟩ := hgen x hx
  · rw [hk]
    have h1 := hb k
    have h2 := hb 0
    have : a ^ k = (a ^ k * b) * (a ^ 0 * b)⁻¹ := by group
    rw [this]
    exact P₂.mul_mem h1 (P₂.inv_mem h2)
  · rw [hk]; exact hb k

end Ctx73

end CFSG.GH74.GLS.Stage1.Thm3.Sec7.C73
