module

public import CFSG.LocalAnalysis.EvenBN.Common.SL2TorusTwo
public import CFSG.LocalAnalysis.EvenBN.Common.SL2TorusThree

public section

namespace CFSG.LocalAnalysis.EvenBN.Common

open Matrix Subgroup CFSG.SL2MinimalFaithful
open scoped MatrixGroups

variable {k : Type*} [Field k] [CharP k 2]

theorem exists_torusSL_conj_eq [Finite k] {W : Subgroup SL(2, k)}
    (hW : W = upperSL k ∨ W = lowerSL k) {a b : SL(2, k)} (ha : a ∈ W) (hb : b ∈ W)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) : ∃ t ∈ torusSL k, t * a * t⁻¹ = b := by
  rcases hW with rfl | rfl
  · obtain ⟨α, rfl⟩ := mem_upperSL_iff.1 ha
    obtain ⟨β, rfl⟩ := mem_upperSL_iff.1 hb
    have hα : α ≠ 0 := fun h => ha1 (by rw [h, unipotent_zero])
    have hβ : β ≠ 0 := fun h => hb1 (by rw [h, unipotent_zero])
    obtain ⟨ρ, hρ⟩ := exists_units_sq_eq (Units.mk0 (β / α) (div_ne_zero hβ hα))
    refine ⟨diagSL ρ, diagSL_mem_torusSL ρ, ?_⟩
    rw [diagSL_conj_unipotent]
    congr 1
    rw [← Units.val_pow_eq_pow_val, hρ, Units.val_mk0]
    exact div_mul_cancel₀ β hα
  · obtain ⟨α, rfl⟩ := mem_lowerSL_iff.1 ha
    obtain ⟨β, rfl⟩ := mem_lowerSL_iff.1 hb
    have hα : α ≠ 0 := fun h => ha1 (by rw [h, lowerUnipotent_zero])
    have hβ : β ≠ 0 := fun h => hb1 (by rw [h, lowerUnipotent_zero])
    obtain ⟨ρ, hρ⟩ := exists_units_sq_eq (Units.mk0 (α / β) (div_ne_zero hα hβ))
    refine ⟨diagSL ρ, diagSL_mem_torusSL ρ, ?_⟩
    rw [diagSL_conj_lowerUnipotent]
    congr 1
    rw [inv_pow, ← Units.val_pow_eq_pow_val, hρ, Units.val_mk0, inv_div]
    exact div_mul_cancel₀ β hα

theorem exists_conj_eq_of_mem_of_card [Finite k] {X : Type*} [Group X] (ψ : X ≃* SL(2, k))
    {d : X} (hd1 : d ≠ 1) (hd : d ^ (Nat.card k - 1) = 1) {S : Subgroup X}
    (hS : Nat.card S = Nat.card k) (hdS : d ∈ normalizer (S : Set X)) {a b : X} (ha : a ∈ S)
    (hb : b ∈ S) (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    ∃ c ∈ centralizer (zpowers d : Set X), c * a * c⁻¹ = b := by
  obtain ⟨ψ₁, μ, hμ, hψ₁d, hC⟩ := exists_mulEquiv_map_centralizer_zpowers ψ hd1 hd
  have hS' : Nat.card (S.map ψ₁.toMonoidHom) = Nat.card k := by
    rw [card_map_of_injective ψ₁.injective, hS]
  have hdS' : diagSL μ ∈ normalizer ((S.map ψ₁.toMonoidHom : Subgroup SL(2, k)) :
      Set SL(2, k)) := by
    rw [← map_equiv_normalizer_eq, ← hψ₁d]
    exact ⟨d, hdS, rfl⟩
  obtain ⟨t, ht, hta⟩ := exists_torusSL_conj_eq (eq_upperSL_or_eq_lowerSL hS' hμ hdS')
    ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ (by simpa using ha1) (by simpa using hb1)
  rw [← hC] at ht
  obtain ⟨c, hc, rfl⟩ := ht
  refine ⟨c, hc, ψ₁.injective ?_⟩
  simpa [map_mul, map_inv] using hta

theorem exists_conj_eq_of_mem_of_card' [Finite k] {G : Type*} [Group G] {X S : Subgroup G}
    (ψ : X ≃* SL(2, k)) {d : G} (hdX : d ∈ X) (hd1 : d ≠ 1) (hd : d ^ (Nat.card k - 1) = 1)
    (hSX : S ≤ X) (hS : Nat.card S = Nat.card k) (hdS : d ∈ normalizer (S : Set G)) {a b : G}
    (ha : a ∈ S) (hb : b ∈ S) (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    ∃ c ∈ X, c * d = d * c ∧ c * a * c⁻¹ = b := by
  set d' : X := ⟨d, hdX⟩ with hd'
  have hd'1 : d' ≠ 1 := fun h => hd1 (congrArg Subtype.val h)
  have hd'q : d' ^ (Nat.card k - 1) = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hd)
  have hS' : Nat.card (S.subgroupOf X) = Nat.card k := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hSX).toEquiv, hS]
  have hdS' : d' ∈ normalizer ((S.subgroupOf X : Subgroup X) : Set X) := by
    rw [mem_normalizer_iff]
    intro w
    exact mem_normalizer_iff.1 hdS w
  obtain ⟨c, hc, hca⟩ := exists_conj_eq_of_mem_of_card ψ hd'1 hd'q hS' hdS'
    (a := ⟨a, hSX ha⟩) (b := ⟨b, hSX hb⟩) ha hb (fun h => ha1 (congrArg Subtype.val h))
    (fun h => hb1 (congrArg Subtype.val h))
  refine ⟨c, c.2, ?_, congrArg Subtype.val hca⟩
  rw [centralizer_zpowers, mem_centralizer_singleton_iff] at hc
  exact congrArg Subtype.val hc

end CFSG.LocalAnalysis.EvenBN.Common
