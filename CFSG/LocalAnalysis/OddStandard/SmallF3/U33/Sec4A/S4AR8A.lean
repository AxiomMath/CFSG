module

public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic.Group

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

section Core

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem coprime_core (F : Subgroup Γ) [F.Normal] (c : Γ →* Γ)
    (hc3 : ∀ x, c (c (c x)) = x) (hcF : ∀ f ∈ F, c f ∈ F)
    (hab : ∀ x y : Γ, x * y * x⁻¹ * y⁻¹ ∈ F) (hsq : ∀ x : Γ, x * x ∈ F)
    (τ : Γ) (hτ : c τ = τ) (hτF : τ ∉ F)
    (hker : ∀ x : Γ, c x * x⁻¹ ∈ F → x ∈ F ⊔ zpowers τ) :
    ∃ R : Subgroup Γ, (∀ x, x ∈ R ↔ ∃ q : Γ, ∃ f ∈ F, x = q * (c q)⁻¹ * f) ∧
      R.index = 2 ∧ τ ∉ R := by
  classical
  let π : Γ →* Γ ⧸ F := QuotientGroup.mk' F
  have hπ : Function.Surjective π := QuotientGroup.mk_surjective
  have hπeq : ∀ x y : Γ, π x = π y ↔ x⁻¹ * y ∈ F := fun x y => QuotientGroup.eq
  have hπ1 : ∀ x : Γ, π x = 1 ↔ x ∈ F := fun x => QuotientGroup.eq_one_iff x
  have hcomm : ∀ a b : Γ ⧸ F, a * b = b * a := by
    intro a b
    obtain ⟨x, rfl⟩ := hπ a
    obtain ⟨y, rfl⟩ := hπ b
    rw [← map_mul, ← map_mul, hπeq]
    have h1 := hab y⁻¹ x⁻¹
    have e : (x * y)⁻¹ * (y * x) = y⁻¹ * x⁻¹ * y⁻¹⁻¹ * x⁻¹⁻¹ := by group
    rw [e]
    exact h1
  letI : CommGroup (Γ ⧸ F) := { (inferInstance : Group (Γ ⧸ F)) with mul_comm := hcomm }
  let σ : Γ ⧸ F →* Γ ⧸ F := QuotientGroup.lift F (π.comp c) (by
    intro f hf
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hπ1]
    exact hcF f hf)
  have hσ : ∀ x : Γ, σ (π x) = π (c x) := fun x => rfl
  have hσ3 : ∀ y : Γ ⧸ F, σ (σ (σ y)) = y := by
    intro y
    obtain ⟨q, rfl⟩ := hπ y
    rw [hσ, hσ, hσ, hc3]
  let δ : Γ ⧸ F →* Γ ⧸ F := MonoidHom.mk' (fun y => y * (σ y)⁻¹) (by
    intro a b
    simp only [map_mul, mul_inv]
    exact mul_mul_mul_comm a b (σ a)⁻¹ (σ b)⁻¹)
  have hδ : ∀ y : Γ ⧸ F, δ y = y * (σ y)⁻¹ := fun y => rfl
  have hδπ : ∀ q : Γ, δ (π q) = π (q * (c q)⁻¹) := by
    intro q
    rw [hδ, hσ, map_mul, map_inv]
  have hker_eq : δ.ker = zpowers (π τ) := by
    apply le_antisymm
    · intro y hy
      obtain ⟨q, rfl⟩ := hπ y
      rw [MonoidHom.mem_ker, hδπ, hπ1] at hy
      have hy' : c q * q⁻¹ ∈ F := by
        have := F.inv_mem hy
        rwa [mul_inv_rev, inv_inv] at this
      have hq := hker q hy'
      obtain ⟨f, hf, z, hz, hfz⟩ := Subgroup.mem_sup_of_normal_left.mp hq
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      rw [← hfz, map_mul, (hπ1 f).mpr hf, one_mul, map_zpow]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k
    · rw [Subgroup.zpowers_le, MonoidHom.mem_ker, hδπ, hτ, mul_inv_cancel, map_one]
  have hπτ1 : π τ ≠ 1 := fun h1 => hτF ((hπ1 τ).mp h1)
  have hπτ2 : π τ ^ 2 = 1 := by
    rw [pow_two, ← map_mul]
    exact (hπ1 _).mpr (hsq τ)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hkercard : Nat.card δ.ker = 2 := by
    rw [hker_eq, Nat.card_zpowers]
    exact orderOf_eq_prime hπτ2 hπτ1
  refine ⟨δ.range.comap π, ?_, ?_, ?_⟩
  · intro x
    rw [Subgroup.mem_comap, MonoidHom.mem_range]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨q, rfl⟩ := hπ y
      rw [hδπ] at hy
      refine ⟨q, (q * (c q)⁻¹)⁻¹ * x, ?_, by group⟩
      rw [← hπeq]
      exact hy
    · rintro ⟨q, f, hf, rfl⟩
      refine ⟨π q, ?_⟩
      rw [hδπ, map_mul π _ f, (hπ1 f).mpr hf, mul_one]
  · rw [Subgroup.index_comap_of_surjective δ.range hπ]
    have h2 : Nat.card δ.ker * Nat.card δ.range = Nat.card (Γ ⧸ F) := card_ker_mul_card_range δ
    have h3 : Nat.card δ.range * δ.range.index = Nat.card (Γ ⧸ F) := card_mul_index δ.range
    have hpos : 0 < Nat.card δ.range := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [h3, ← hkercard, mul_comm]
    exact h2.symm
  · intro hτR
    rw [Subgroup.mem_comap, MonoidHom.mem_range] at hτR
    obtain ⟨y, hy⟩ := hτR
    have hfix : σ (π τ) = π τ := by rw [hσ, hτ]
    have ha3 : π τ * π τ * π τ = 1 := by
      calc π τ * π τ * π τ = π τ * σ (π τ) * σ (σ (π τ)) := by rw [hfix, hfix]
        _ = δ y * σ (δ y) * σ (σ (δ y)) := by rw [hy]
        _ = 1 := by
          simp only [hδ, map_mul, map_inv, hσ3]
          group
    have ha2 : π τ * π τ = 1 := by
      rw [← pow_two]
      exact hπτ2
    apply hπτ1
    calc π τ = π τ * π τ * π τ * (π τ * π τ)⁻¹ := by group
      _ = 1 := by rw [ha3, ha2]; simp

end Core

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
