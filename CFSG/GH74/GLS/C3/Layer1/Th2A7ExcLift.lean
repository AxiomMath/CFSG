module

public import Mathlib.GroupTheory.PGroup
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.Maschke
public import Mathlib.Data.Rat.Floor
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG

variable {G : Type} [Group G]

theorem exists_exact_inverted_lift_gen {K Y : Subgroup G}
    (hYK : Y ≤ K) (hYn : ∀ k ∈ K, ∀ y ∈ Y, k * y * k⁻¹ ∈ Y) (hYodd : Odd (Nat.card ↥Y))
    {ρ k₀ : G} (hρ : ρ ∈ K) (hk₀ : k₀ ∈ K) (hρ4 : ρ ^ 4 = 1)
    (h : (ρ * k₀ * ρ⁻¹) * k₀ ∈ Y) :
    ∃ f ∈ K, k₀⁻¹ * f ∈ Y ∧ ρ * f * ρ⁻¹ = f⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  classical
  let X : Set G := {f | f ∈ K ∧ k₀⁻¹ * f ∈ Y}
  let θ : G → G := fun f => ρ * f⁻¹ * ρ⁻¹
  have hθ4 : ∀ f, θ (θ (θ (θ f))) = f := by
    intro f
    show ρ * (ρ * (ρ * (ρ * f⁻¹ * ρ⁻¹)⁻¹ * ρ⁻¹)⁻¹ * ρ⁻¹)⁻¹ * ρ⁻¹ = f
    calc ρ * (ρ * (ρ * (ρ * f⁻¹ * ρ⁻¹)⁻¹ * ρ⁻¹)⁻¹ * ρ⁻¹)⁻¹ * ρ⁻¹
        = ρ ^ 4 * f * (ρ ^ 4)⁻¹ := by group
      _ = f := by rw [hρ4]; group
  have hθX : ∀ f ∈ X, θ f ∈ X := by
    rintro f ⟨hfK, hfY⟩
    refine ⟨K.mul_mem (K.mul_mem hρ (K.inv_mem hfK)) (K.inv_mem hρ), ?_⟩
    set y : G := k₀⁻¹ * f with hy
    have hf : f = k₀ * y := by rw [hy]; group
    have h1 : ρ * y⁻¹ * ρ⁻¹ ∈ Y := hYn ρ hρ _ (Y.inv_mem hfY)
    have h2 : k₀⁻¹ * (ρ * y⁻¹ * ρ⁻¹) * k₀ ∈ Y := by
      have := hYn k₀⁻¹ (K.inv_mem hk₀) _ h1
      simpa using this
    have h3 : ((ρ * k₀ * ρ⁻¹) * k₀)⁻¹ ∈ Y := Y.inv_mem h
    have e : k₀⁻¹ * (ρ * f⁻¹ * ρ⁻¹) =
        (k₀⁻¹ * (ρ * y⁻¹ * ρ⁻¹) * k₀) * ((ρ * k₀ * ρ⁻¹) * k₀)⁻¹ := by
      rw [hf]; group
    show k₀⁻¹ * (ρ * f⁻¹ * ρ⁻¹) ∈ Y
    rw [e]
    exact Y.mul_mem h2 h3
  have hXcard : Odd (Nat.card ↥X) := by
    have e : ↥X ≃ ↥Y :=
      { toFun := fun f => ⟨k₀⁻¹ * f, f.2.2⟩
        invFun := fun y => ⟨k₀ * y, K.mul_mem hk₀ (hYK y.2), by simp⟩
        left_inv := fun f => Subtype.ext (by simp)
        right_inv := fun y => Subtype.ext (by simp) }
    rw [Nat.card_congr e]
    exact hYodd
  let σ : Equiv.Perm ↥X :=
    { toFun := fun f => ⟨θ f, hθX f f.2⟩
      invFun := fun f => ⟨θ (θ (θ f)), hθX _ (hθX _ (hθX _ f.2))⟩
      left_inv := fun f => Subtype.ext (hθ4 f)
      right_inv := fun f => Subtype.ext (hθ4 f) }
  have hσ4 : σ ^ 4 = 1 := by
    ext f
    show θ (θ (θ (θ f))) = f
    exact hθ4 f
  have hσ2 : IsPGroup 2 ↥(Subgroup.zpowers σ) := by
    have h1 : orderOf σ ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one (by simpa using hσ4)
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  have hndvd : ¬ 2 ∣ Nat.card ↥X := by
    intro hd
    exact (Nat.not_even_iff_odd.2 hXcard) (even_iff_two_dvd.2 hd)
  obtain ⟨⟨f, hfX⟩, hfix⟩ := hσ2.nonempty_fixed_point_of_prime_not_dvd_card ↥X hndvd
  have hσf : σ ⟨f, hfX⟩ = ⟨f, hfX⟩ := by
    have := MulAction.mem_fixedPoints.1 hfix ⟨σ, Subgroup.mem_zpowers σ⟩
    exact this
  have hθf : θ f = f := congrArg Subtype.val hσf
  refine ⟨f, hfX.1, hfX.2, ?_⟩
  have : ρ * f⁻¹ * ρ⁻¹ = f := hθf
  calc ρ * f * ρ⁻¹ = (ρ * f⁻¹ * ρ⁻¹)⁻¹ := by group
    _ = f⁻¹ := by rw [this]

end CFSG.GH74.GLS.C3.Layer1.Bk
