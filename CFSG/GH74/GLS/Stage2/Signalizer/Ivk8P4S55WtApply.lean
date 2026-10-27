module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55WtStar

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.WtP

open Subgroup CFSG.GroupTheory.TwoWeights

theorem data_of_coe {Y : Type*} [Group Y] {H : Subgroup Y} {a u₁ u₂ u₃ x y : H}
    (D : Data (a : Y) (u₁ : Y) (u₂ : Y) (u₃ : Y) (x : Y) (y : Y)) : Data a u₁ u₂ u₃ x y :=
  ⟨Subtype.ext (by simpa using D.a_a), Subtype.ext (by simpa using D.u₁_u₁),
    Subtype.ext (by simpa using D.u₂_u₂), Subtype.ext (by simpa using D.u₃_u₃),
    Subtype.ext (by simpa using D.u₁_u₂), Subtype.ext (by simpa using D.u₁_u₃),
    Subtype.ext (by simpa using D.u₁_a), Subtype.ext (by simpa using D.u₂_u₃),
    Subtype.ext (by simpa using D.u₂_a), Subtype.ext (by simpa using D.u₃_a),
    Subtype.ext (by simpa using D.a_x), Subtype.ext (by simpa using D.a_y),
    Subtype.ext (by simpa using D.x_u₁), Subtype.ext (by simpa using D.x_u₂),
    Subtype.ext (by simpa using D.x_u₃), Subtype.ext (by simpa using D.xi_u₁),
    Subtype.ext (by simpa using D.xi_u₂), Subtype.ext (by simpa using D.xi_u₃),
    Subtype.ext (by simpa using D.y_u₁), Subtype.ext (by simpa using D.y_u₂),
    Subtype.ext (by simpa using D.y_u₃), Subtype.ext (by simpa using D.yi_u₁),
    Subtype.ext (by simpa using D.yi_u₂), Subtype.ext (by simpa using D.yi_u₃),
    Subtype.ext (by simpa using D.xx), Subtype.ext (by simpa using D.yy),
    Subtype.ext (by simpa using D.xy4)⟩

theorem central_of_data {Y : Type*} [Group Y] [Finite Y] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {R X : Subgroup Y} {τ u₁ u₂ u₃ x y : Y} (D : Data τ u₁ u₂ u₃ x y)
    (hτ : τ ∈ R) (hu₁ : u₁ ∈ R) (hu₂ : u₂ ∈ R) (hu₃ : u₃ ∈ R) (hx : x ∈ R) (hy : y ∈ R)
    (hX : IsPGroup p ↥X) (hN : R ≤ normalizer (X : Set Y)) (hsmall : Nat.card ↥X < p ^ 8) :
    X ≤ centralizer ({τ} : Set Y) := by
  let ρ : ↥R →* MulAut ↥X := X.normalizerMonoidHom.comp (Subgroup.inclusion hN)
  have D' : Data (⟨τ, hτ⟩ : ↥R) ⟨u₁, hu₁⟩ ⟨u₂, hu₂⟩ ⟨u₃, hu₃⟩ ⟨x, hx⟩ ⟨y, hy⟩ := data_of_coe D
  have h1 := star_mod hp2 D' (Nat.card ↥X) ↥X hX rfl hsmall ρ
  intro k hk
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h2 : (ρ ⟨τ, hτ⟩) ⟨k, hk⟩ = ⟨k, hk⟩ := by rw [h1]; rfl
  have h3 := congrArg Subtype.val h2
  change τ * k * τ⁻¹ = k at h3
  calc k * τ = (τ * k * τ⁻¹) * τ := by rw [h3]
    _ = τ * k := by group

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.WtP
