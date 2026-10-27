module

public import CFSG.LargeExtraspecial.GLW4Lat
public import CFSG.LargeExtraspecial.GLRLinGL
public import CFSG.LargeExtraspecial.GLRSplitBasic
public import CFSG.LargeExtraspecial.S12FifteenB
public import CFSG.LargeExtraspecial.S3bConj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

attribute [-instance] CFSG.BenderSuzuki.PFAppendixIII.instFactNatPrimeTwo

namespace CFSG.LargeExtraspecial.GLW4

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial.S14 CFSG.LargeExtraspecial.GLR

variable {K : Type*} [Group K] [Finite K]

namespace LatData

variable {T : Setting K} {R : Subgroup K} {W₁ W₂ : Submodule (ZMod 2) T.Qt}
  (L : LatData T R W₁ W₂)
include L

theorem exists_R_of_preserve
    (hsurj : ∀ f : W₁ ≃ₗ[ZMod 2] W₁, ∃ r : T.M, (r : K) ∈ R ∧
      ∀ w : W₁, ((f w : W₁) : T.Qt) = ((T.ρ r : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) w)
    {k : T.M} (hk₁ : W₁.map ((T.ρ k : T.O) : T.Qt →ₗ[ZMod 2] T.Qt) = W₁)
    (hk₂ : W₂.map ((T.ρ k : T.O) : T.Qt →ₗ[ZMod 2] T.Qt) = W₂) :
    ∃ r : T.M, (r : K) ∈ R ∧ T.ρ (r⁻¹ * k) = 1 := by
  obtain ⟨r, hr, hrk⟩ := hsurj (LinearEquiv.ofSubmodules _ W₁ W₁ hk₁)
  refine ⟨r, hr, L.eq_one_of_fix (fun w hw => ?_) (fun w hw => ?_)⟩
  · have e := hrk ⟨w, hw⟩
    change ((T.ρ k : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) w = _ at e
    rw [map_mul, map_inv, Subgroup.coe_mul, LinearEquiv.mul_apply, e]
    exact Config.inv_apply_apply _ _
  · have hk : ((T.ρ k : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) w ∈ W₂ := hk₂ ▸ ⟨w, hw, rfl⟩
    rw [map_mul, Subgroup.coe_mul, LinearEquiv.mul_apply]
    exact L.inv₂ r⁻¹ (R.inv_mem hr) _ hk

theorem not_isReducible_of_swap {k : T.M}
    (hk : W₁.map ((T.ρ k : T.O) : T.Qt →ₗ[ZMod 2] T.Qt) = W₂) : ¬ T.IsReducible := by
  rintro ⟨W, h0, htop, hW⟩
  have hk₂ : W₂.map ((T.ρ k : T.O) : T.Qt →ₗ[ZMod 2] T.Qt) = W₁ := by
    rcases L.map_eq k with ⟨h1, -⟩ | ⟨-, h2⟩
    · exfalso
      have := L.inf
      rw [← hk, h1, inf_idem] at this
      have h4 := L.finrank₁
      rw [this, finrank_bot] at h4
      omega
    · exact h2
  have hle : ∀ {U U' : Submodule (ZMod 2) T.Qt}, W = U →
      U.map ((T.ρ k : T.O) : T.Qt →ₗ[ZMod 2] T.Qt) = U' → U' ≤ U := by
    rintro U U' rfl hU _ hv
    rw [← hU] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    exact hW k u hu
  have hbot : ∀ {U U' : Submodule (ZMod 2) T.Qt}, U' ≤ U → U ⊓ U' = ⊥ →
      finrank (ZMod 2) U' = 4 → False := fun hle' hinf h4 => by
    rw [inf_of_le_right hle'] at hinf
    rw [hinf, finrank_bot] at h4
    omega
  rcases L.all W fun r _ v hv => hW r v hv with h | h | h | h
  · exact h0 h
  · exact hbot (hle h hk) L.inf L.finrank₂
  · exact hbot (hle h hk₂) (by rw [inf_comm]; exact L.inf) L.finrank₁
  · exact htop h

theorem pair_Xbar12 (hw : T.width = 4) (g₀ : K)
    (hX : Nonempty (T.Xbar12 g₀ ≃* Matrix.SpecialLinearGroup (Fin T.width) (ZMod 2))) :
    Pair T (T.Xbar12 g₀) W₁ W₂ := by
  obtain ⟨e⟩ := hX
  exact ⟨L.ts₁, L.ts₂, L.inf, L.sup, by rw [L.finrank₁, hw], by rw [L.finrank₂, hw],
    fun x hx v hv => (L.Xbar12_stab g₀ hx).1 v hv, fun x hx v hv => (L.Xbar12_stab g₀ hx).2 v hv,
    by rw [Nat.card_congr e.toEquiv, card_SL_eq_card_GL]⟩

theorem map_eq_of_not_mem {g₀ : K} (hidx : (T.Xbar12 g₀).relIndex T.Mbar = 2) {k : T.M}
    (hk : W₁.map ((T.ρ k : T.O) : T.Qt →ₗ[ZMod 2] T.Qt) = W₂) {σ : T.O} (hσ : σ ∈ T.Mbar)
    (hσX : σ ∉ T.Xbar12 g₀) :
    W₁.map ((σ : T.Qt ≃ₗ[ZMod 2] T.Qt) : T.Qt →ₗ[ZMod 2] T.Qt) = W₂ := by
  obtain ⟨m, rfl⟩ := MonoidHom.mem_range.mp hσ
  rcases L.map_eq m with ⟨h1, -⟩ | ⟨h1, -⟩
  swap
  · exact h1
  exfalso
  have hne : W₁ ≠ W₂ := fun h => by
    have := L.inf
    rw [h, inf_idem] at this
    have h4 := L.finrank₂
    rw [this, finrank_bot] at h4
    omega
  have hkW : ∀ w ∈ W₁, ((T.ρ k : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) w ∈ W₁ := by
    by_cases hkX : T.ρ k ∈ T.Xbar12 g₀
    · exact (L.Xbar12_stab g₀ hkX).1
    · have hmem := s12_mul_mem_of_relIndex_two hidx (⟨k, rfl⟩ : T.ρ k ∈ T.Mbar)
        (T.Mbar.inv_mem (⟨m, rfl⟩ : T.ρ m ∈ T.Mbar)) hkX
        (fun h => hσX (by simpa using (T.Xbar12 g₀).inv_mem h))
      intro w hw
      have hw' : ((T.ρ m : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) w ∈ W₁ := h1 ▸ ⟨w, hw, rfl⟩
      have := (L.Xbar12_stab g₀ hmem).1 _ hw'
      rwa [Subgroup.coe_mul, LinearEquiv.mul_apply, Config.inv_apply_apply] at this
  exact hne ((map_eq_of_mapsTo hkW).symm.trans hk)

end LatData

end CFSG.LargeExtraspecial.GLW4
