module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnPol

public section

open scoped Pointwise

namespace CFSG.GH74.BNPair

namespace RankTwoSystem

variable {X : Type*} [Group X] {D : RankTwoSystem X 3}

theorem w₂_mul_w₁_mul_w₂ : D.w₂ * D.w₁ * D.w₂ = D.w₀ := by
  have hbr : D.w₁ * D.w₂ * D.w₁ = D.w₂ * D.w₁ * D.w₂ := by
    simpa only [altWord, one_mul] using D.rank2.dih.altWord_eq
  have h0 : D.w₀ = D.w₁ * D.w₂ * D.w₁ := by
    simp only [w₀, altWord, one_mul]
  rw [h0, hbr]

section Aux

private theorem intList_one_three_lay2 : intList 1 ((3 : ℕ) : ℤ) = [1, 2, 3] := by decide

private theorem tau_sq_mem_root {τ : X ≃* X} (hτ : D.IsOpposition τ) {k : ℤ} (hk : IsRoot 3 k)
    {x : X} (hx : x ∈ D.root k) : τ (τ x) ∈ D.root k := by
  have h1 := hτ.mem_root k hk x hx
  have h2 := hτ.mem_root (-k) ⟨neg_ne_zero.2 hk.1, by simpa only [Int.natAbs_neg] using hk.2⟩
    (τ x) h1
  rwa [neg_neg] at h2

private theorem tau_sq_mem_U {τ : X ≃* X} (hτ : D.IsOpposition τ) {u : X} (hu : u ∈ D.U) :
    τ (τ u) ∈ D.U := by
  have hU : (D.U : Set X) = chainProd D.root [1, 2, 3] := by
    rw [D.roots.carrier_eq, intList_one_three_lay2]
  have hu' : u ∈ chainProd D.root [1, 2, 3] := by
    rw [← hU]
    exact hu
  rw [chainProd_cons, chainProd_cons, chainProd_singleton] at hu'
  obtain ⟨x₁, hx₁, y, hy, rfl⟩ := Set.mem_mul.1 hu'
  obtain ⟨x₂, hx₂, x₃, hx₃, rfl⟩ := Set.mem_mul.1 hy
  rw [← SetLike.mem_coe, hU, chainProd_cons, chainProd_cons, chainProd_singleton,
    map_mul, map_mul, map_mul, map_mul]
  exact Set.mem_mul.2 ⟨_, tau_sq_mem_root hτ ⟨by norm_num, by norm_num⟩ hx₁, _,
    Set.mem_mul.2 ⟨_, tau_sq_mem_root hτ ⟨by norm_num, by norm_num⟩ hx₂, _,
      tau_sq_mem_root hτ ⟨by norm_num, by norm_num⟩ hx₃, rfl⟩, rfl⟩

end Aux

theorem IsOpposition.tau_sq_mem_B {τ : X ≃* X} (hτ : D.IsOpposition τ) {b : X}
    (hb : b ∈ D.B) : τ (τ b) ∈ D.B := by
  have hb' : b ∈ ((D.B ⊓ D.N : Subgroup X) : Set X) * (D.U : Set X) := D.isSplit.2 ▸ hb
  obtain ⟨h, hh, u, hu, rfl⟩ := Set.mem_mul.1 hb'
  rw [map_mul, map_mul]
  exact D.B.mul_mem (hτ.mem_torus _ (hτ.mem_torus h hh)).1 (D.U_le_B (tau_sq_mem_U hτ hu))

theorem IsOpposition.lift₂_all {τ : X ≃* X} (hτ : D.IsOpposition τ) {m : D.N}
    (hm : (m : D.Weyl) = D.w₂) : (m : X)⁻¹ * τ (m : X) ∈ D.B ⊓ D.N := by
  obtain ⟨m₀, hm₀, h₀⟩ := hτ.lift₂
  have hB : (m₀ : X)⁻¹ * (m : X) ∈ D.B := mk_eq_mk_iff.1 (hm₀.trans hm.symm)
  have hN : (m₀ : X)⁻¹ * (m : X) ∈ D.N := D.N.mul_mem (D.N.inv_mem m₀.2) m.2
  have hc : (m₀ : X)⁻¹ * (m : X) ∈ D.B ⊓ D.N := ⟨hB, hN⟩
  have key : (m : X)⁻¹ * τ (m : X) =
      ((m₀ : X)⁻¹ * (m : X))⁻¹ * ((m₀ : X)⁻¹ * τ (m₀ : X)) * τ ((m₀ : X)⁻¹ * (m : X)) := by
    simp only [map_mul, map_inv]
    group
  rw [key]
  exact (D.B ⊓ D.N).mul_mem ((D.B ⊓ D.N).mul_mem ((D.B ⊓ D.N).inv_mem hc) h₀)
    (hτ.mem_torus _ hc)

theorem conj_mem_root₂_neg (m : D.N) (hm : (m : D.Weyl) = D.w₂) {y : X}
    (hy : y ∈ D.root (-1)) : (m : X) * y * (m : X)⁻¹ ∈ D.root (-2) := by
  have h := actsPos_lift₂ (D := D) m hm 3 y (by rw [show Rt 3 3 = -1 by decide]; exact hy)
  rwa [show Rt 3 (((3 : ℕ) : ℤ) - 2 - 3) = -2 by decide] at h

end RankTwoSystem

end CFSG.GH74.BNPair
