module

public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralCoreTwo
public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralCoreTwoB

public noncomputable section

namespace CFSG.ComponentClassification.HSDihedral

open CFSG Subgroup CFSG.ABGLocalTools DihedralGroup
open CFSG.ComponentClassification.HSFLit (ElemAbelianTwo)

variable {X : Type} [Group X] {A : Type} [Group A]

namespace LocalDatum

variable {Δ : LocalDatum X A}

structure TwoBSplit (φ : Δ.Fusion) where
  d₀ : X
  d₀_mem : d₀ ∈ Δ.D
  sq : φ.x ^ 2 = d₀ * (φ.x * d₀ * φ.x⁻¹)
  h8 : 8 ≤ Nat.card Δ.D
  hD1 : ∀ u ∈ Δ.D, φ.x⁻¹ * u * φ.x ∈ Δ.D → u = 1
  conj_dz : φ.x * Δ.dz * φ.x⁻¹ = Δ.t
  conj_t : φ.x * Δ.t * φ.x⁻¹ = Δ.dz
  decomp : ∀ s ∈ Δ.S, ∃ a ∈ Δ.D, ∃ b ∈ Δ.D, s = a * (φ.x * b * φ.x⁻¹)

namespace TwoBSplit

variable {φ : Δ.Fusion} (B : TwoBSplit φ)

@[expose] def e : X := φ.x * B.d₀⁻¹

theorem d₀S : B.d₀ ∈ Δ.S := Δ.D_le B.d₀_mem

theorem e_mem : B.e ∈ (φ.T : Subgroup X) := mul_mem φ.mem (inv_mem (φ.le B.d₀S))

theorem e_not_mem : B.e ∉ Δ.S := fun h => φ.not_mem (by
  have := mul_mem h B.d₀S
  rwa [e, inv_mul_cancel_right] at this)

theorem conj_e_D (d : X) : B.e * d * B.e⁻¹ = φ.x * (B.d₀⁻¹ * d * B.d₀) * φ.x⁻¹ := by
  rw [e]; group

theorem conj_e_S {s : X} (hs : s ∈ Δ.S) : B.e * s * B.e⁻¹ ∈ Δ.S := by
  rw [B.conj_e_D]
  exact φ.conj_mem _ (mul_mem (mul_mem (inv_mem B.d₀S) hs) B.d₀S)

theorem conj_e_t : B.e * Δ.t * B.e⁻¹ = Δ.dz := by
  have h : B.d₀⁻¹ * Δ.t * B.d₀ = Δ.t := by
    rw [mul_assoc, ← Δ.commute_t B.d₀S]; group
  rw [B.conj_e_D, h, B.conj_t]

variable [Finite X]

include B in
theorem comm₁ {d d' : X} (hd : d ∈ Δ.D) (hd' : d' ∈ Δ.D) :
    d * (φ.x * d' * φ.x⁻¹) = (φ.x * d' * φ.x⁻¹) * d := TwoB_commute φ B.hD1 hd hd'

theorem e_sq : B.e ^ 2 = 1 := by
  have h := B.comm₁ B.d₀_mem B.d₀_mem
  calc B.e ^ 2 = (φ.x * B.d₀⁻¹ * φ.x⁻¹) * φ.x ^ 2 * B.d₀⁻¹ := by rw [e, pow_two, pow_two]; group
    _ = (φ.x * B.d₀ * φ.x⁻¹)⁻¹ * (B.d₀ * (φ.x * B.d₀ * φ.x⁻¹)) * B.d₀⁻¹ := by
        rw [B.sq]; group
    _ = 1 := by rw [h]; group

theorem e_inv : B.e⁻¹ = B.e := inv_eq_of_mul_eq_one_right (by rw [← pow_two, B.e_sq])

theorem conj_e_D1 {d : X} (hd : d ∈ Δ.D) :
    B.e * (φ.x * d * φ.x⁻¹) * B.e⁻¹ = φ.x ^ 2 * d * (φ.x ^ 2)⁻¹ := by
  have h := B.comm₁ (inv_mem B.d₀_mem) hd
  calc B.e * (φ.x * d * φ.x⁻¹) * B.e⁻¹ =
      φ.x * (B.d₀⁻¹ * (φ.x * d * φ.x⁻¹)) * B.d₀ * φ.x⁻¹ := by rw [e]; group
    _ = φ.x * ((φ.x * d * φ.x⁻¹) * B.d₀⁻¹) * B.d₀ * φ.x⁻¹ := by rw [h]
    _ = φ.x ^ 2 * d * (φ.x ^ 2)⁻¹ := by rw [pow_two]; group

theorem conj_e_dz : B.e * Δ.dz * B.e⁻¹ = Δ.t := by
  have h : B.d₀⁻¹ * Δ.dz * B.d₀ = Δ.dz := by
    rw [mul_assoc, ← Δ.dz_comm_S B.h8 B.d₀S]; group
  rw [B.conj_e_D, h, B.conj_dz]

end TwoBSplit

end LocalDatum

end CFSG.ComponentClassification.HSDihedral
