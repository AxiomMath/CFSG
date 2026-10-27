module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YSylow

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem y54_V_cycle {V : Subgroup G} (hV2 : ∀ v ∈ V, v ^ 2 = 1) (hV4 : Nat.card ↥V = 4) {κ : G}
    (hκV : ∀ v ∈ V, κ * v * κ⁻¹ ∈ V) (hκ3 : κ ^ 3 = 1)
    (hfpf : ∀ v ∈ V, κ * v * κ⁻¹ = v → v = 1) :
    ∀ v ∈ V, v * (κ * v * κ⁻¹) = κ * (κ * v * κ⁻¹) * κ⁻¹ := by
  have hcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := by
    intro a ha b hb
    have ha2 : a * a = 1 := by simpa [pow_two] using hV2 a ha
    have hb2 : b * b = 1 := by simpa [pow_two] using hV2 b hb
    have hab2 : (a * b) * (a * b) = 1 := by
      simpa [pow_two] using hV2 (a * b) (V.mul_mem ha hb)
    have habinv : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_left hab2
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_left ha2, inv_eq_of_mul_eq_one_left hb2] at habinv
    exact habinv.symm
  intro v hv
  generalize hv1 : κ * v * κ⁻¹ = v1
  generalize hv2 : κ * v1 * κ⁻¹ = v2
  have hv1V : v1 ∈ V := by rw [← hv1]; exact hκV v hv
  have hv2V : v2 ∈ V := by rw [← hv2]; exact hκV v1 hv1V
  have hvv : v * v = 1 := by simpa [pow_two] using hV2 v hv
  have hv1v1 : v1 * v1 = 1 := by simpa [pow_two] using hV2 v1 hv1V
  have hkk : κ * κ * κ = 1 := by
    have h : κ ^ 2 * κ = 1 := by simpa [pow_succ] using hκ3
    simpa [pow_two] using h
  have hφv2 : κ * v2 * κ⁻¹ = v := by
    rw [← hv2, ← hv1]
    have h : κ * (κ * (κ * v * κ⁻¹) * κ⁻¹) * κ⁻¹
        = (κ * κ * κ) * v * (κ * κ * κ)⁻¹ := by group
    rw [h, hkk]
    simp
  have hu : v2 * v1 * v ∈ V := V.mul_mem (V.mul_mem hv2V hv1V) hv
  have hfix : κ * (v2 * v1 * v) * κ⁻¹ = v2 * v1 * v := by
    have h1 : κ * (v2 * v1 * v) * κ⁻¹
        = (κ * v2 * κ⁻¹) * (κ * v1 * κ⁻¹) * (κ * v * κ⁻¹) := by group
    rw [h1, hφv2, hv2, hv1]
    calc v * v2 * v1 = v2 * v * v1 := by rw [hcomm v hv v2 hv2V]
      _ = v2 * (v * v1) := by rw [mul_assoc]
      _ = v2 * (v1 * v) := by rw [hcomm v hv v1 hv1V]
      _ = v2 * v1 * v := by rw [mul_assoc]
  have hone : v2 * v1 * v = 1 := hfpf (v2 * v1 * v) hu hfix
  have h3 : v2 = (v1 * v)⁻¹ := eq_inv_of_mul_eq_one_left (by simpa only [mul_assoc] using hone)
  have : v2 = v * v1 := by
    rw [h3, mul_inv_rev, inv_eq_of_mul_eq_one_left hvv, inv_eq_of_mul_eq_one_left hv1v1]
  exact this.symm

end CFSG.OddStandard.HigherRank.YamadaG23
