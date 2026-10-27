module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CentDPull

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {t : OGroup Q}

private theorem sl2f3_centralizer_q8 (A : SL2F3)
    (h : ∀ a : SL2F3, a ^ 4 = 1 → A * a = a * A) : A = 1 ∨ A = sl2f3NegOne := by
  revert A
  decide +kernel

theorem sec5qc_cent_q8Img (D : Om6Par Q t) {c : OGroup Q} (hc : c ∈ D.L ⊔ D.R)
    (h : ∀ q ∈ D.q8Img, c * q = q * c) : c = 1 ∨ c = t := by
  rw [← D.map_omega] at hc
  obtain ⟨ω, hω, rfl⟩ := Subgroup.mem_map.mp hc
  rw [← range_detPhi] at hω
  obtain ⟨⟨A, B⟩, rfl⟩ := hω
  have hA_cent : ∀ a : SL2F3, a ^ 4 = 1 → A * a = a * A := by
    intro a ha
    have hqa := h (D.theta (leftMulHom a)) (D.theta_left_mem_q8Img ha)
    have h2 : detPhi (A, B) * leftMulHom a = leftMulHom a * detPhi (A, B) :=
      D.theta_injective (by simpa only [map_mul] using hqa)
    rw [detPhi_apply] at h2
    have h3 : leftMulHom A * leftMulHom a = leftMulHom a * leftMulHom A := by
      have h4 : leftMulHom A * leftMulHom a * rightMulHom B =
          leftMulHom a * leftMulHom A * rightMulHom B := by
        calc leftMulHom A * leftMulHom a * rightMulHom B
            = leftMulHom A * (leftMulHom a * rightMulHom B) := by rw [mul_assoc]
          _ = leftMulHom A * (rightMulHom B * leftMulHom a) := by
                rw [leftMulHom_mul_rightMulHom_comm a B]
          _ = leftMulHom A * rightMulHom B * leftMulHom a := by rw [← mul_assoc]
          _ = leftMulHom a * (leftMulHom A * rightMulHom B) := h2
          _ = leftMulHom a * leftMulHom A * rightMulHom B := by rw [← mul_assoc]
      exact mul_right_cancel h4
    exact leftMulHom_injective (by simpa only [map_mul] using h3)
  have hB_cent : ∀ b : SL2F3, b ^ 4 = 1 → B * b = b * B := by
    intro b hb
    have hqb := h (D.theta (rightMulHom b)) (D.theta_right_mem_q8Img hb)
    have h2 : detPhi (A, B) * rightMulHom b = rightMulHom b * detPhi (A, B) :=
      D.theta_injective (by simpa only [map_mul] using hqb)
    rw [detPhi_apply] at h2
    have h3 : rightMulHom B * rightMulHom b = rightMulHom b * rightMulHom B := by
      have h4 : leftMulHom A * (rightMulHom B * rightMulHom b) =
          leftMulHom A * (rightMulHom b * rightMulHom B) := by
        calc leftMulHom A * (rightMulHom B * rightMulHom b)
            = leftMulHom A * rightMulHom B * rightMulHom b := by rw [mul_assoc]
          _ = rightMulHom b * (leftMulHom A * rightMulHom B) := h2
          _ = rightMulHom b * leftMulHom A * rightMulHom B := by rw [← mul_assoc]
          _ = leftMulHom A * rightMulHom b * rightMulHom B := by
                rw [leftMulHom_mul_rightMulHom_comm A b]
          _ = leftMulHom A * (rightMulHom b * rightMulHom B) := by rw [mul_assoc]
      exact mul_left_cancel h4
    exact rightMulHom_injective (by simpa only [map_mul] using h3)
  rcases sl2f3_centralizer_q8 A hA_cent with hA | hA <;>
    rcases sl2f3_centralizer_q8 B hB_cent with hB | hB
  · left; rw [hA, hB]; simp [detPhi_apply]
  · right; rw [hA, hB]; simp [detPhi_apply, rightMulHom_sl2f3NegOne, D.theta_piOrth]
  · right; rw [hA, hB]
    simp [detPhi_apply, leftMulHom_eq_piOrth coe_sl2f3NegOne, D.theta_piOrth]
  · left; rw [hA, hB]
    simp [detPhi_apply, leftMulHom_eq_piOrth coe_sl2f3NegOne, rightMulHom_sl2f3NegOne,
      D.theta_piOrth, D.htt]

end CFSG.OddStandard.SmallF3.Omega
