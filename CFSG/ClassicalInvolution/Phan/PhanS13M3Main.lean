module

public import CFSG.ClassicalInvolution.Phan.PhanS12Plane
import CFSG.ClassicalInvolution.Phan.PhanS13M1Gram
import CFSG.ClassicalInvolution.Phan.PhanS13M2Move

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open CFSG.LieType.Universal.Spin QuadraticMap CFSG.ClassicalInvolution.PhanB3.H
  CFSG.ClassicalInvolution.PhanB3

section Main

variable {p f : ℕ} [Fact p.Prime]
  {hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2} {h2 : (2 : GaloisField p f) ≠ 0}
  {C : B2Coord hK (GaloisField p f) h2} {M : ModelB3 p f h2}
  {E : PhanFamilyB3 C (spinGroup (quadOdd 3 (GaloisField p f)))}
  [Algebra (GaloisField p f) (GaloisField p (2 * f))]
  {D : KDat (GaloisField p f) (GaloisField p (2 * f))}

theorem planeMove (S : Setup M E D) : PlaneMove D := by
  intro a b c ha hb hc hab hbc hca hdet
  obtain ⟨g₁, κ, hκ, hg₁⟩ := S.exists_move_xi ha
  have ha' : actK g₁⁻¹ a = κ⁻¹ • vXi D := by
    calc actK g₁⁻¹ a = actK g₁⁻¹ (κ⁻¹ • (κ • a)) := by
          rw [smul_smul, inv_mul_cancel₀ hκ, one_smul]
      _ = κ⁻¹ • vXi D := by rw [← hg₁, map_smul, actK_inv_actK]
  have hy : IsFF7 D (actK g₁⁻¹ b) := isFF7_actK D S.h2K g₁⁻¹ hb
  have hz : IsFF7 D (actK g₁⁻¹ c) := isFF7_actK D S.h2K g₁⁻¹ hc
  have h1 : Col7 D (vXi D) (actK g₁⁻¹ b) := by
    have := (col7_actK D g₁⁻¹ _ _).2 hab
    rw [ha'] at this
    exact (col7_smul D (c := κ⁻¹) (d := 1) (inv_ne_zero hκ) one_ne_zero (a := vXi D)
      (b := actK g₁⁻¹ b)).1 (by rwa [one_smul])
  have h2' : polar (quadOdd 3 (GaloisField p (2 * f))) (actK g₁⁻¹ b) (actK g₁⁻¹ c) = 0 := by
    rw [polar_actK]
    exact hbc.1
  have h3 : polar (quadOdd 3 (GaloisField p (2 * f))) (actK g₁⁻¹ c) (vXi D) = 0 := by
    have := (col7_actK D g₁⁻¹ _ _).2 hca
    rw [ha'] at this
    exact ((col7_smul D (c := 1) (d := κ⁻¹) one_ne_zero (inv_ne_zero hκ)
      (a := actK g₁⁻¹ c) (b := vXi D)).1 (by rwa [one_smul])).1
  have hdet' : det3_7 D (vXi D) (actK g₁⁻¹ b) (actK g₁⁻¹ c) ≠ 0 := by
    have e := det3_7_actK D g₁⁻¹ a b c
    rw [ha', det3_7_smul_left] at e
    intro h
    exact hdet (by rw [← e, h, mul_zero])
  obtain ⟨ly, lz, μ, y₂, z₃, hyy, hzz, hy₂, hz₃, h5, h6, h7, h8, h9, h10⟩ :=
    exists_orth_triple D S.h2K hy hz h1 h2' h3 hdet'
  obtain ⟨w, c₁, c₂, -, -, hwξ, hwy, hwz⟩ := S.exists_two_moves hy₂ hz₃ h5 h6 h7 h8 h9 h10
  have hwξ' : actK w⁻¹ (vXi D) = vXi D := by
    have := congrArg (actK w⁻¹) hwξ
    rw [actK_inv_actK] at this
    exact this.symm
  have hinv : (g₁ * w⁻¹)⁻¹ = w * g₁⁻¹ := by group
  refine ⟨g₁ * w⁻¹, κ, hκ, ?_, ?_, ?_⟩
  · rw [actK_mul, hwξ', hg₁]
  · rw [hinv, actK_mul, hyy, map_add, map_smul, hwy, hwξ]
    exact ⟨ly, c₁, 0, by module⟩
  · rw [hinv, actK_mul, hzz, map_add, map_add, map_smul, map_smul, hwz, hwy, hwξ]
    exact ⟨lz, μ * c₁, c₂, by module⟩

end Main

end CFSG.ClassicalInvolution.PhanB3.S
