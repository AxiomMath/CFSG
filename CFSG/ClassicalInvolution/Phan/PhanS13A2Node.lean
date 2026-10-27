module

import CFSG.ClassicalInvolution.Phan.PhanS9A1Act
import CFSG.ClassicalInvolution.Phan.PhanS9B2Rot
public import CFSG.ClassicalInvolution.Phan.PhanS12Close
public import CFSG.ClassicalInvolution.Phan.PhanS7Def

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open CFSG.LieType.Universal.Spin QuadraticMap CFSG.ClassicalInvolution.PhanB3.H
open scoped MatrixGroups

section Node0

variable {F K : Type} [Field F] [Field K] [Algebra F K] (D : KDat F K) (h2 : (2 : F) ≠ 0)

theorem piDetOne_of_La0 (A : SL(2, F)) {g : spinGroup (quadOdd 3 F)}
    (hg : spinAction (quadOdd 3 F) g = La0 h2 A) : PiDetOne D g := by
  have hx : ∀ x : W7 K, actK g x = extK (La0 h2 A).toLinearMap x := fun x => by
    simp [actK, hg]
  obtain ⟨p, q, r, s, hA⟩ := A0.exists_pqrs h2 A
  have hdA : (p + r) * (p - r) - (q + s) * (s - q) = 1 := by
    have := A.2
    rw [hA, Matrix.det_fin_two_of] at this
    exact this
  have hdK := congrArg (algebraMap F K) hdA
  simp only [map_sub, map_mul, map_add, map_one] at hdK
  refine ⟨!![algebraMap F K p + D.θ * algebraMap F K q,
      algebraMap F K r - D.θ * algebraMap F K s, 0;
    algebraMap F K r + D.θ * algebraMap F K s, algebraMap F K p - D.θ * algebraMap F K q, 0;
    0, 0, 1], ?_, ?_, ?_, ?_⟩
  · rw [Matrix.det_fin_three]
    simp
    linear_combination hdK + (algebraMap F K s ^ 2 - algebraMap F K q ^ 2) * D.theta_sq
  · rw [hx, A0.La0_vXi_pqrs D h2 A p q r s hA]
    simp
  · rw [hx, A0.La0_vE2_pqrs D h2 A p q r s hA]
    simp
  · rw [hx, La0_fix_vE3 D h2 A]
    simp

end Node0

section Node1

variable {F K : Type} [Field F] [Field K] [Algebra F K] (D : KDat F K) (h2 : (2 : F) ≠ 0)

theorem mk7_l23 (h2K : (2 : K) ≠ 0) (X Y : K) :
    mk7 0 X (D.θ * Y) 0 Y (D.θ * X) 0 =
      ((2 : K)⁻¹ * (X - Y)) • vE2 D + ((2 : K)⁻¹ * (X + Y)) • vE3 D := by
  have hi : 2 * (2 : K)⁻¹ = 1 := mul_inv_cancel₀ h2K
  rw [HA1.add_vE23, HA1.mk7_eq_iff]
  refine ⟨rfl, ?_, ?_, rfl, ?_, ?_, rfl⟩
  · linear_combination (-X) * hi
  · linear_combination (-(D.θ * Y)) * hi
  · linear_combination (-Y) * hi
  · linear_combination (-(D.θ * X)) * hi

theorem extK_La1_vE2_l23 (A : SL(2, F)) (X Y : K)
    (hX : X = algebraMap F K (A 0 0) - 2 * algebraMap F K (A 0 1) * D.θ)
    (hY : Y = -algebraMap F K (A 1 1) - algebraMap F K (A 1 0) * D.θ / 2) :
    extK (La1 h2 A).toLinearMap (vE2 D) =
      ((2 : K)⁻¹ * (X - Y)) • vE2 D + ((2 : K)⁻¹ * (X + Y)) • vE3 D := by
  subst hX hY
  rw [HA1.extK_La1_vE2]
  exact mk7_l23 D (HA1.two_ne_zero_K (K := K) h2) _ _

theorem extK_La1_vE3_l23 (A : SL(2, F)) (X Y : K)
    (hX : X = algebraMap F K (A 0 0) + 2 * algebraMap F K (A 0 1) * D.θ)
    (hY : Y = algebraMap F K (A 1 1) - algebraMap F K (A 1 0) * D.θ / 2) :
    extK (La1 h2 A).toLinearMap (vE3 D) =
      ((2 : K)⁻¹ * (X - Y)) • vE2 D + ((2 : K)⁻¹ * (X + Y)) • vE3 D := by
  subst hX hY
  rw [HA1.extK_La1_vE3]
  exact mk7_l23 D (HA1.two_ne_zero_K (K := K) h2) _ _

theorem det_l23 (a b c d θ X Y X' Y' : K) (h2K : (2 : K) ≠ 0) (hθ : θ ^ 2 = -1)
    (hd : a * d - b * c = 1) (hX : X = a - 2 * b * θ) (hY : Y = -d - c * θ / 2)
    (hX' : X' = a + 2 * b * θ) (hY' : Y' = d - c * θ / 2) :
    (2 : K)⁻¹ * (X - Y) * ((2 : K)⁻¹ * (X' + Y')) -
      (2 : K)⁻¹ * (X' - Y') * ((2 : K)⁻¹ * (X + Y)) = 1 := by
  have hu : 2 * (2 : K)⁻¹ = 1 := mul_inv_cancel₀ h2K
  subst hX hY hX' hY'
  linear_combination hd + (b * c) * hθ +
    (a * d * (2 * (2 : K)⁻¹ + 1) + b * c * θ ^ 2 * (4 * (2 : K)⁻¹ ^ 2 + 2 * (2 : K)⁻¹ + 1)) * hu

theorem piDetOne_of_La1 (A : SL(2, F)) {g : spinGroup (quadOdd 3 F)}
    (hg : spinAction (quadOdd 3 F) g = La1 h2 A) : PiDetOne D g := by
  have hx : ∀ x : W7 K, actK g x = extK (La1 h2 A).toLinearMap x := fun x => by
    simp [actK, hg]
  have h2K := HA1.two_ne_zero_K (K := K) h2
  have hdA : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    have := A.2
    rwa [Matrix.det_fin_two] at this
  have hdK := congrArg (algebraMap F K) hdA
  simp only [map_sub, map_mul, map_one] at hdK
  obtain ⟨X, hX⟩ : ∃ X : K, X = algebraMap F K (A 0 0) - 2 * algebraMap F K (A 0 1) * D.θ :=
    ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : K,
      Y = -algebraMap F K (A 1 1) - algebraMap F K (A 1 0) * D.θ / 2 := ⟨_, rfl⟩
  obtain ⟨X', hX'⟩ : ∃ X' : K, X' = algebraMap F K (A 0 0) + 2 * algebraMap F K (A 0 1) * D.θ :=
    ⟨_, rfl⟩
  obtain ⟨Y', hY'⟩ : ∃ Y' : K,
      Y' = algebraMap F K (A 1 1) - algebraMap F K (A 1 0) * D.θ / 2 := ⟨_, rfl⟩
  refine ⟨!![1, 0, 0; 0, (2 : K)⁻¹ * (X - Y), (2 : K)⁻¹ * (X' - Y');
    0, (2 : K)⁻¹ * (X + Y), (2 : K)⁻¹ * (X' + Y')], ?_, ?_, ?_, ?_⟩
  · rw [Matrix.det_fin_three]
    simp
    linear_combination det_l23 _ _ _ _ D.θ X Y X' Y' h2K D.theta_sq hdK hX hY hX' hY'
  · rw [hx, La1_fix_vXi D h2 A]
    simp
  · rw [hx, extK_La1_vE2_l23 D h2 A X Y hX hY]
    simp
  · rw [hx, extK_La1_vE3_l23 D h2 A X' Y' hX' hY']
    simp

end Node1

end CFSG.ClassicalInvolution.PhanB3.S
