module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaPDGen

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix Module QuadraticMap CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Plane

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]

@[expose] noncomputable def pdRotLin (Q : QuadraticForm K (ι → K)) (a b : ι → K) :
    (ι → K) →ₗ[K] (ι → K) :=
  LinearMap.id + ((polarBilin Q).flip b).smulRight (a + b) + ((polarBilin Q).flip a).smulRight a

@[expose] noncomputable def pdRotMat (Q : QuadraticForm K (ι → K)) (a b : ι → K) : Matrix ι ι K :=
  LinearMap.toMatrix' (pdRotLin Q a b)

variable {Q : QuadraticForm K (ι → K)} {a b : ι → K}

theorem pdRotMat_mulVec (x : ι → K) :
    pdRotMat Q a b *ᵥ x = x + polar Q x b • (a + b) + polar Q x a • a := by
  rw [pdRotMat, LinearMap.toMatrix'_mulVec]
  simp [pdRotLin, LinearMap.smulRight_apply, polarBilin_apply_apply]

theorem pdRotMat_mulVec' (x : ι → K) :
    pdRotMat Q a b *ᵥ x = x + (polar Q x a + polar Q x b) • a + polar Q x b • b := by
  rw [pdRotMat_mulVec, smul_add, add_smul]
  abel

theorem pdRotMat_mulVec_of_polar {x : ι → K} (hxa : polar Q x a = 0) (hxb : polar Q x b = 0) :
    pdRotMat Q a b *ᵥ x = x := by
  rw [pdRotMat_mulVec, hxa, hxb, zero_smul, zero_smul, add_zero, add_zero]

variable [CharP K 2]

omit [Fintype ι] [DecidableEq ι] in
theorem pd_polar_self_two (x : ι → K) : polar Q x x = 0 := by
  rw [polar_self, two_nsmul, CharTwo.add_self_eq_zero]

omit [Fintype ι] [DecidableEq ι] in
theorem pd_add_self (v : ι → K) : v + v = 0 := by
  rw [← two_smul K v, CharTwo.two_eq_zero, zero_smul]

variable (ha : Q a = 1) (hb : Q b = 1) (hab : polar Q a b = 1)
include hab

theorem pdRotMat_polar_a (x : ι → K) :
    polar Q (pdRotMat Q a b *ᵥ x) a = polar Q x a + polar Q x b := by
  rw [pdRotMat_mulVec', polar_add_left, polar_add_left, polar_smul_left, polar_smul_left,
    pd_polar_self_two, polar_comm (⇑Q) b a, hab]
  simp

theorem pdRotMat_polar_b (x : ι → K) : polar Q (pdRotMat Q a b *ᵥ x) b = polar Q x a := by
  rw [pdRotMat_mulVec', polar_add_left, polar_add_left, polar_smul_left, polar_smul_left,
    pd_polar_self_two, hab]
  simp only [smul_eq_mul, mul_one, mul_zero, add_zero]
  rw [add_comm (polar Q x a), ← add_assoc, CharTwo.add_self_eq_zero, zero_add]

theorem pdRotMat_mulVec_a : pdRotMat Q a b *ᵥ a = b := by
  rw [pdRotMat_mulVec', pd_polar_self_two, hab, zero_add, one_smul, one_smul, pd_add_self,
    zero_add]

theorem pdRotMat_mulVec_b : pdRotMat Q a b *ᵥ b = a + b := by
  rw [pdRotMat_mulVec', pd_polar_self_two, polar_comm (⇑Q) b a, hab, add_zero, one_smul,
    zero_smul, add_zero, add_comm]

include ha hb in
theorem pdRotMat_isometry (x : ι → K) : Q (pdRotMat Q a b *ᵥ x) = Q x := by
  rw [pdRotMat_mulVec']
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [add_assoc, QuadraticMap.map_add (⇑Q) x, QuadraticMap.map_add (⇑Q) _ (polar Q x b • b),
    QuadraticMap.map_smul, QuadraticMap.map_smul, polar_add_right, polar_smul_right,
    polar_smul_right, polar_smul_left, polar_smul_right, ha, hb, hab]
  simp only [smul_eq_mul, mul_one]
  linear_combination (polar Q x a * polar Q x a + 2 * polar Q x a * polar Q x b +
    2 * polar Q x b * polar Q x b) * h2

theorem pdRotMat_cube (x : ι → K) :
    pdRotMat Q a b *ᵥ (pdRotMat Q a b *ᵥ (pdRotMat Q a b *ᵥ x)) = x := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [pdRotMat_mulVec' (pdRotMat Q a b *ᵥ (pdRotMat Q a b *ᵥ x)),
    pdRotMat_polar_a hab, pdRotMat_polar_b hab, pdRotMat_polar_a hab, pdRotMat_polar_b hab,
    pdRotMat_mulVec' (pdRotMat Q a b *ᵥ x), pdRotMat_polar_a hab, pdRotMat_polar_b hab,
    pdRotMat_mulVec' x]
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination ((3 * polar Q x a + 2 * polar Q x b) * a i +
    (polar Q x a + polar Q x b) * b i) * h2

theorem pdRotMat_mul_cube : pdRotMat Q a b * (pdRotMat Q a b * pdRotMat Q a b) = 1 := by
  refine pd_matrix_ext_mulVec fun x => ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, pdRotMat_cube hab, Matrix.one_mulVec]

theorem pdRotMat_mul_cube' : pdRotMat Q a b * pdRotMat Q a b * pdRotMat Q a b = 1 := by
  rw [Matrix.mul_assoc, pdRotMat_mul_cube hab]

@[expose] noncomputable def pdRotGL : GL ι K :=
  ⟨pdRotMat Q a b, pdRotMat Q a b * pdRotMat Q a b, pdRotMat_mul_cube hab, pdRotMat_mul_cube' hab⟩

omit [CharP K 2] in
theorem coe_pdRotGL [CharP K 2] : ((pdRotGL hab : GL ι K) : Matrix ι ι K) = pdRotMat Q a b := rfl

include ha hb in
theorem pdRotGL_mem_statedOmega [Finite K] (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (ι → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) :
    pdRotGL hab ∈ StatedOmega ⇑Q := by
  have hB : ∀ v, Q (((pdRotGL hab * pdRotGL hab : GL ι K) : Matrix ι ι K) *ᵥ v) = Q v :=
    fun v => by
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, coe_pdRotGL, pdRotMat_isometry ha hb hab,
        pdRotMat_isometry ha hb hab]
  have h4 : (pdRotGL hab * pdRotGL hab) * (pdRotGL hab * pdRotGL hab) = pdRotGL hab := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_pdRotGL, ← Matrix.mul_assoc, pdRotMat_mul_cube' hab,
      Matrix.one_mul]
  rw [← h4]
  exact pdMul_self_mem_statedOmega Q hQ hT hB

omit [Fintype ι] [DecidableEq ι] in
theorem pd_plane_polar (p q : K) :
    polar Q (p • a + q • b) b = p ∧ polar Q (p • a + q • b) a = q := by
  refine ⟨?_, ?_⟩
  · rw [polar_add_left, polar_smul_left, polar_smul_left, hab, pd_polar_self_two]
    simp
  · rw [polar_add_left, polar_smul_left, polar_smul_left, pd_polar_self_two,
      polar_comm (⇑Q) b a, hab]
    simp

theorem pdRot_comm_plane {g : Matrix ι ι K} (hg : g * pdRotMat Q a b = pdRotMat Q a b * g) :
    g *ᵥ a = polar Q (g *ᵥ a) b • a + polar Q (g *ᵥ a) a • b ∧
      g *ᵥ b = polar Q (g *ᵥ a) a • a + (polar Q (g *ᵥ a) b + polar Q (g *ᵥ a) a) • b := by
  have hgc : ∀ z, g *ᵥ (pdRotMat Q a b *ᵥ z) = pdRotMat Q a b *ᵥ (g *ᵥ z) := fun z => by
    rw [Matrix.mulVec_mulVec, hg, ← Matrix.mulVec_mulVec]
  have hga : g *ᵥ a = (polar Q (g *ᵥ b) a + polar Q (g *ᵥ b) b) • a + polar Q (g *ᵥ b) b • b := by
    have h1 : a = pdRotMat Q a b *ᵥ b - b := by
      rw [pdRotMat_mulVec_b hab, add_sub_cancel_right]
    have h2 := pdRotMat_mulVec' (Q := Q) (a := a) (b := b) (g *ᵥ b)
    conv_lhs => rw [h1]
    rw [Matrix.mulVec_sub, hgc, h2]
    abel
  set p := polar Q (g *ᵥ b) a + polar Q (g *ᵥ b) b with hp
  set q := polar Q (g *ᵥ b) b with hq
  obtain ⟨hpb, hqa⟩ := pd_plane_polar hab p q
  rw [← hga] at hpb hqa
  refine ⟨by rw [hpb, hqa]; exact hga, ?_⟩
  rw [hpb, hqa, ← pdRotMat_mulVec_a hab, hgc, hga, Matrix.mulVec_add, Matrix.mulVec_smul,
    Matrix.mulVec_smul, pdRotMat_mulVec_a hab, pdRotMat_mulVec_b hab]
  module

theorem pdRot_mulVec_plane_eq {g : Matrix ι ι K} (hg : g * pdRotMat Q a b = pdRotMat Q a b * g)
    (p q : K) : g *ᵥ (p • a + q • b) =
      (p * polar Q (g *ᵥ a) b + q * polar Q (g *ᵥ a) a) • a +
        (p * polar Q (g *ᵥ a) a + q * (polar Q (g *ᵥ a) b + polar Q (g *ᵥ a) a)) • b := by
  obtain ⟨h1, h2⟩ := pdRot_comm_plane hab hg
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
  conv_lhs => rw [h1, h2]
  module

theorem pdRot_mulVec_plane {g : Matrix ι ι K} (hg : g * pdRotMat Q a b = pdRotMat Q a b * g)
    (p q : K) : ∃ p' q' : K, g *ᵥ (p • a + q • b) = p' • a + q' • b :=
  ⟨_, _, pdRot_mulVec_plane_eq hab hg p q⟩

theorem pdRot_mul_comm_plane {x y : Matrix ι ι K} (hx : x * pdRotMat Q a b = pdRotMat Q a b * x)
    (hy : y * pdRotMat Q a b = pdRotMat Q a b * y) (p q : K) :
    (x * y) *ᵥ (p • a + q • b) = (y * x) *ᵥ (p • a + q • b) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  simp only [pdRot_mulVec_plane_eq hab hx, pdRot_mulVec_plane_eq hab hy]
  module

theorem pdRot_commutator_fix {x y : GL ι K} (hx : x * pdRotGL hab = pdRotGL hab * x)
    (hy : y * pdRotGL hab = pdRotGL hab * y) :
    ((⁅x, y⁆ : GL ι K) : Matrix ι ι K) *ᵥ a = a ∧ ((⁅x, y⁆ : GL ι K) : Matrix ι ι K) *ᵥ b = b := by
  have hcomm : ∀ g : GL ι K, g * pdRotGL hab = pdRotGL hab * g →
      (g : Matrix ι ι K) * pdRotMat Q a b = pdRotMat Q a b * g := fun g h => by
    have h1 := congrArg Units.val h
    rwa [Units.val_mul, Units.val_mul, coe_pdRotGL] at h1
  have hinv : ∀ g : GL ι K, g * pdRotGL hab = pdRotGL hab * g →
      g⁻¹ * pdRotGL hab = pdRotGL hab * g⁻¹ := fun g h => by
    calc g⁻¹ * pdRotGL hab = g⁻¹ * (pdRotGL hab * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * pdRotGL hab) * g⁻¹ := by rw [h]
      _ = pdRotGL hab * g⁻¹ := by group
  have hx' := hcomm x hx
  have hy' := hcomm y hy
  have hxi := hcomm _ (hinv x hx)
  have hyi := hcomm _ (hinv y hy)
  have key : ∀ p q : K, ((⁅x, y⁆ : GL ι K) : Matrix ι ι K) *ᵥ (p • a + q • b) = p • a + q • b := by
    intro p q
    obtain ⟨p1, q1, h1⟩ := pdRot_mulVec_plane hab hyi p q
    obtain ⟨p2, q2, h2⟩ := pdRot_mulVec_plane hab hxi p1 q1
    have hw : (((x⁻¹ * y⁻¹ : GL ι K)) : Matrix ι ι K) *ᵥ (p • a + q • b) = p2 • a + q2 • b := by
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, h1, h2]
    have hc : ((⁅x, y⁆ : GL ι K) : Matrix ι ι K) =
        ((x * y : GL ι K) : Matrix ι ι K) * ((x⁻¹ * y⁻¹ : GL ι K) : Matrix ι ι K) := by
      rw [commutatorElement_def, ← Units.val_mul]
      congr 1
      group
    have hyx : ((y * x : GL ι K) : Matrix ι ι K) * ((x⁻¹ * y⁻¹ : GL ι K) : Matrix ι ι K) = 1 := by
      rw [← Units.val_mul, show y * x * (x⁻¹ * y⁻¹) = 1 by group, Units.val_one]
    rw [hc, ← Matrix.mulVec_mulVec, hw, Units.val_mul, pdRot_mul_comm_plane hab hx' hy',
      ← hw, Matrix.mulVec_mulVec, ← Units.val_mul, hyx, Matrix.one_mulVec]
  refine ⟨?_, ?_⟩
  · have h := key 1 0
    rwa [one_smul, zero_smul, add_zero] at h
  · have h := key 0 1
    rwa [one_smul, zero_smul, zero_add] at h

end Plane

end CFSG.SeitzReduction.SymplecticPilot
