module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTU4N
public import CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylowSupport
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearTwoAutomorphism

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

namespace BU4

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K} {n₀ : ℕ}
  {W : Subgroup (hypPSU h 2 0)}

noncomputable abbrev barV (h : UnitaryFieldData p f K) (v : HypIndex 2 0 → K) :
    HypIndex 2 0 → K :=
  fun a => h.bar (v a)

theorem mulVec_barV (h : UnitaryFieldData p f K) (M : Matrix (HypIndex 2 0) (HypIndex 2 0) K)
    (v : HypIndex 2 0 → K) : M.map h.bar *ᵥ barV h v = barV h (M *ᵥ v) := by
  funext a
  simp [barV, mulVec, dotProduct]

theorem bar_eq_inv {A : GL (HypIndex 2 0) K}
    (hAA : (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
      (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar = 1) :
    (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar =
      ((A⁻¹ : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) ∧
    ((A⁻¹ : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar =
      (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) := by
  have hiA : ((A⁻¹ : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
      (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h1 : (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar =
      ((A⁻¹ : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) := by
    calc (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar
        = ((A⁻¹ : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
            ((A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
              (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar) := by
          rw [← Matrix.mul_assoc, hiA, Matrix.one_mul]
      _ = _ := by rw [hAA, Matrix.mul_one]
  refine ⟨h1, ?_⟩
  have h2 := congrArg (fun M => M.map h.bar) hiA
  simp only [Matrix.map_mul, Matrix.map_one _ (map_zero h.bar) (map_one h.bar), h1] at h2
  calc ((A⁻¹ : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar
      = ((A⁻¹ : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar *
          (((A⁻¹ : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
            (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K)) := by rw [hiA, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]

theorem semilin_mem_fixSp {A : GL (HypIndex 2 0) K}
    (hA : ∀ x, IsPElt h n₀ W x → ∃ y, IsPElt h n₀ W y ∧
      (y : Matrix (HypIndex 2 0) (HypIndex 2 0) K) = (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
        (x : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar *
          ((A⁻¹ : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K))
    (hAA : (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
      (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar = 1)
    {c : HypIndex 2 0 → K} (hc : c ∈ fixSp h n₀ W) :
    (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ barV h c ∈ fixSp h n₀ W := by
  intro y hy
  obtain ⟨x, hx, hxe⟩ := hA y hy
  obtain ⟨h1, h2⟩ := bar_eq_inv hAA
  have hyx : (y : Matrix (HypIndex 2 0) (HypIndex 2 0) K) =
      (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
        (x : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar *
          ((A⁻¹ : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) := by
    rw [hxe, Matrix.map_mul, Matrix.map_mul, h1, h2]
    have hbb : ((y : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar).map h.bar =
        (y : Matrix (HypIndex 2 0) (HypIndex 2 0) K) := by
      ext i j
      simp [h.bar_bar]
    rw [hbb]
    have e1 : (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
        ((A⁻¹ : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    simp only [Matrix.mul_assoc]
    rw [e1, Matrix.mul_one, ← Matrix.mul_assoc, e1, Matrix.one_mul]
  have hxc := hc x hx
  rw [hyx, mulVec_mulVec, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.mul_one, ← mulVec_mulVec, mulVec_barV, hxc]

theorem semilin_mem_comSp {A : GL (HypIndex 2 0) K}
    (hA : ∀ x, IsPElt h n₀ W x → ∃ y, IsPElt h n₀ W y ∧
      (y : Matrix (HypIndex 2 0) (HypIndex 2 0) K) = (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
        (x : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar *
          ((A⁻¹ : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K))
    {v : HypIndex 2 0 → K} (hv : v ∈ comSp h n₀ W) :
    (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ barV h v ∈ comSp h n₀ W := by
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x, u, hx, rfl⟩ := hw
    obtain ⟨y, hy, hye⟩ := hA x hx
    refine Submodule.subset_span ⟨y, (A : Matrix _ _ K) *ᵥ barV h u, hy, ?_⟩
    rw [hye, mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.mul_one, ← mulVec_mulVec, mulVec_barV, ← mulVec_sub]
    congr 1
    funext a
    simp [barV]
  | zero =>
    have : barV h (0 : HypIndex 2 0 → K) = 0 := funext fun a => by simp
    rw [this, mulVec_zero]
    exact Submodule.zero_mem _
  | add a b _ _ ha hb =>
    have : barV h (a + b) = barV h a + barV h b := funext fun i => by simp [barV]
    rw [this, mulVec_add]
    exact Submodule.add_mem _ ha hb
  | smul c a _ ha =>
    have : barV h (c • a) = h.bar c • barV h a := funext fun i => by simp [barV]
    rw [this, mulVec_smul]
    exact Submodule.smul_mem _ _ ha

end BU4

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
