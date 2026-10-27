module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SympU4Surv

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

namespace BU4

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped commutatorElement

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}

theorem eq_of_semilinearAutHom_eq {x y : semilinearSimilitudes h 2 0}
    (hxy : semilinearAutHom h (by norm_num) (by norm_num) x =
      semilinearAutHom h (by norm_num) (by norm_num) y) :
    (x : SemiGL (HypIndex 2 0) K).right = (y : SemiGL (HypIndex 2 0) K).right ∧
      ∃ c : Kˣ, (x : SemiGL (HypIndex 2 0) K).left =
        GeneralLinearGroup.scalar _ c * (y : SemiGL (HypIndex 2 0) K).left := by
  have h1 : semilinearAutHom h (by norm_num) (by norm_num) (x * y⁻¹) = 1 := by
    rw [map_mul, map_inv, hxy, mul_inv_cancel]
  obtain ⟨hr, c, hc⟩ := (semilinearAutHom_eq_one_iff h (by norm_num) (by norm_num) (by norm_num)
    (x * y⁻¹)).mp h1
  rw [Subgroup.coe_mul, Subgroup.coe_inv, SemidirectProduct.mul_right,
    SemidirectProduct.inv_right] at hr
  have hr' : (x : SemiGL (HypIndex 2 0) K).right = (y : SemiGL (HypIndex 2 0) K).right := by
    have := congrArg (· * (y : SemiGL (HypIndex 2 0) K).right) hr
    simp only [inv_mul_cancel_right] at this
    exact this.trans (one_mul _)
  refine ⟨hr', c, ?_⟩
  rw [Subgroup.coe_mul, Subgroup.coe_inv, SemidirectProduct.mul_left,
    SemidirectProduct.inv_left, ← MulAut.mul_apply, ← map_mul, hr', mul_inv_cancel, map_one,
    MulAut.one_apply] at hc
  calc (x : SemiGL (HypIndex 2 0) K).left
      = (x : SemiGL (HypIndex 2 0) K).left * (y : SemiGL (HypIndex 2 0) K).left⁻¹ *
          (y : SemiGL (HypIndex 2 0) K).left := by group
    _ = _ := by rw [hc]

theorem eq_of_eq_mul {B A A₃ : GL (HypIndex 2 0) K} {σ σ₃ : K ≃+* K}
    (hxB : (⟨B, RingEquiv.refl K⟩ : SemiGL (HypIndex 2 0) K) ∈ semilinearSimilitudes h 2 0)
    (hxA : (⟨A, σ⟩ : SemiGL (HypIndex 2 0) K) ∈ semilinearSimilitudes h 2 0)
    (hx₃ : (⟨A₃, σ₃⟩ : SemiGL (HypIndex 2 0) K) ∈ semilinearSimilitudes h 2 0)
    (he : semilinearAutHom h (by norm_num) (by norm_num) ⟨_, hx₃⟩ =
      semilinearAutHom h (by norm_num) (by norm_num) ⟨_, hxB⟩ *
        semilinearAutHom h (by norm_num) (by norm_num) ⟨_, hxA⟩) :
    σ₃ = σ ∧ ∃ c : Kˣ, A₃ = GeneralLinearGroup.scalar _ c * (B * A) := by
  rw [← map_mul] at he
  obtain ⟨hr, c, hc⟩ := eq_of_semilinearAutHom_eq he
  refine ⟨hr.trans (one_mul σ), c, ?_⟩
  have e : glAut (RingEquiv.refl K) A = A := by
    rw [show RingEquiv.refl K = 1 from rfl, map_one, MulAut.one_apply]
  rw [Subgroup.coe_mul, SemidirectProduct.mul_left] at hc
  exact hc.trans (by rw [e])

theorem ne_smul_of_ne_one {B : GL (HypIndex 2 0) K}
    {hx : (⟨B, RingEquiv.refl K⟩ : SemiGL (HypIndex 2 0) K) ∈ semilinearSimilitudes h 2 0}
    (h1 : semilinearAutHom h (by norm_num) (by norm_num) ⟨_, hx⟩ ≠ 1) :
    ∀ μ : K, (B : Matrix (HypIndex 2 0) (HypIndex 2 0) K) ≠ μ • 1 := by
  intro μ hμ
  apply h1
  rw [semilinearAutHom_eq_one_iff h (by norm_num) (by norm_num) (by norm_num)]
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hμ
    exact B.ne_zero hμ
  refine ⟨rfl, Units.mk0 μ hμ0, Units.ext ?_⟩
  rw [GeneralLinearGroup.coe_scalar, Units.val_mk0, Matrix.scalar_apply, ← smul_one_eq_diagonal]
  exact hμ

theorem lin_or_semi {u : MulAut (hypPSU h 2 0)} (hS : SurvU4Orth h u) :
    (∃ (B : GL (HypIndex 2 0) K)
      (hx : (⟨B, RingEquiv.refl K⟩ : SemiGL (HypIndex 2 0) K) ∈ semilinearSimilitudes h 2 0),
      B ∈ hypUnitary h 2 0 ∧
      (∃ s : K, (B : Matrix (HypIndex 2 0) (HypIndex 2 0) K) * B = s • 1) ∧
      u = semilinearAutHom h (by norm_num) (by norm_num) ⟨_, hx⟩) ∨
    ∃ (A : GL (HypIndex 2 0) K) (σ : K ≃+* K)
      (hx : (⟨A, σ⟩ : SemiGL (HypIndex 2 0) K) ∈ semilinearSimilitudes h 2 0),
      A ∈ hypUnitary h 2 0 ∧ (∀ c, σ c = h.bar c) ∧
      (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
        (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar = 1 ∧
      u = semilinearAutHom h (by norm_num) (by norm_num) ⟨_, hx⟩ := by
  rcases hS with ⟨B, l, hx, hB, -, hBB, -, -, hu⟩ | ⟨B, l, hx, hB, -, hBB, -, hu⟩ | hS
  · exact Or.inl ⟨B, hx, hB, ⟨_, hBB⟩, hu⟩
  · exact Or.inl ⟨B, hx, hB, ⟨_, hBB⟩, hu⟩
  · exact Or.inr hS

end BU4

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
