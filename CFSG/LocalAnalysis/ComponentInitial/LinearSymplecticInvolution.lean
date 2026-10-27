module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.LocalAnalysis.ComponentInitial.LinearIsometry
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

open Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem add_self_eq_zero_zmod_two (x : V) : x + x = 0 := by
  rw [← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem sub_eq_add_zmod_two (x y : V) : x - y = x + y := by
  rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_left (add_self_eq_zero_zmod_two y)]

variable {b : LinearMap.BilinForm (ZMod 2) V}

@[expose] def pointwiseStabilizer (b : LinearMap.BilinForm (ZMod 2) V)
    (W : Submodule (ZMod 2) V) : Subgroup (bilinIsometryGroup b) where
  carrier := {g | ∀ w ∈ W, (((g : LinearMap.GeneralLinearGroup (ZMod 2) V) :
    V →ₗ[ZMod 2] V)) w = w}
  one_mem' _ _ := rfl
  mul_mem' {g h} hg hh w hw := by
    change ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V)
      (((h : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) w) = w
    rw [hh w hw, hg w hw]
  inv_mem' {g} hg w hw := by
    have h := congrArg (fun f : V →ₗ[ZMod 2] V => f w)
      (congrArg Units.val (inv_mul_cancel (g : LinearMap.GeneralLinearGroup (ZMod 2) V)))
    simp only [Units.val_mul, Module.End.mul_apply, hg w hw, Units.val_one,
      Module.End.one_apply] at h
    exact h

theorem mem_pointwiseStabilizer {W : Submodule (ZMod 2) V} {g : bilinIsometryGroup b} :
    g ∈ pointwiseStabilizer b W ↔
      ∀ w ∈ W, (((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V)) w = w :=
  Iff.rfl

theorem range_sub_one_le_orthogonal {W : Submodule (ZMod 2) V}
    {g : LinearMap.GeneralLinearGroup (ZMod 2) V} (hg : g ∈ bilinIsometryGroup b)
    (hgW : ∀ w ∈ W, (g : V →ₗ[ZMod 2] V) w = w) :
    LinearMap.range ((g : V →ₗ[ZMod 2] V) - 1) ≤ b.orthogonal W := by
  rintro _ ⟨v, rfl⟩ w hw
  change b w (((g : V →ₗ[ZMod 2] V) - 1) v) = 0
  rw [LinearMap.sub_apply, Module.End.one_apply, map_sub, ← hg w v, hgW w hw, sub_self]

theorem orthogonal_eq_range_sub_one [FiniteDimensional (ZMod 2) V] (hb : b.Nondegenerate)
    {a : LinearMap.GeneralLinearGroup (ZMod 2) V} (ha : a ∈ bilinIsometryGroup b) :
    b.orthogonal (LinearMap.ker ((a : V →ₗ[ZMod 2] V) - 1)) =
      LinearMap.range ((a : V →ₗ[ZMod 2] V) - 1) := by
  refine (Submodule.eq_of_le_of_finrank_eq
    (range_sub_one_le_orthogonal ha fun w hw => ?_) ?_).symm
  · simpa [sub_eq_zero] using hw
  · have hrank := LinearMap.finrank_range_add_finrank_ker
      ((a : V →ₗ[ZMod 2] V) - (1 : V →ₗ[ZMod 2] V))
    rw [LinearMap.BilinForm.finrank_orthogonal hb]
    omega

theorem range_sub_one_le_ker_sub_one {a : LinearMap.GeneralLinearGroup (ZMod 2) V}
    (ha2 : a ^ 2 = 1) :
    LinearMap.range ((a : V →ₗ[ZMod 2] V) - 1) ≤ LinearMap.ker ((a : V →ₗ[ZMod 2] V) - 1) := by
  have haa : ∀ v, (a : V →ₗ[ZMod 2] V) ((a : V →ₗ[ZMod 2] V) v) = v := fun v => by
    have h := congrArg (fun f : V →ₗ[ZMod 2] V => f v) (congrArg Units.val ha2)
    simpa [sq] using h
  rintro _ ⟨v, rfl⟩
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.sub_apply, Module.End.one_apply,
    Module.End.one_apply, map_sub, haa]
  calc v - (a : V →ₗ[ZMod 2] V) v - ((a : V →ₗ[ZMod 2] V) v - v) =
      (v + v) - ((a : V →ₗ[ZMod 2] V) v + (a : V →ₗ[ZMod 2] V) v) := by abel
    _ = 0 := by rw [add_self_eq_zero_zmod_two, add_self_eq_zero_zmod_two, sub_zero]

theorem mul_sub_one_apply {W : Submodule (ZMod 2) V} (hW : b.orthogonal W ≤ W)
    {g h : bilinIsometryGroup b} (hg : g ∈ pointwiseStabilizer b W)
    (hh : h ∈ pointwiseStabilizer b W) (v : V) :
    (((g * h : bilinIsometryGroup b) : LinearMap.GeneralLinearGroup (ZMod 2) V) :
        V →ₗ[ZMod 2] V) v - v =
      ((((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) v - v) +
        (((h : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) v - v)) := by
  set G := ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V)
  set H := ((h : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V)
  have hN : H v - v ∈ W :=
    hW (range_sub_one_le_orthogonal h.2 hh ⟨v, by simp [H]⟩)
  have hGN : G (H v - v) = H v - v := hg _ hN
  change G (H v) - v = (G v - v) + (H v - v)
  rw [map_sub] at hGN
  rw [show G (H v) = G (H v) - G v + G v by abel, hGN]
  abel

variable (b) in
@[expose] def pointwiseStabilizerHom {W : Submodule (ZMod 2) V} (hW : b.orthogonal W ≤ W) :
    pointwiseStabilizer b W →* Multiplicative ((V ⧸ W) →ₗ[ZMod 2] b.orthogonal W) where
  toFun g := Multiplicative.ofAdd (W.liftQ (LinearMap.codRestrict (b.orthogonal W)
    ((((g : bilinIsometryGroup b) : LinearMap.GeneralLinearGroup (ZMod 2) V) :
      V →ₗ[ZMod 2] V) - 1)
    fun v => range_sub_one_le_orthogonal (g : bilinIsometryGroup b).2 g.2 ⟨v, rfl⟩)
    fun w hw => by
      rw [LinearMap.mem_ker]
      ext
      simp [g.2 w hw])
  map_one' := by
    apply Multiplicative.toAdd.injective
    refine Submodule.linearMap_qext _ (LinearMap.ext fun v => Subtype.ext ?_)
    simp
  map_mul' g h := by
    apply Multiplicative.toAdd.injective
    refine Submodule.linearMap_qext _ (LinearMap.ext fun v => Subtype.ext ?_)
    have := mul_sub_one_apply hW g.2 h.2 v
    simpa using this

theorem pointwiseStabilizerHom_apply {W : Submodule (ZMod 2) V} (hW : b.orthogonal W ≤ W)
    (g : pointwiseStabilizer b W) (x : V) :
    ((Multiplicative.toAdd (pointwiseStabilizerHom b hW g)) (Submodule.Quotient.mk x) : V) =
      (((g : bilinIsometryGroup b) : LinearMap.GeneralLinearGroup (ZMod 2) V) :
        V →ₗ[ZMod 2] V) x - x := rfl

theorem pointwiseStabilizerHom_injective {W : Submodule (ZMod 2) V} (hW : b.orthogonal W ≤ W) :
    Function.Injective (pointwiseStabilizerHom b hW) := by
  intro g h hgh
  have hx := fun x => congrArg (fun φ => ((Multiplicative.toAdd φ) (Submodule.Quotient.mk x) : V))
    hgh
  simp only [pointwiseStabilizerHom_apply, sub_left_inj] at hx
  exact Subtype.ext (Subtype.ext (Units.ext (LinearMap.ext hx)))

theorem binary_symplectic_involution_fixed_space_pointwise_stabilizer
    [FiniteDimensional (ZMod 2) V] (hb : b.Nondegenerate)
    {a : LinearMap.GeneralLinearGroup (ZMod 2) V}
    (ha : a ∈ bilinIsometryGroup b) (ha2 : a ^ 2 = 1) {W : Submodule (ZMod 2) V}
    (hW : W = LinearMap.ker ((a : V →ₗ[ZMod 2] V) - 1)) :
    b.orthogonal W = LinearMap.range ((a : V →ₗ[ZMod 2] V) - 1) ∧ b.orthogonal W ≤ W ∧
    (∀ g ∈ bilinIsometryGroup b, (∀ w ∈ W, (g : V →ₗ[ZMod 2] V) w = w) →
      LinearMap.range ((g : V →ₗ[ZMod 2] V) - 1) ≤ b.orthogonal W ∧
        ∀ w ∈ W, ((g : V →ₗ[ZMod 2] V) - 1) w = 0) ∧
    Finite (pointwiseStabilizer b W) ∧ IsElementaryAbelian 2 (pointwiseStabilizer b W) ∧
    ∃ φ : pointwiseStabilizer b W →* Multiplicative ((V ⧸ W) →ₗ[ZMod 2] b.orthogonal W),
      Function.Injective φ ∧ ∀ (g : pointwiseStabilizer b W) (x : V),
        ((Multiplicative.toAdd (φ g)) (Submodule.Quotient.mk x) : V) =
          (((g : bilinIsometryGroup b) : LinearMap.GeneralLinearGroup (ZMod 2) V) :
            V →ₗ[ZMod 2] V) x - x := by
  subst hW
  have horth := orthogonal_eq_range_sub_one hb ha
  have hle : b.orthogonal (LinearMap.ker ((a : V →ₗ[ZMod 2] V) - 1)) ≤
      LinearMap.ker ((a : V →ₗ[ZMod 2] V) - 1) := horth ▸ range_sub_one_le_ker_sub_one ha2
  set W := LinearMap.ker ((a : V →ₗ[ZMod 2] V) - 1)
  have hinj := pointwiseStabilizerHom_injective hle
  have hcomm : ∀ g h : pointwiseStabilizer b W, g * h = h * g := by
    intro g h
    apply hinj
    rw [map_mul, map_mul, mul_comm]
  have hsq : ∀ g : pointwiseStabilizer b W, g ^ 2 = 1 := by
    intro g
    apply hinj
    rw [map_pow, map_one]
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, two_smul, add_self_eq_zero_zmod_two]
  have hEA : IsElementaryAbelian 2 (pointwiseStabilizer b W) :=
    { toIsMulCommutative := ⟨⟨hcomm⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hsq }
  refine ⟨horth, hle, fun g hg hgW => ⟨range_sub_one_le_orthogonal hg hgW, fun w hw => ?_⟩,
    ?_, hEA, pointwiseStabilizerHom b hle, hinj, pointwiseStabilizerHom_apply hle⟩
  · rw [LinearMap.sub_apply, Module.End.one_apply, hgW w hw, sub_self]
  · have : Finite (V ⧸ W →ₗ[ZMod 2] b.orthogonal W) := Module.finite_of_finite (ZMod 2)
    exact Finite.of_injective _ hinj

end CFSG.LocalAnalysis.ComponentInitial
