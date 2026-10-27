module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GroupTheory.WeirSylow.FieldTorus
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareSquareCases
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2GenInr
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesSimil
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import Certificates.Data.ExceptionalSL3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup QuadraticMap
open CFSG.GroupTheory.WeirSylow
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ff_commSp_reflOf (hQ : Q.Nondegenerate) {a : V} (ha : Q a ≠ 0) :
    commSp (reflOf Q a ha) = Submodule.span (ZMod 3) {a} := by
  have h2 : reflOf Q a ha * reflOf Q a ha = 1 := reflOf_mul_self a ha
  ext v
  rw [mem_commSp_iff h2, Submodule.mem_span_singleton]
  constructor
  · intro hv
    have key : v - (polar Q a v / Q a) • a = -v := by
      rw [← coe_reflOf_apply a ha v, hv]
    have hzero : (2 : ZMod 3) • v = (polar Q a v / Q a) • a := by
      have h := congrArg (fun z : V => z + v) key
      rw [neg_add_cancel] at h
      have h' : (2 : ZMod 3) • v - (polar Q a v / Q a) • a = 0 := by
        rw [← h]; module
      exact sub_eq_zero.mp h'
    refine ⟨2 * (polar Q a v / Q a), ?_⟩
    have h4 : (2 : ZMod 3) * 2 = 1 := by decide
    have hcalc : v = ((2 : ZMod 3) * (polar Q a v / Q a)) • a := by
      calc v = (2 : ZMod 3) • ((2 : ZMod 3) • v) := by rw [smul_smul, h4, one_smul]
        _ = (2 : ZMod 3) • ((polar Q a v / Q a) • a) := by rw [hzero]
        _ = ((2 : ZMod 3) * (polar Q a v / Q a)) • a := by rw [smul_smul]
    exact hcalc.symm
  · rintro ⟨k, rfl⟩
    have hqa : ((reflOf Q a ha : OGroup Q) : V ≃ₗ[ZMod 3] V) a = -a := by
      rw [coe_reflOf_apply a ha a, polar_self, nsmul_eq_mul,
        show (↑(2 : ℕ) : ZMod 3) = 2 by norm_num]
      have h2' : (2 : ZMod 3) * Q a / Q a = 2 := by
        rw [mul_div_assoc, div_self ha, mul_one]
      rw [h2']
      module
    calc ((reflOf Q a ha : OGroup Q) : V ≃ₗ[ZMod 3] V) (k • a)
        = k • (((reflOf Q a ha : OGroup Q) : V ≃ₗ[ZMod 3] V) a) := map_smul _ _ _
      _ = k • (-a) := by rw [hqa]
      _ = -(k • a) := by rw [smul_neg]

theorem ff_quadSign_span (hQ : Q.Nondegenerate) {a : V} (ha : Q a ≠ 0) :
    quadSign (Q.restrict (Submodule.span (ZMod 3) {a})) = toSign (Units.mk0 (Q a) ha) := by
  have ha0 : a ≠ 0 := fun h => ha (by rw [h, map_zero])
  let u : (ZMod 3)ˣ := Units.mk0 (Q a) ha
  have hu : (u : ZMod 3) = Q a := Units.val_mk0 ha
  let pres : TauCeti.RegularFormPresentation (ZMod 3) := ⟨1, fun _ : Fin 1 => u⟩
  let P : QuadraticForm (ZMod 3) (Fin 1 → ZMod 3) := TauCeti.presentedForm pres
  have hP : P.Nondegenerate := TauCeti.nondegenerate_presentedForm pres
  let e : (Submodule.span (ZMod 3) {a}) ≃ₗ[ZMod 3] (Fin 1 → ZMod 3) :=
    (LinearEquiv.toSpanNonzeroSingleton (ZMod 3) V a ha0).symm.trans
      (LinearEquiv.funUnique (Fin 1) (ZMod 3) (ZMod 3)).symm
  have he : (Q.restrict (Submodule.span (ZMod 3) {a})).IsometryEquiv P :=
    { toLinearEquiv := e
      map_app' := by
        intro x
        have hx : ((LinearEquiv.toSpanNonzeroSingleton (ZMod 3) V a ha0).symm x) • a
            = (x : V) := LinearEquiv.toSpanNonzeroSingleton_symm_apply_smul (ZMod 3) V a ha0 x
        change P (e x) = Q (x : V)
        rw [show e x = fun _ : Fin 1 => ((LinearEquiv.toSpanNonzeroSingleton
          (ZMod 3) V a ha0).symm x) by rfl]
        rw [TauCeti.presentedForm_apply, Fin.sum_univ_one, hu, ← hx,
          QuadraticMap.map_smul, smul_eq_mul]
        ring }
  have hsource : (Q.restrict (Submodule.span (ZMod 3) {a})).Nondegenerate :=
    he.nondegenerate_iff.mpr hP
  rw [quadSign_congr hsource ⟨he⟩, quadSign_eq_signOf P hP,
    TauCeti.formClass_presentedForm, signOf_mk_diag]
  simp [u]

theorem ff_invType_reflOf (hQ : Q.Nondegenerate) {a : V} (ha : Q a ≠ 0) :
    invType (reflOf Q a ha) = (1, toSign (Units.mk0 (Q a) ha)) := by
  have h1 : invDim (reflOf Q a ha) = 1 :=
    (congrArg (fun c : Submodule (ZMod 3) V => Module.finrank (ZMod 3) ↥c)
      (ff_commSp_reflOf hQ ha)).trans
      (finrank_span_singleton (fun h => ha (by rw [h, map_zero])))
  have h2 : invSign (reflOf Q a ha) = toSign (Units.mk0 (Q a) ha) :=
    (congrArg (fun c => quadSign (Q.restrict c)) (ff_commSp_reflOf hQ ha)).trans
      (ff_quadSign_span hQ ha)
  rw [invType, h1, h2]

theorem ff_polar_sub_sub (x₁ x₂ y₁ y₂ : V) :
    polar Q (x₁ - y₁) (x₂ - y₂) =
      polar Q x₁ x₂ - polar Q x₁ y₂ - polar Q y₁ x₂ + polar Q y₁ y₂ := by
  rw [QuadraticMap.polar_sub_left, QuadraticMap.polar_sub_right, QuadraticMap.polar_sub_right]
  ring

theorem ff_map_sub (x y : V) : Q (x - y) = Q x + Q y - polar Q x y := by
  rw [sub_eq_add_neg, CFSG.RankThree.OrthogonalInvolutions.map_add_eq Q,
    QuadraticMap.map_neg, QuadraticMap.polar_neg_right]
  ring

theorem ff_posKernel_singular {A : V ≃ₗ[ZMod 3] V} (hA : IsSimilitude Q A (-1))
    {x : V} (hx : x ∈ positiveSquareKernel A 1) : Q x = 0 := by
  have hAx : A x = (1 : ZMod 3) • x := by
    rw [positiveSquareKernel_eq A 1 one_ne_zero] at hx
    exact (Module.End.mem_eigenspace_iff).mp hx
  have h : Q x = -Q x := by
    have h1 := hA x
    rw [hAx, one_smul] at h1
    simpa only [Units.val_neg, Units.val_one, neg_one_mul] using h1
  have h2 : (2 : ZMod 3) * Q x = 0 := by rw [two_mul]; nth_rewrite 2 [h]; abel
  exact (mul_eq_zero.mp h2).resolve_left (by decide)

theorem ff_negKernel_singular {A : V ≃ₗ[ZMod 3] V} (hA : IsSimilitude Q A (-1))
    {y : V} (hy : y ∈ negativeSquareKernel A 1) : Q y = 0 := by
  have hAy : A y = -y := by
    rw [negativeSquareKernel_eq A 1 one_ne_zero] at hy
    have h := (Module.End.mem_eigenspace_iff).mp hy
    simpa using h
  have h : Q y = -Q y := by
    have h1 := hA y
    rw [hAy] at h1
    simpa only [QuadraticMap.map_neg, Units.val_neg, Units.val_one, neg_one_mul] using h1
  have h2 : (2 : ZMod 3) * Q y = 0 := by rw [two_mul]; nth_rewrite 2 [h]; abel
  exact (mul_eq_zero.mp h2).resolve_left (by decide)

theorem ff_posKernel_apply {A : V ≃ₗ[ZMod 3] V} {x : V}
    (hx : x ∈ positiveSquareKernel A 1) : A x = x := by
  have h := (Module.End.mem_eigenspace_iff).mp (by
    rwa [positiveSquareKernel_eq A 1 one_ne_zero] at hx)
  simpa using h

theorem ff_negKernel_apply {A : V ≃ₗ[ZMod 3] V} {y : V}
    (hy : y ∈ negativeSquareKernel A 1) : A y = -y := by
  have h := (Module.End.mem_eigenspace_iff).mp (by
    rwa [negativeSquareKernel_eq A 1 one_ne_zero] at hy)
  simpa using h

theorem ff_posKernel_polar {A : V ≃ₗ[ZMod 3] V} (hA : IsSimilitude Q A (-1)) {x z : V}
    (hx : x ∈ positiveSquareKernel A 1) (hz : z ∈ positiveSquareKernel A 1) :
    polar Q x z = 0 := by
  have h1 := CFSG.RankThree.OrthogonalInvolutions.map_add_eq Q x z
  rw [ff_posKernel_singular hA hx, ff_posKernel_singular hA hz, add_zero, zero_add] at h1
  have h2 := ff_posKernel_singular hA ((positiveSquareKernel A 1).add_mem hx hz)
  rw [h1] at h2
  exact h2

theorem ff_negKernel_polar {A : V ≃ₗ[ZMod 3] V} (hA : IsSimilitude Q A (-1)) {x z : V}
    (hx : x ∈ negativeSquareKernel A 1) (hz : z ∈ negativeSquareKernel A 1) :
    polar Q x z = 0 := by
  have h1 := CFSG.RankThree.OrthogonalInvolutions.map_add_eq Q x z
  rw [ff_negKernel_singular hA hx, ff_negKernel_singular hA hz, add_zero, zero_add] at h1
  have h2 := ff_negKernel_singular hA ((negativeSquareKernel A 1).add_mem hx hz)
  rw [h1] at h2
  exact h2

theorem ff_polar_add_add (x₁ x₂ y₁ y₂ : V) :
    polar Q (x₁ + y₁) (x₂ + y₂) =
      polar Q x₁ x₂ + polar Q x₁ y₂ + polar Q y₁ x₂ + polar Q y₁ y₂ := by
  rw [QuadraticMap.polar_add_left, QuadraticMap.polar_add_right, QuadraticMap.polar_add_right]
  ring

theorem ff_polar_sub_add (x₁ x₂ y₁ y₂ : V) :
    polar Q (x₁ - y₁) (x₂ + y₂) =
      polar Q x₁ x₂ + polar Q x₁ y₂ - polar Q y₁ x₂ - polar Q y₁ y₂ := by
  rw [sub_eq_add_neg, QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
    QuadraticMap.polar_add_right, QuadraticMap.polar_neg_left, QuadraticMap.polar_neg_left]
  ring

end CFSG.OddStandard.SmallF3.Omega
