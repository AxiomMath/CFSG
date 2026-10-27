module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.PieceAction
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.LinearAlgebra.Center
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open Module

section PartA

variable {K : Type*} [Field K] [CharP K 2] {Y : Type*} [AddCommGroup Y] [Module K Y]

theorem eq_one_of_mul_eq_smul_mul (hY : finrank K Y = 2) (E X : LinearMap.GeneralLinearGroup K Y)
    {c : K} (h : (E : Module.End K Y) * X = c • ((X : Module.End K Y) * E)) : c = 1 := by
  have hE : IsUnit (LinearMap.det (E : Module.End K Y)) := (Units.isUnit E).map LinearMap.det
  have hX : IsUnit (LinearMap.det (X : Module.End K Y)) := (Units.isUnit X).map LinearMap.det
  have h1 := congrArg LinearMap.det h
  rw [map_mul, LinearMap.det_smul, map_mul, hY] at h1
  have hne : LinearMap.det (E : Module.End K Y) * LinearMap.det (X : Module.End K Y) ≠ 0 :=
    (hE.mul hX).ne_zero
  have h2 : c ^ 2 = 1 := by
    have : c ^ 2 * (LinearMap.det (E : Module.End K Y) * LinearMap.det (X : Module.End K Y)) =
        1 * (LinearMap.det (E : Module.End K Y) * LinearMap.det (X : Module.End K Y)) := by
      rw [one_mul, mul_comm (LinearMap.det (E : Module.End K Y)), ← h1]
      ring
    exact mul_right_cancel₀ hne this
  have h3 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h4 : (c - 1) ^ 2 = 0 := by linear_combination h2 + (1 - c) * h3
  exact sub_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp h4)

omit [CharP K 2] in
theorem exists_span_pair_eq_top (hY : finrank K Y = 2) (X : Module.End K Y)
    (hX : ∀ c : K, X ≠ c • 1) : ∃ v : Y, Submodule.span K {v, X v} = ⊤ := by
  have : FiniteDimensional K Y := Module.finite_of_finrank_pos (by omega)
  by_contra hcon
  obtain ⟨a, ha⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent (f := X) (by
    intro v hv
    refine hcon ⟨v, ?_⟩
    have h := hv.span_eq_top_of_card_eq_finrank' (by simp [hY])
    simpa [Matrix.range_cons, Set.pair_comm] using h)
  exact hX a ha

omit [CharP K 2] in
theorem eq_add_smul_of_mul_eq (hY : finrank K Y = 2) {X : Module.End K Y}
    (hX : ∀ c : K, X ≠ c • 1) {M : Module.End K Y} (h : M * X = X * M) :
    ∃ a b : K, M = a • 1 + b • X := by
  obtain ⟨v, hv⟩ := exists_span_pair_eq_top hY X hX
  have hmem : M v ∈ Submodule.span K {v, X v} := hv ▸ Submodule.mem_top
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hmem
  refine ⟨a, b, LinearMap.ext_on hv ?_⟩
  intro y hy
  have hc : M (X v) = X (M v) := congrArg (fun T => T v) h
  rcases hy with rfl | hy
  · simp [← hab]
  · rw [Set.mem_singleton_iff] at hy
    subst hy
    simp [hc, ← hab]

theorem scalar_of_commute_up_to_scalar (hY : finrank K Y = 2)
    {X E A B : LinearMap.GeneralLinearGroup K Y}
    (hX : ∀ c : K, (X : Module.End K Y) ≠ c • 1)
    (hEX : ∃ c : K, (E : Module.End K Y) * X = c • ((X : Module.End K Y) * E))
    (hEA : ∃ c : K, (E : Module.End K Y) * A = c • ((A : Module.End K Y) * E))
    (hEB : ∃ c : K, (E : Module.End K Y) * B = c • ((B : Module.End K Y) * E))
    (hAB : (A : Module.End K Y) * B ≠ (B : Module.End K Y) * A) :
    ∃ c : K, (E : Module.End K Y) = c • 1 := by
  obtain ⟨c1, h1⟩ := hEX
  obtain ⟨c2, h2⟩ := hEA
  obtain ⟨c3, h3⟩ := hEB
  have e1 := eq_one_of_mul_eq_smul_mul hY E X h1
  have e2 := eq_one_of_mul_eq_smul_mul hY E A h2
  have e3 := eq_one_of_mul_eq_smul_mul hY E B h3
  subst e1 e2 e3
  simp only [one_smul] at h1 h2 h3
  obtain ⟨a, b, hE⟩ := eq_add_smul_of_mul_eq hY hX h1
  by_cases hb : b = 0
  · exact ⟨a, by simp [hE, hb]⟩
  · exfalso
    have key : ∀ T : Module.End K Y, E * T = T * E → T * X = X * T := by
      intro T hT
      rw [hE] at hT
      simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, one_mul, mul_one] at hT
      have hT' : b • (X * T) = b • (T * X) := by
        have := add_left_cancel (a := a • T) (by simpa [add_comm] using hT)
        exact this
      exact (smul_right_injective _ hb hT').symm
    obtain ⟨a1, b1, hA⟩ := eq_add_smul_of_mul_eq hY hX (key A h2)
    obtain ⟨a2, b2, hB⟩ := eq_add_smul_of_mul_eq hY hX (key B h3)
    apply hAB
    rw [hA, hB]
    simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, one_mul, mul_one]
    module

end PartA

section PartB

variable {K : Type*} [Field K] [CharP K 2] {V : Type*} [AddCommGroup V] [Module K V]

theorem quotGL_scalar_of_commutators_scalar {F F' : Submodule K V}
    (hdim : finrank K (PieceQ F F') = 2) {Δ : Subgroup (LinearMap.GeneralLinearGroup K V)}
    (hΔ : Δ ≤ stabPair F F') (hperf : ⁅Δ, Δ⁆ = Δ) {x : LinearMap.GeneralLinearGroup K V}
    (hx : x ∈ Δ)
    (hxs : ∀ c : K, ((quotGL F F' ⟨x, hΔ hx⟩ : LinearMap.GeneralLinearGroup K (PieceQ F F')) :
      Module.End K (PieceQ F F')) ≠ c • 1)
    {e : LinearMap.GeneralLinearGroup K V} (he : e ∈ stabPair F F')
    (hec : ∀ d ∈ Δ, ∃ c : K,
      ((e * d * e⁻¹ * d⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) = c • 1) :
    ∃ c : K, ((quotGL F F' ⟨e, he⟩ : LinearMap.GeneralLinearGroup K (PieceQ F F')) :
      Module.End K (PieceQ F F')) = c • 1 := by
  have hcomm : ∀ (d : LinearMap.GeneralLinearGroup K V) (hd : d ∈ Δ), ∃ c : K,
      ((quotGL F F' ⟨e, he⟩ : LinearMap.GeneralLinearGroup K (PieceQ F F')) :
        Module.End K (PieceQ F F')) *
        (quotGL F F' ⟨d, hΔ hd⟩ : LinearMap.GeneralLinearGroup K (PieceQ F F')) =
      c • ((quotGL F F' ⟨d, hΔ hd⟩ : LinearMap.GeneralLinearGroup K (PieceQ F F')) *
        (quotGL F F' ⟨e, he⟩ : LinearMap.GeneralLinearGroup K (PieceQ F F'))) := by
    intro d hd
    obtain ⟨c, hc⟩ := hec d hd
    refine ⟨c, ?_⟩
    have hV : ((e * d : LinearMap.GeneralLinearGroup K V) : Module.End K V) =
        c • ((d * e : LinearMap.GeneralLinearGroup K V) : Module.End K V) := by
      calc ((e * d : LinearMap.GeneralLinearGroup K V) : Module.End K V)
          = ((e * d * e⁻¹ * d⁻¹ * (d * e) : LinearMap.GeneralLinearGroup K V) :
              Module.End K V) := by congr 1; group
        _ = _ := by rw [Units.val_mul, hc, smul_mul_assoc, one_mul]
    refine LinearMap.ext fun q => ?_
    induction q using Submodule.Quotient.induction_on with
    | H v =>
      simp only [coe_quotGL, Module.End.mul_apply, quotEnd_mk, LinearMap.smul_apply]
      rw [← Submodule.Quotient.mk_smul]
      congr 1
      refine Subtype.ext ?_
      exact congrArg (fun T => T (v : V)) hV
  let φ : Δ →* LinearMap.GeneralLinearGroup K (PieceQ F F') :=
    (quotGL F F').comp (Subgroup.inclusion hΔ)
  have hnc : ∃ d₁ d₂ : Δ, ((φ d₁ : LinearMap.GeneralLinearGroup K (PieceQ F F')) :
      Module.End K (PieceQ F F')) * (φ d₂ : Module.End K (PieceQ F F')) ≠
      (φ d₂ : Module.End K (PieceQ F F')) * (φ d₁ : Module.End K (PieceQ F F')) := by
    by_contra hall
    push Not at hall
    have hP : (⁅(⊤ : Subgroup Δ), ⊤⁆ : Subgroup Δ) = ⊤ := by
      rw [← commutator_def]
      exact Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr hperf)
    have hker : (⊤ : Subgroup Δ) ≤ φ.ker := by
      rw [← hP, Subgroup.commutator_le]
      intro g₁ _ g₂ _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
      exact Units.ext (by simpa [Units.val_mul] using hall g₁ g₂)
    have h1 : φ ⟨x, hx⟩ = 1 := hker (Subgroup.mem_top _)
    refine hxs 1 ?_
    rw [one_smul]
    exact congrArg Units.val h1
  obtain ⟨d₁, d₂, hd⟩ := hnc
  exact scalar_of_commute_up_to_scalar hdim hxs (hcomm x hx) (hcomm d₁.1 d₁.2)
    (hcomm d₂.1 d₂.2) hd

end PartB

end CFSG.HardMathSupport.Curtis.UnitaryLevi
