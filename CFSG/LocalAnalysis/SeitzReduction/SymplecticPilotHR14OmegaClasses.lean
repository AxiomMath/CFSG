module

public import Mathlib.FieldTheory.Perfect
public import CFSG.ClassicalGroups.Orthogonal.Eichler

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

section CharTwo

theorem omegaInv_two_eq_zero [CharP K 2] : (2 : K) = 0 := CharTwo.two_eq_zero

variable (K) in
include K in
theorem omegaInv_add_self [CharP K 2] (x : V) : x + x = 0 := by
  rw [← two_smul K x, omegaInv_two_eq_zero, zero_smul]

variable (K) in
include K in
theorem omegaInv_neg_eq [CharP K 2] (x : V) : -x = x := by
  rw [neg_eq_iff_add_eq_zero, omegaInv_add_self K]

variable (K) in
include K in
theorem omegaInv_sub_eq_add [CharP K 2] (x y : V) : x - y = x + y := by
  rw [sub_eq_add_neg, omegaInv_neg_eq K]

end CharTwo

@[expose] def omegaInvNil (s : V ≃ₗ[K] V) : V →ₗ[K] V :=
  s.toLinearMap - LinearMap.id

theorem omegaInvNil_apply (s : V ≃ₗ[K] V) (x : V) : omegaInvNil s x = s x - x :=
  rfl

@[expose] def omegaInvSpace (s : V ≃ₗ[K] V) : Submodule K V :=
  LinearMap.range (omegaInvNil s)

theorem omegaInvNil_mem_omegaInvSpace (s : V ≃ₗ[K] V) (x : V) :
    omegaInvNil s x ∈ omegaInvSpace s :=
  LinearMap.mem_range_self _ x

theorem mem_omegaInvSpace_iff {s : V ≃ₗ[K] V} {w : V} :
    w ∈ omegaInvSpace s ↔ ∃ x, omegaInvNil s x = w :=
  LinearMap.mem_range

theorem omegaInvNil_eq_zero_iff_apply {s : V ≃ₗ[K] V} {x : V} :
    omegaInvNil s x = 0 ↔ s x = x := by
  rw [omegaInvNil_apply, sub_eq_zero]

theorem omegaInv_apply_apply_of_mul_self {s : V ≃ₗ[K] V} (hss : s * s = 1) (x : V) :
    s (s x) = x := by
  rw [← LinearEquiv.mul_apply, hss]
  rfl

section Involution

variable {s : V ≃ₗ[K] V}

theorem polar_omegaInvNil_left (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hss : s * s = 1) (x y : V) :
    polar Q (omegaInvNil s x) y = polar Q x (omegaInvNil s y) := by
  rw [omegaInvNil_apply, omegaInvNil_apply, polar_sub_left, polar_sub_right,
    ← polar_map_of_mem hs (s x) y, omegaInv_apply_apply_of_mul_self hss]

theorem omegaInvNil_omegaInvNil [CharP K 2] (hss : s * s = 1) (x : V) :
    omegaInvNil s (omegaInvNil s x) = 0 := by
  rw [omegaInvNil_apply, omegaInvNil_apply, map_sub, omegaInv_apply_apply_of_mul_self hss,
    show x - s x - (s x - x) = (x + x) - (s x + s x) by abel, omegaInv_add_self K,
    omegaInv_add_self K, sub_zero]

theorem apply_omegaInvNil [CharP K 2] (hss : s * s = 1) (x : V) :
    s (omegaInvNil s x) = omegaInvNil s x :=
  omegaInvNil_eq_zero_iff_apply.1 (omegaInvNil_omegaInvNil hss x)

theorem apply_of_mem_omegaInvSpace [CharP K 2] (hss : s * s = 1) {w : V}
    (hw : w ∈ omegaInvSpace s) : s w = w := by
  obtain ⟨x, rfl⟩ := mem_omegaInvSpace_iff.1 hw
  exact apply_omegaInvNil hss x

theorem omegaInvNil_of_mem_omegaInvSpace [CharP K 2] (hss : s * s = 1) {w : V}
    (hw : w ∈ omegaInvSpace s) : omegaInvNil s w = 0 :=
  omegaInvNil_eq_zero_iff_apply.2 (apply_of_mem_omegaInvSpace hss hw)

theorem polar_omegaInvNil_omegaInvNil [CharP K 2]
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hss : s * s = 1) (x y : V) :
    polar Q (omegaInvNil s x) (omegaInvNil s y) = 0 := by
  rw [polar_omegaInvNil_left hs hss, omegaInvNil_omegaInvNil hss, polar_zero_right]

theorem polar_of_mem_omegaInvSpace [CharP K 2]
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hss : s * s = 1) {v w : V}
    (hv : v ∈ omegaInvSpace s) (hw : w ∈ omegaInvSpace s) : polar Q v w = 0 := by
  obtain ⟨x, rfl⟩ := mem_omegaInvSpace_iff.1 hv
  obtain ⟨y, rfl⟩ := mem_omegaInvSpace_iff.1 hw
  exact polar_omegaInvNil_omegaInvNil hs hss x y

theorem map_omegaInvNil [CharP K 2] (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (x : V) : Q (omegaInvNil s x) = polar Q x (omegaInvNil s x) := by
  have h := map_of_mem hs x
  have hsx : s x = x + omegaInvNil s x := by
    rw [omegaInvNil_apply]
    abel
  rw [hsx, QuadraticMap.map_add Q] at h
  have h2 : (2 : K) = 0 := omegaInv_two_eq_zero
  linear_combination h - polar Q x (omegaInvNil s x) * h2

theorem map_omegaInvNil_add [CharP K 2] (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hss : s * s = 1) (x y : V) :
    Q (omegaInvNil s (x + y)) = Q (omegaInvNil s x) + Q (omegaInvNil s y) := by
  rw [map_add, QuadraticMap.map_add Q, polar_omegaInvNil_omegaInvNil hs hss, add_zero]

theorem omegaInvNil_eq_zero_iff (hQ : (polarBilin Q).Nondegenerate)
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hss : s * s = 1) {x : V} :
    omegaInvNil s x = 0 ↔ ∀ w ∈ omegaInvSpace s, polar Q x w = 0 := by
  constructor
  · intro hx w hw
    obtain ⟨y, rfl⟩ := mem_omegaInvSpace_iff.1 hw
    rw [← polar_omegaInvNil_left hs hss, hx, polar_zero_left]
  · intro h
    apply eq_zero_of_polar_eq_zero hQ
    intro y
    rw [polar_omegaInvNil_left hs hss]
    exact h _ (omegaInvNil_mem_omegaInvSpace s y)

theorem omegaInv_polarBilin_isRefl : (polarBilin Q).IsRefl := fun x y h => by
  rw [polarBilin_apply_apply] at h ⊢
  rw [polar_comm]
  exact h

theorem ker_omegaInvNil (hQ : (polarBilin Q).Nondegenerate)
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hss : s * s = 1) :
    LinearMap.ker (omegaInvNil s) =
      LinearMap.BilinForm.orthogonal (polarBilin Q) (omegaInvSpace s) := by
  ext x
  rw [LinearMap.mem_ker, omegaInvNil_eq_zero_iff hQ hs hss,
    LinearMap.BilinForm.mem_orthogonal_iff]
  refine forall₂_congr fun w _ => ?_
  rw [polarBilin_apply_apply, polar_comm]

theorem mem_omegaInvSpace_of_forall_polar [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hss : s * s = 1) {z : V} (hz : ∀ z', omegaInvNil s z' = 0 → polar Q z z' = 0) :
    z ∈ omegaInvSpace s := by
  rw [← LinearMap.BilinForm.orthogonal_orthogonal hQ omegaInv_polarBilin_isRefl (omegaInvSpace s),
    ← ker_omegaInvNil hQ hs hss, LinearMap.BilinForm.mem_orthogonal_iff]
  intro z' hz'
  rw [polarBilin_apply_apply, polar_comm]
  exact hz z' (LinearMap.mem_ker.1 hz')

end Involution

@[expose] def OmegaInvTypeB (Q : QuadraticForm K V) (s : V ≃ₗ[K] V) (l : ℕ) : Prop :=
  s ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧ s * s = 1 ∧
    finrank K (omegaInvSpace s) = l ∧ Odd l

@[expose] def omegaInvRadical (Q : QuadraticForm K V) (W : Submodule K V) :
    Subgroup (V ≃ₗ[K] V) where
  carrier := {g | g ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧ (∀ x, g x - x ∈ W) ∧
    ∀ x, (∀ w ∈ W, polar Q x w = 0) → g x = x}
  one_mem' := ⟨Subgroup.one_mem _, fun x => by simp, fun _ _ => rfl⟩
  mul_mem' := by
    rintro g g' ⟨hg, hgW, hgf⟩ ⟨hg', hg'W, hg'f⟩
    refine ⟨Subgroup.mul_mem _ hg hg', fun x => ?_, fun x hx => ?_⟩
    · rw [LinearEquiv.mul_apply, show g (g' x) - x = (g (g' x) - g' x) + (g' x - x) by abel]
      exact W.add_mem (hgW _) (hg'W _)
    · rw [LinearEquiv.mul_apply, hg'f x hx, hgf x hx]
  inv_mem' := by
    rintro g ⟨hg, hgW, hgf⟩
    refine ⟨Subgroup.inv_mem _ hg, fun x => ?_, fun x hx => ?_⟩
    · have h := hgW (g⁻¹ x)
      rw [LinearEquiv.apply_inv_apply'] at h
      rw [show g⁻¹ x - x = -(x - g⁻¹ x) by abel]
      exact W.neg_mem h
    · conv_lhs => rw [← hgf x hx]
      exact LinearEquiv.inv_apply_apply' g x

theorem eichler_mem_omegaInvRadical {W : Submodule K V} {u w : V} (hu : u ∈ W) (hw : w ∈ W) :
    eichler Q u w ∈ omegaInvRadical Q W := by
  refine ⟨eichler_mem_orthogonalGroup Q u w, fun x => ?_, fun x hx => ?_⟩
  · obtain ⟨a, b, h⟩ := eichler_apply_eq_add (Q := Q) u w x
    rw [h, show x + a • w + b • u - x = a • w + b • u by abel]
    exact W.add_mem (W.smul_mem a hw) (W.smul_mem b hu)
  · exact eichler_apply_of_polar_eq_zero (hx u hu) (hx w hw)

section Lambda

variable [Finite K] [CharP K 2]

@[expose] noncomputable def omegaInvLambda {s : V ≃ₗ[K] V}
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hss : s * s = 1) : V →ₗ[K] K where
  toFun x := (frobeniusEquiv K 2).symm (Q (omegaInvNil s x))
  map_add' x y := by
    rw [map_omegaInvNil_add hs hss, map_add]
  map_smul' c x := by
    rw [map_smul, QuadraticMap.map_smul, smul_eq_mul, smul_eq_mul, RingHom.id_apply, map_mul,
      ← _root_.sq, show c ^ 2 = frobenius K 2 c from rfl, frobeniusEquiv_symm_apply_frobenius]

theorem omegaInvLambda_apply {s : V ≃ₗ[K] V} (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hss : s * s = 1) (x : V) :
    omegaInvLambda hs hss x = (frobeniusEquiv K 2).symm (Q (omegaInvNil s x)) :=
  rfl

theorem omegaInvLambda_sq {s : V ≃ₗ[K] V} (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hss : s * s = 1) (x : V) : omegaInvLambda hs hss x ^ 2 = Q (omegaInvNil s x) := by
  rw [omegaInvLambda_apply, show ∀ a : K, a ^ 2 = frobenius K 2 a from fun a => rfl,
    frobenius_apply_frobeniusEquiv_symm]

end Lambda

end CFSG.SeitzReduction.SymplecticPilot
