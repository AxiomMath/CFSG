module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherInvolutionSplit

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Module

variable {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

section Ratio

variable {B : LinearMap.BilinForm K V} {A : Module.End K V} {d μ : K}

theorem multiplier_ratio [Nontrivial V] (hBnd : B.Nondegenerate) (hd : d ≠ 0)
    (hAA : A * A = d • 1) (hAμ : ∀ v w, B (A v) (A w) = μ * B v w) :
    μ / d = 1 ∨ μ / d = -1 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨w, hw⟩ : ∃ w, B v w ≠ 0 := by
    by_contra! h0
    exact hv (hBnd.1 v h0)
  have hA2 : ∀ u, A (A u) = d • u := fun u => by
    rw [← Module.End.mul_apply, hAA, LinearMap.smul_apply, Module.End.one_apply]
  have h1 := hAμ (A v) (A w)
  rw [hA2, hA2, hAμ] at h1
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h1
  have h2 : (μ / d) * (μ / d) = 1 := by
    field_simp
    have h3 : (d * d - μ * μ) * B v w = 0 := by linear_combination h1
    have h4 := (mul_eq_zero.mp h3).resolve_right hw
    linear_combination -h4
  exact mul_self_eq_one_iff.mp h2

theorem bilin_adjoint (hd : d ≠ 0) (hAA : A * A = d • 1) (hAμ : ∀ v w, B (A v) (A w) = μ * B v w)
    (v w : V) : B (A v) w = (μ / d) * B v (A w) := by
  have hw : w = A (d⁻¹ • A w) := by
    rw [map_smul, ← Module.End.mul_apply, hAA, LinearMap.smul_apply, Module.End.one_apply,
      smul_smul, inv_mul_cancel₀ hd, one_smul]
  conv_lhs => rw [hw]
  rw [hAμ, map_smul, smul_eq_mul, div_eq_mul_inv]
  ring

theorem bilin_invSMulOp {l : K} {B : LinearMap.BilinForm K V} {A : Module.End K V}
    {d μ : K} (hld : l ^ 2 = d) (hAμ : ∀ v w, B (A v) (A w) = μ * B v w) (v w : V) :
    B (invSMulOp l A v) (invSMulOp l A w) = (μ / d) * B v w := by
  change B ((l⁻¹ • A) v) ((l⁻¹ • A) w) = _
  simp only [LinearMap.smul_apply, map_smul, smul_eq_mul, hAμ, ← hld]
  rcases eq_or_ne l 0 with rfl | hl
  · simp
  · field_simp

end Ratio

section Eigen

variable {B : LinearMap.BilinForm K V}

theorem bilin_eq_zero_of_eigen_one (h2 : (2 : K) ≠ 0) {T : Module.End K V}
    (hT : ∀ v w, B (T v) (T w) = B v w) {v w : V} (hv : v ∈ LinearMap.ker (T - 1))
    (hw : w ∈ LinearMap.ker (T + 1)) : B v w = 0 := by
  have h1 := hT v w
  rw [apply_eq_of_mem_ker_sub_one hv, apply_eq_neg_of_mem_ker_add_one hw, map_neg] at h1
  have h3 : (2 : K) * B v w = 0 := by linear_combination -h1
  exact (mul_eq_zero.mp h3).resolve_left h2

theorem bilin_eq_zero_of_eigen_neg_plus (h2 : (2 : K) ≠ 0) {T : Module.End K V}
    (hT : ∀ v w, B (T v) (T w) = -B v w) {v w : V} (hv : v ∈ LinearMap.ker (T - 1))
    (hw : w ∈ LinearMap.ker (T - 1)) : B v w = 0 := by
  have h1 := hT v w
  rw [apply_eq_of_mem_ker_sub_one hv, apply_eq_of_mem_ker_sub_one hw] at h1
  have h3 : (2 : K) * B v w = 0 := by linear_combination h1
  exact (mul_eq_zero.mp h3).resolve_left h2

theorem bilin_eq_zero_of_eigen_neg_minus (h2 : (2 : K) ≠ 0) {T : Module.End K V}
    (hT : ∀ v w, B (T v) (T w) = -B v w) {v w : V} (hv : v ∈ LinearMap.ker (T + 1))
    (hw : w ∈ LinearMap.ker (T + 1)) : B v w = 0 := by
  have h1 := hT v w
  rw [apply_eq_neg_of_mem_ker_add_one hv, apply_eq_neg_of_mem_ker_add_one hw] at h1
  simp only [map_neg, LinearMap.neg_apply, neg_neg] at h1
  have h3 : (2 : K) * B v w = 0 := by linear_combination h1
  exact (mul_eq_zero.mp h3).resolve_left h2

theorem bilin_eq_zero_swap (hB : B.IsAlt) {v w : V} (h0 : B v w = 0) : B w v = 0 := by
  rw [← LinearMap.IsAlt.neg hB, h0, neg_zero]

end Eigen

section Restrict

@[expose] noncomputable def subgroupRestrictHom {C : Subgroup (LinearMap.GeneralLinearGroup K V)}
    (W : Submodule K V)
    (hW : ∀ g ∈ C, ∀ v ∈ W, ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v ∈ W) :
    C →* LinearMap.GeneralLinearGroup K W where
  toFun g := glRestrict W (g : LinearMap.GeneralLinearGroup K V) (hW g g.2) (hW _ (inv_mem g.2))
  map_one' := Units.ext (LinearMap.ext fun _ => rfl)
  map_mul' _ _ := Units.ext (LinearMap.ext fun _ => rfl)

theorem coe_subgroupRestrictHom_apply {C : Subgroup (LinearMap.GeneralLinearGroup K V)}
    (W : Submodule K V)
    (hW : ∀ g ∈ C, ∀ v ∈ W, ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v ∈ W)
    (g : C) (v : W) :
    ((((subgroupRestrictHom W hW g : LinearMap.GeneralLinearGroup K W) : Module.End K W) v : W) :
      V) = ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v :=
  rfl

abbrev similitudeCentralizer (B : LinearMap.BilinForm K V) (A : LinearMap.GeneralLinearGroup K V) :
    Subgroup (LinearMap.GeneralLinearGroup K V) :=
  sesqUnitaryGroup B ⊓ Subgroup.centralizer {A}

theorem commute_of_mem_similitudeCentralizer {B : LinearMap.BilinForm K V}
    {A g : LinearMap.GeneralLinearGroup K V} (hg : g ∈ similitudeCentralizer B A) :
    (g : Module.End K V) * (A : Module.End K V) = (A : Module.End K V) * (g : Module.End K V) :=
  congrArg (fun x : LinearMap.GeneralLinearGroup K V => (x : Module.End K V))
    (Subgroup.mem_centralizer_singleton_iff.mp hg.2)

theorem mapsTo_eigenPlus_of_mem {B : LinearMap.BilinForm K V}
    {A g : LinearMap.GeneralLinearGroup K V} (l : K) (hg : g ∈ similitudeCentralizer B A)
    {v : V} (hv : v ∈ eigenPlus l (A : Module.End K V)) :
    (g : Module.End K V) v ∈ eigenPlus l (A : Module.End K V) := by
  have e : invSMulOp l (A : Module.End K V) - 1 =
      invSMulOp l (A : Module.End K V) - (1 : K) • (1 : Module.End K V) := by rw [one_smul]
  change v ∈ LinearMap.ker (invSMulOp l (A : Module.End K V) - 1) at hv
  change (g : Module.End K V) v ∈ LinearMap.ker (invSMulOp l (A : Module.End K V) - 1)
  rw [e] at hv ⊢
  exact mapsTo_eigen_of_commute (commute_of_mem_similitudeCentralizer hg) hv

theorem mapsTo_eigenMinus_of_mem {B : LinearMap.BilinForm K V}
    {A g : LinearMap.GeneralLinearGroup K V} (l : K) (hg : g ∈ similitudeCentralizer B A)
    {v : V} (hv : v ∈ eigenMinus l (A : Module.End K V)) :
    (g : Module.End K V) v ∈ eigenMinus l (A : Module.End K V) := by
  have e : invSMulOp l (A : Module.End K V) + 1 =
      invSMulOp l (A : Module.End K V) - (-1 : K) • (1 : Module.End K V) := by
    rw [neg_smul, one_smul, sub_neg_eq_add]
  change v ∈ LinearMap.ker (invSMulOp l (A : Module.End K V) + 1) at hv
  change (g : Module.End K V) v ∈ LinearMap.ker (invSMulOp l (A : Module.End K V) + 1)
  rw [e] at hv ⊢
  exact mapsTo_eigen_of_commute (commute_of_mem_similitudeCentralizer hg) hv

end Restrict

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
