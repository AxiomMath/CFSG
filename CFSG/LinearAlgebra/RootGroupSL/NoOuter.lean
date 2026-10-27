module

public import CFSG.LinearAlgebra.RootGroupSL.NoOuterGraph
public import CFSG.LinearAlgebra.RootGroupSL.NoOuterField
public import CFSG.LinearAlgebra.RootGroupSL.AutAbs
import CFSG.LinearAlgebra.RootGroupSL.SchurSL

public section

namespace CFSG.LinearAlgebra.RootGroupSL

variable {k E X : Type} [Field k] [Field E] [Algebra k E] [AddCommGroup X] [Module k X]
  [Finite k] [Finite E] [Module.Finite k X] [CharP k 2]

private lemma iterate_sq_eq_pow {K : Type} [CommRing K] (m : ℕ) (x : K) :
    ((fun y : K => y ^ 2)^[m]) x = x ^ (2 ^ m) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply', ih, ← pow_mul, pow_succ]

private lemma pow_two_pow_injective {K : Type} [Field K] [CharP K 2] (m : ℕ) :
    Function.Injective (fun x : K => x ^ (2 ^ m)) := by
  have hsq : Function.Injective (fun x : K => x ^ 2) := CharTwo.sq_injective
  have h := hsq.iterate m
  have hfun : (fun x : K => x ^ 2)^[m] = fun x : K => x ^ (2 ^ m) :=
    funext (iterate_sq_eq_pow m)
  rwa [hfun] at h

private lemma det_smulOfUnit_eq {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (u : Kˣ) :
    LinearEquiv.det (LinearEquiv.smulOfUnit u : V ≃ₗ[K] V) = u ^ Module.finrank K V := by
  apply Units.ext
  rw [LinearEquiv.coe_det, Units.val_pow_eq_pow_val]
  have h : ((LinearEquiv.smulOfUnit u : V ≃ₗ[K] V) : V →ₗ[K] V) =
      (u : K) • (1 : V →ₗ[K] V) := by
    ext x
    rfl
  rw [h, LinearMap.det_smul, map_one, mul_one]

private lemma det_smul_linearEquiv {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (a : Kˣ) (f : V ≃ₗ[K] V) :
    LinearEquiv.det (a • f) = a ^ Module.finrank K V * LinearEquiv.det f := by
  apply Units.ext
  rw [LinearEquiv.coe_det, Units.val_mul, Units.val_pow_eq_pow_val]
  have h : ((a • f : V ≃ₗ[K] V) : V →ₗ[K] V) = (a : K) • (f : V →ₗ[K] V) := rfl
  rw [h, LinearMap.det_smul, LinearEquiv.coe_det]

private lemma smul_conj {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (a : Kˣ) (f h : V ≃ₗ[K] V) :
    (a • f) * h * (a • f)⁻¹ = f * h * f⁻¹ := by
  ext x
  change (a • f) (h ((a • f)⁻¹ x)) = f (h (f⁻¹ x))
  simp only [LinearEquiv.coe_inv, LinearEquiv.symm_smul, LinearEquiv.smul_apply, map_smul]
  rw [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]

theorem exists_conj_of_linear_form {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (α : MulAut (SpecialLinearGroup k V)) (T : V ≃+ V)
    (hT : ∀ (c : k) (v : V), T (c • v) = c • T v)
    (hα : ∀ (g : SpecialLinearGroup k V) (v : V), α g (T v) = T (g v))
    (h2 : ∃ m : ℕ, α ^ (2 ^ m) = 1) : ∃ g : SpecialLinearGroup k V, α = MulAut.conj g := by
  classical
  by_cases hn : Module.finrank k V ≤ 1
  ·
    haveI : Subsingleton (SpecialLinearGroup k V) := by
      rcases Nat.eq_zero_or_pos (Module.finrank k V) with h0 | hpos
      · have hsub : Subsingleton V := Module.finrank_zero_iff.mp h0
        exact ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
      · have h1 : Module.finrank k V = 1 := by omega
        exact SpecialLinearGroup.subsingleton_of_finrank_eq_one (R := k) (V := V) h1
    refine ⟨1, MulEquiv.ext fun g => ?_⟩
    rw [MulAut.conj_apply, one_mul, inv_one, mul_one]
    exact Subsingleton.elim _ _
  · push Not at hn
    have hV : 2 ≤ Module.finrank k V := by omega
    obtain ⟨m, hm⟩ := h2
    let T' : V ≃ₗ[k] V :=
      { toFun := T
        invFun := T.symm
        left_inv := T.left_inv
        right_inv := T.right_inv
        map_add' := T.map_add
        map_smul' := hT }
    have hα' : ∀ (g : SpecialLinearGroup k V) (v : V), α g (T' v) = T' (g v) :=
      fun g v => hα g v
    have hiter : ∀ j : ℕ, ∀ (g : SpecialLinearGroup k V) (v : V),
        (α ^ j) g ((T' ^ j) v) = (T' ^ j) (g v) := by
      intro j
      induction j with
      | zero => intro g v; simp
      | succ j ih =>
          intro g v
          rw [pow_succ', pow_succ', MulAut.mul_apply, LinearEquiv.mul_apply,
            LinearEquiv.mul_apply, hα' ((α ^ j) g) ((T' ^ j) v), ih g v]
    let S : V →+ V := (T' ^ (2 ^ m)).toAddEquiv.toAddMonoidHom
    have hS_apply : ∀ v : V, S v = (T' ^ (2 ^ m)) v := fun v => rfl
    have hS_comm : ∀ (g : SpecialLinearGroup k V) (v : V), S (g v) = g (S v) := by
      intro g v
      have h := hiter (2 ^ m) g v
      simp only [hm, MulAut.one_apply] at h
      rw [hS_apply, hS_apply]
      exact h.symm
    obtain ⟨c, hc⟩ := exists_smul_of_commute_specialLinear (F := k) (V := V) hV S hS_comm
    obtain ⟨v0, hv0⟩ :=
      Module.finrank_pos_iff_exists_ne_zero.mp (by omega : 0 < Module.finrank k V)
    have hc0 : c ≠ 0 := by
      intro hc_eq
      have hzero : S v0 = 0 := by rw [hc v0, hc_eq, zero_smul]
      have hS0 : S 0 = 0 := map_zero S
      have hinj : Function.Injective S := fun a b hab => (T' ^ (2 ^ m)).injective hab
      exact hv0 (hinj (hzero.trans hS0.symm))
    let u : kˣ := Units.mk0 c hc0
    have hS_eq : T' ^ (2 ^ m) = LinearEquiv.smulOfUnit u := by
      ext v
      rw [← hS_apply v, hc v]
      rfl
    have hdet : (LinearEquiv.det T') ^ (2 ^ m) = u ^ Module.finrank k V := by
      rw [← map_pow (LinearEquiv.det) T' (2 ^ m), hS_eq, det_smulOfUnit_eq]
    have hpow_inj : Function.Injective (fun x : k => x ^ (2 ^ m)) := pow_two_pow_injective m
    have hpow_surj : Function.Surjective (fun x : k => x ^ (2 ^ m)) :=
      Finite.injective_iff_surjective.mp hpow_inj
    obtain ⟨mu0, hmu0⟩ := hpow_surj (u : k)
    have hmu0_ne : mu0 ≠ 0 := by
      intro h0
      have hzero : (0 : k) = (u : k) := by
        have h1 : mu0 ^ (2 ^ m) = (u : k) := hmu0
        rw [h0, zero_pow (pow_ne_zero m (by norm_num : (2 : ℕ) ≠ 0))] at h1
        exact h1
      exact Units.ne_zero u hzero.symm
    let mu : kˣ := Units.mk0 mu0 hmu0_ne
    have hmu : mu ^ (2 ^ m) = u := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val]
      exact hmu0
    have hpow_inj_units : Function.Injective (fun x : kˣ => x ^ (2 ^ m)) := by
      intro x y hxy
      apply Units.ext
      apply hpow_inj
      have hval := congrArg (fun z : kˣ => (z : k)) hxy
      simpa [Units.val_pow_eq_pow_val] using hval
    have hmu_pow : (mu ^ Module.finrank k V) ^ (2 ^ m) =
        (LinearEquiv.det T') ^ (2 ^ m) := by
      rw [← pow_mul, Nat.mul_comm (Module.finrank k V) (2 ^ m), pow_mul, hmu, hdet]
    have hmun_eq : mu ^ Module.finrank k V = LinearEquiv.det T' := hpow_inj_units hmu_pow
    have hdet_g : LinearEquiv.det ((mu⁻¹) • T') = 1 := by
      rw [det_smul_linearEquiv, ← hmun_eq, inv_pow, inv_mul_cancel]
    let g : SpecialLinearGroup k V := ⟨(mu⁻¹) • T', hdet_g⟩
    have hαφ : ∀ h : SpecialLinearGroup k V,
        (α h : V ≃ₗ[k] V) = T' * (h : V ≃ₗ[k] V) * T'⁻¹ := by
      intro h
      apply LinearEquiv.ext
      intro w
      calc ((α h : V ≃ₗ[k] V)) w
          = ((α h : V ≃ₗ[k] V)) (T' (T'.symm w)) := by
            rw [LinearEquiv.apply_symm_apply T' w]
        _ = T' ((h : V ≃ₗ[k] V) (T'.symm w)) := hα' h (T'.symm w)
        _ = (T' * (h : V ≃ₗ[k] V) * T'⁻¹) w := by
            rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.coe_inv]
    have hconj : ∀ h : SpecialLinearGroup k V,
        (MulAut.conj g h : V ≃ₗ[k] V) = T' * (h : V ≃ₗ[k] V) * T'⁻¹ := by
      intro h
      rw [MulAut.conj_apply, SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul,
        SpecialLinearGroup.coe_inv]
      rw [show (g : V ≃ₗ[k] V) = (mu⁻¹) • T' from rfl, smul_conj]
    exact ⟨g, MulEquiv.ext fun h => Subtype.ext ((hαφ h).trans (hconj h).symm)⟩

theorem exists_conj_of_two_element_mem_Y
    (hdX : Module.finrank k E ≤ Module.finrank k X)
    (hstar : 2 ≤ Module.finrank k E ∨
      (Module.finrank k E = 1 ∧ 4 ≤ Nat.card k ∧ 2 ≤ Module.finrank k X))
    (α : MulAut (SpecialLinearGroup k (DSpace E X)))
    (hR : (rootSL k E X).map α.toMonoidHom = rootSL k E X)
    (hC : ∀ h ∈ Subgroup.normalizer (rootSL k E X : Set (SpecialLinearGroup k (DSpace E X))),
      α h * h⁻¹ ∈ QK k E X ⊔ Subgroup.center (SpecialLinearGroup k (DSpace E X)))
    (h2 : ∃ m : ℕ, α ^ (2 ^ m) = 1) :
    ∃ g : SpecialLinearGroup k (DSpace E X), α = MulAut.conj g := by
  classical
  haveI : Module.Finite k E := Module.Finite.of_finite
  have hEpos : 0 < Module.finrank k E := by
    rw [Module.finrank_pos_iff_exists_ne_zero]
    exact ⟨1, one_ne_zero⟩
  have hX : 0 < Module.finrank k X := lt_of_lt_of_le hEpos hdX
  have hfin : Module.finrank k (DSpace E X) =
      Module.finrank k E + Module.finrank k X + Module.finrank k E := by
    rw [Module.finrank_prod, Module.finrank_prod, add_assoc]
  have hV : 3 ≤ Module.finrank k (DSpace E X) := by
    rw [hfin]
    rcases hstar with hd | ⟨hd, _hk, hX2⟩ <;> omega
  obtain ⟨σ, hform⟩ := exists_semilinear_form_of_mulAut_sl (F := k) (V := DSpace E X) hV α
  rcases hform with ⟨T, hT, hα⟩ | ⟨T, hT, hα⟩
  ·
    have hσ : σ = RingEquiv.refl k := field_form_eq_refl hX α hR hC σ T hT hα
    have hTlin : ∀ (c : k) (v : DSpace E X), T (c • v) = c • T v := by
      intro c v
      rw [hT c v, hσ]
      rfl
    exact exists_conj_of_linear_form α T hTlin hα h2
  ·
    exact False.elim (false_of_graph_form hstar α hR hC σ T hT hα)

end CFSG.LinearAlgebra.RootGroupSL
