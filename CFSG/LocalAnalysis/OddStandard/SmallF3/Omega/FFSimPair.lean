module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Sim
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2GenInr
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFSimOrth

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ff_reflPair_apply {u v : V} (hu : Q u ≠ 0) (hv : Q v ≠ 0) (huv : polar Q u v = 0)
    (x : V) :
    (((reflOf Q u hu * reflOf Q v hv : OGroup Q)) : V ≃ₗ[ZMod 3] V) x =
      x - (polar Q u x / Q u) • u - (polar Q v x / Q v) • v := by
  rw [Subgroup.coe_mul, LinearEquiv.mul_apply]
  rw [coe_reflOf_apply v hv, coe_reflOf_apply u hu]
  have hpol : QuadraticMap.polar Q u (x - (polar Q v x / Q v) • v) =
      QuadraticMap.polar Q u x := by
    rw [QuadraticMap.polar_sub_right, QuadraticMap.polar_smul_right, huv, smul_zero, sub_zero]
  rw [hpol]
  abel

theorem ff_mem_span_of_reflPair_apply_eq_neg {u v : V} (hu : Q u ≠ 0) (hv : Q v ≠ 0)
    (huv : polar Q u v = 0) {x : V}
    (hx : (((reflOf Q u hu * reflOf Q v hv : OGroup Q)) : V ≃ₗ[ZMod 3] V) x = -x) :
    x ∈ Submodule.span (ZMod 3) {u, v} := by
  have hx' : x - (polar Q u x / Q u) • u - (polar Q v x / Q v) • v = -x := by
    rw [← ff_reflPair_apply hu hv huv x]; exact hx
  have h' : x = -x + ((polar Q u x / Q u) • u + (polar Q v x / Q v) • v) := by
    rw [sub_sub, sub_eq_iff_eq_add] at hx'
    exact hx'
  have hsum : (2 : ZMod 3) • x =
      (polar Q u x / Q u) • u + (polar Q v x / Q v) • v := by
    have h2 : (2 : ZMod 3) • x = x + x := by
      rw [show (2 : ZMod 3) = 1 + 1 by decide, add_smul, one_smul]
    rw [h2]
    nth_rewrite 1 [h']
    abel
  have hx2 : x = (2 : ZMod 3) •
      ((polar Q u x / Q u) • u + (polar Q v x / Q v) • v) := by
    rw [← hsum, smul_smul, show (2 : ZMod 3) * 2 = 1 by decide, one_smul]
  refine Submodule.mem_span_pair.mpr
    ⟨(2 : ZMod 3) * (polar Q u x / Q u), (2 : ZMod 3) * (polar Q v x / Q v), ?_⟩
  conv_rhs => rw [hx2]
  rw [smul_add, smul_smul, smul_smul]

theorem ff_simAct_pair (hQ : Q.Nondegenerate) (h5 : 5 ≤ Module.finrank (ZMod 3) V)
    (γ : simGroup Q)
    (hγ : ∀ t ∈ omegaGroup hQ, simAct Q γ t = t ∨ simAct Q γ t = piOrth Q * t)
    {u v : V} (hu : Q u ≠ 0) (hv : Q v = Q u) (huv : polar Q u v = 0) :
    (γ : V ≃ₗ[ZMod 3] V) u ∈ Submodule.span (ZMod 3) {u, v} := by
  have hv' : Q v ≠ 0 := by rw [hv]; exact hu
  set t : OGroup Q := reflOf Q u hu * reflOf Q v hv' with ht_def
  have ht : t ∈ omegaGroup hQ := by
    rw [ht_def]
    exact reflOf_mul_reflOf_mem_omegaGroup hQ u v hu hv' hv.symm
  have htu : (t : V ≃ₗ[ZMod 3] V) u = -u := by
    rw [ht_def, ff_reflPair_apply hu hv' huv u]
    rw [QuadraticMap.polar_self, QuadraticMap.polar_comm, huv, zero_div, zero_smul, sub_zero]
    have hcoef : (2 : ℕ) • Q u / Q u = 2 := by
      rw [← Nat.cast_smul_eq_nsmul (R := ZMod 3) 2 (Q u), smul_eq_mul,
        mul_div_cancel_right₀ _ hu]
      norm_num
    rw [hcoef]
    have h2u : (2 : ZMod 3) • u = -u := by
      rw [show (2 : ZMod 3) = -1 by decide, neg_one_smul]
    have h2u' : (2 : ZMod 3) • u = u + u := by
      rw [show (2 : ZMod 3) = 1 + 1 by decide, add_smul, one_smul]
    have huu : u + u = -u := by
      rw [← h2u']; exact h2u
    rw [h2u, sub_neg_eq_add]
    exact huu
  rcases hγ t ht with hcase | hcase
  · have hconj : (γ : V ≃ₗ[ZMod 3] V) * (t : V ≃ₗ[ZMod 3] V) *
        (γ : V ≃ₗ[ZMod 3] V)⁻¹ = (t : V ≃ₗ[ZMod 3] V) := by
      have h := congrArg (fun s : OGroup Q => (s : V ≃ₗ[ZMod 3] V)) hcase
      rwa [coe_simAct] at h
    have hcomm : (γ : V ≃ₗ[ZMod 3] V) * (t : V ≃ₗ[ZMod 3] V) =
        (t : V ≃ₗ[ZMod 3] V) * (γ : V ≃ₗ[ZMod 3] V) := by
      have h := congrArg (· * (γ : V ≃ₗ[ZMod 3] V)) hconj
      rw [mul_assoc, inv_mul_cancel, mul_one] at h
      exact h
    have happ : (t : V ≃ₗ[ZMod 3] V) ((γ : V ≃ₗ[ZMod 3] V) u) =
        (γ : V ≃ₗ[ZMod 3] V) ((t : V ≃ₗ[ZMod 3] V) u) := by
      have h := congrArg (fun e : V ≃ₗ[ZMod 3] V => e u) hcomm
      simpa [LinearEquiv.mul_apply] using h.symm
    have hx : (t : V ≃ₗ[ZMod 3] V) ((γ : V ≃ₗ[ZMod 3] V) u) =
        -((γ : V ≃ₗ[ZMod 3] V) u) := by
      rw [happ, htu, map_neg]
    refine ff_mem_span_of_reflPair_apply_eq_neg hu hv' huv ?_
    rw [← ht_def]
    exact hx
  · have hconj : (γ : V ≃ₗ[ZMod 3] V) * (t : V ≃ₗ[ZMod 3] V) *
        (γ : V ≃ₗ[ZMod 3] V)⁻¹ =
        (piOrth Q : V ≃ₗ[ZMod 3] V) * (t : V ≃ₗ[ZMod 3] V) := by
      have h := congrArg (fun s : OGroup Q => (s : V ≃ₗ[ZMod 3] V)) hcase
      rwa [coe_simAct, Subgroup.coe_mul] at h
    have hpoint : ∀ y : V,
        (γ : V ≃ₗ[ZMod 3] V) ((t : V ≃ₗ[ZMod 3] V) ((γ : V ≃ₗ[ZMod 3] V)⁻¹ y)) =
          -((t : V ≃ₗ[ZMod 3] V) y) := by
      intro y
      have h := congrArg (fun e : V ≃ₗ[ZMod 3] V => e y) hconj
      simpa [LinearEquiv.mul_apply, coe_piOrth_apply] using h
    let P : Submodule (ZMod 3) V := Submodule.span (ZMod 3) {u, v}
    let Porth : Submodule (ZMod 3) V := LinearMap.BilinForm.orthogonal Q.polarBilin P
    have hmem : ∀ x ∈ Porth, (γ : V ≃ₗ[ZMod 3] V) x ∈ P := by
      intro x hxP
      have hxpair : polar Q u x = 0 ∧ polar Q v x = 0 :=
        (ff_mem_orth_pair_iff (u := u) (v := v) (w := x)).mp hxP
      have htx : (t : V ≃ₗ[ZMod 3] V) x = x := by
        rw [ht_def, ff_reflPair_apply hu hv' huv x, hxpair.1, hxpair.2]
        simp
      have h1 := hpoint ((γ : V ≃ₗ[ZMod 3] V) x)
      rw [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply] at h1
      rw [htx] at h1
      have hneg : (t : V ≃ₗ[ZMod 3] V) ((γ : V ≃ₗ[ZMod 3] V) x) =
          -((γ : V ≃ₗ[ZMod 3] V) x) := by
        have h := congrArg Neg.neg h1
        simpa using h.symm
      exact ff_mem_span_of_reflPair_apply_eq_neg hu hv' huv hneg
    let φ : Porth →ₗ[ZMod 3] P :=
      ((γ : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V).restrict hmem
    have hφinj : Function.Injective φ := by
      intro a b hab
      apply Subtype.ext
      have hcoe : (γ : V ≃ₗ[ZMod 3] V) (a : V) = (γ : V ≃ₗ[ZMod 3] V) (b : V) := by
        have h := congrArg (fun z : P => (z : V)) hab
        simpa [φ, LinearMap.coe_restrict_apply] using h
      exact (γ : V ≃ₗ[ZMod 3] V).injective hcoe
    have hle : Module.finrank (ZMod 3) Porth ≤ Module.finrank (ZMod 3) P :=
      LinearMap.finrank_le_finrank_of_injective hφinj
    have hfinP : Module.finrank (ZMod 3) P = 2 := ff_finrank_span_pair hu hv' huv
    have hfinOrth : Module.finrank (ZMod 3) Porth + 2 = Module.finrank (ZMod 3) V :=
      ff_finrank_orth_pair hQ hu hv' huv
    exfalso
    omega

end CFSG.OddStandard.SmallF3.Omega
