module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalGroups.Orthogonal.Hyperbolic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartOne.KC.OrthogonalKernelSectorRigidityPaired
public import CFSG.RankThree.PartOne.KC.OrthogonalSelfDualBlock

public section

namespace CFSG.LieType.SeitzGeneration.OrthBlk

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.ClassicalGroups.Orthogonal

section SelfDualDichotomy

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {y : V ≃ₗ[K] V}

theorem selfDual_of_dvd (hy : OddOrderIsometry Q p y) {h : K[X]}
    [Fact (Irreducible h)] (hh : h ∈ primaryFactors y.toLinearMap) {d : ℕ}
    (hdvd : p ∣ Nat.card K ^ d + 1) : h = reciprocalPolynomial h := by
  have hlamp : AdjoinRoot.root h ^ p = 1 := root_pow_eq_one (hy.dvd_X_pow_sub_one hh)
  have hp0 : p ≠ 0 := fun h0 => hy.cast_ne_zero (by rw [h0]; simp)
  have hlam0 : AdjoinRoot.root h ≠ 0 := fun h0 => by
    rw [h0, zero_pow hp0] at hlamp
    exact zero_ne_one hlamp
  have hroot : AdjoinRoot.root h ^ Nat.card K ^ d = (AdjoinRoot.root h)⁻¹ := by
    obtain ⟨k, hk⟩ := hdvd
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ, hk, pow_mul, hlamp, one_pow]
  have h0 : h.coeff 0 ≠ 0 := hy.coeff_zero_ne hh
  have hmon : h.Monic := monic_of_mem_primaryFactors hh
  have hirr : Irreducible h := irreducible_of_mem_primaryFactors hh
  have h1 : aeval (AdjoinRoot.root h)⁻¹ h = 0 := by
    have e := Polynomial.aeval_algHom_apply (frobPow K (AdjoinRoot h) d : AdjoinRoot h →ₐ[K]
      AdjoinRoot h) (AdjoinRoot.root h) h
    have h3 : aeval (AdjoinRoot.root h) h = 0 := by
      rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
    rw [h3, map_zero] at e
    rw [← hroot]
    simpa [frobPow_apply] using e
  have h2 : aeval (AdjoinRoot.root h) (reciprocalPolynomial h) = 0 := by
    have := aeval_reciprocalPolynomial_of_unit (A := AdjoinRoot h) (Units.mk0 _ hlam0) h
    simp only [Units.val_mk0, Units.val_inv_eq_inv_val] at this
    rw [this, h1, mul_zero, smul_zero]
  have h3 : aeval (AdjoinRoot.root h) h = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  exact (minpoly.eq_of_irreducible_of_monic hirr h3 hmon).trans
    (minpoly.eq_of_irreducible_of_monic (irreducible_reciprocalPolynomial hirr h0) h2
      (monic_reciprocalPolynomial h0)).symm

end SelfDualDichotomy

section Mixing

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

@[expose] noncomputable def eline (x : V ≃ₗ[K] V) (r : K[X])
    (u : primaryComponent x.toLinearMap r) : AdjoinRoot r →ₗ[K] V :=
  (primaryComponent x.toLinearMap r).subtype ∘ₗ
    ((LinearMap.toSpanSingleton (AdjoinRoot r) (primaryComponent x.toLinearMap r) u).restrictScalars
      K)

omit [Finite K] [FiniteDimensional K V] in
theorem eline_apply (r : K[X]) (u : primaryComponent x.toLinearMap r) (z : AdjoinRoot r) :
    eline x r u z = ((z • u : primaryComponent x.toLinearMap r) : V) := rfl

omit [Finite K] [FiniteDimensional K V] in
theorem eline_injective (r : K[X]) [Fact (Irreducible r)]
    {u : primaryComponent x.toLinearMap r} (hu : u ≠ 0) :
    Function.Injective (eline x r u) := by
  intro z z' h
  have h' : z • u = z' • u := Subtype.ext h
  exact smul_left_injective _ hu h'

theorem exists_selfdual_mixing_action (hx : OddOrderIsometry Q p x) (hp2 : Odd p) {r : K[X]}
    (hr : r ∈ primaryFactors x.toLinearMap) (hne1 : r ≠ X - 1)
    (hself : r = reciprocalPolynomial r) (h2 : (2 : K) ≠ 0) {S₁ S₂ : Submodule K V}
    (hS₂ : ∀ v ∈ S₂, x v ∈ S₂)
    (hperp : ∀ u ∈ S₁, ∀ w ∈ S₂, QuadraticMap.polar Q u w = 0)
    (hv : ∃ v ∈ S₁ ⊓ primaryComponent x.toLinearMap r, Q v ≠ 0)
    (hw : ∃ w ∈ S₂ ⊓ primaryComponent x.toLinearMap r, Q w ≠ 0) :
    ∃ g ∈ specialBlock Q x r, ∃ u w : primaryComponent x.toLinearMap r,
      (u : V) ∈ S₁ ∧ (w : V) ∈ S₂ ∧ Q (u : V) ≠ 0 ∧ Q (w : V) ≠ 0 ∧
      PolarNondegOn Q (LinearMap.range (eline x r u)) ∧
      PolarNondegOn Q (LinearMap.range (eline x r w)) ∧
      ∃ lam mu : AdjoinRoot r, lam ≠ 0 ∧ mu ≠ 0 ∧ ∀ z : AdjoinRoot r,
        g (eline x r u z) = eline x r u (lam * z) + eline x r w (mu * z) := by
  have : Fact (Irreducible r) := ⟨irreducible_of_mem_primaryFactors hr⟩
  obtain ⟨d, H, hdeg, -, htr, hadd₁, hadd₂, hsm₁, hsm₂, hsymm⟩ :=
    hx.exists_selfDual_hermitian hp2 hr hne1 hself
  have hfin : finrank K (AdjoinRoot r) = 2 * d := by
    rw [(AdjoinRoot.powerBasis (Fact.out : Irreducible r).ne_zero).finrank,
      AdjoinRoot.powerBasis_dim, hdeg]
  obtain ⟨ℓ, f, hU, -, hbar⟩ := exists_unitaryFieldData K (AdjoinRoot r) hfin
  have hfb : ∀ z, frobPow K (AdjoinRoot r) d z = hU.bar z := fun z => by
    rw [frobPow_apply, hbar]
  have hsm₁' : ∀ (c : AdjoinRoot r) u w, H (c • u) w = hU.bar c * H u w := fun c u w => by
    rw [hsm₁, hfb]
  have hsymm' : ∀ u w, H w u = hU.bar (H u w) := fun u w => by rw [hsymm, hfb]
  obtain ⟨v, hv1, hvQ⟩ := hv
  obtain ⟨w, hw1, hwQ⟩ := hw
  let u : primaryComponent x.toLinearMap r := ⟨v, hv1.2⟩
  let w' : primaryComponent x.toLinearMap r := ⟨w, hw1.2⟩
  have hu0 : u ≠ 0 := fun h => hvQ (by
    have : v = 0 := congrArg Subtype.val h
    rw [this, QuadraticMap.map_zero])
  have hw0 : w' ≠ 0 := fun h => hwQ (by
    have : w = 0 := congrArg Subtype.val h
    rw [this, QuadraticMap.map_zero])
  have hHuw : H u w' = 0 := by
    refine eq_zero_of_trace_mul_eq_zero K (AdjoinRoot r) fun c => ?_
    rw [htr u w' c]
    exact hperp _ hv1.1 _ (smul_mem_of_stable hS₂ c w' hw1.1)
  have hHwu : H w' u = 0 := by rw [hsymm' u w', hHuw, map_zero]
  have hanis : ∀ y : primaryComponent x.toLinearMap r, Q (y : V) ≠ 0 → H y y ≠ 0 := by
    intro y hy h0
    have h1 := htr y y 1
    rw [h0, zero_mul, map_zero, one_smul, QuadraticMap.polar_self, two_nsmul] at h1
    have h3 : (2 : K) * Q (y : V) = 0 := by rw [two_mul]; exact h1.symm
    exact hy ((mul_eq_zero.mp h3).resolve_left h2)
  have hHuu : H u u ≠ 0 := hanis u hvQ
  have hHww : H w' w' ≠ 0 := hanis w' hwQ
  have hHuu_fix : hU.bar (H u u) = H u u := (hsymm' u u).symm
  have hHww_fix : hU.bar (H w' w') = H w' w' := (hsymm' w' w').symm
  have hreg : ∀ y : primaryComponent x.toLinearMap r, H y y ≠ 0 →
      PolarNondegOn Q (LinearMap.range (eline x r y)) := by
    intro y hy
    rintro _ ⟨z₁, rfl⟩ hxy
    have hz : ∀ z : AdjoinRoot r, Algebra.trace K (AdjoinRoot r) (hU.bar z₁ * H y y * z) = 0 := by
      intro z
      have h1 := hxy (eline x r y z) ⟨z, rfl⟩
      rw [eline_apply, eline_apply] at h1
      have h3 := htr (z₁ • y) y z
      rw [hsm₁', h1] at h3
      exact h3
    have h4 : hU.bar z₁ * H y y = 0 := eq_zero_of_trace_mul_eq_zero K (AdjoinRoot r) hz
    have h5 : hU.bar z₁ = 0 := (mul_eq_zero.mp h4).resolve_right hy
    have h6 : z₁ = 0 := by
      have := congrArg hU.bar h5
      rwa [hU.bar_bar, map_zero] at this
    rw [h6, map_zero]
  set f₀ : AdjoinRoot r := -(H u u) / H w' w' with hf₀
  have hf₀0 : f₀ ≠ 0 := div_ne_zero (neg_ne_zero.mpr hHuu) hHww
  have hf₀fix : hU.bar f₀ = f₀ := by
    rw [hf₀, map_div₀, map_neg, hHuu_fix, hHww_fix]
  obtain ⟨c, hc⟩ := hU.normHom_surjective ⟨f₀, hU.mem_fixedField.mpr hf₀fix⟩
  have hcn : c * hU.bar c = f₀ := congrArg Subtype.val hc
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hf₀0 (by rw [← hcn, zero_mul])
  have he : H (u + c • w') (u + c • w') = 0 := by
    simp only [hadd₁, hadd₂, hsm₁', hsm₂, hHuw, hHwu, mul_zero, add_zero, zero_add]
    have : hU.bar c * (c * H w' w') = f₀ * H w' w' := by rw [← hcn]; ring
    rw [this, hf₀, div_mul_cancel₀ _ hHww, add_neg_cancel]
  obtain ⟨z, hz⟩ := hU.exists_bar_ne
  set a : AdjoinRoot r := z - hU.bar z with ha
  have ha0 : a ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have haσ : hU.bar a = -a := by rw [ha, map_sub, hU.bar_bar]; ring
  have hpres : ∀ y y' : primaryComponent x.toLinearMap r,
      H (((unitaryTransvection H hadd₂ hsm₂ he a : BlockGL x r) :
          Module.End (AdjoinRoot r) (primaryComponent x.toLinearMap r)) y)
        (((unitaryTransvection H hadd₂ hsm₂ he a : BlockGL x r) :
          Module.End (AdjoinRoot r) (primaryComponent x.toLinearMap r)) y') = H y y' := by
    intro y y'
    rw [unitaryTransvection_apply, unitaryTransvection_apply]
    exact hermitian_transvection_preserves hU.bar H hadd₁ hadd₂ hsm₁' hsm₂ hsymm' he haσ y y'
  obtain ⟨g, hg⟩ := (hx.mem_range_blockGL_selfDual_iff hr hne1 hself H htr
    (unitaryTransvection H hadd₂ hsm₂ he a)).mpr hpres
  have hlam : 1 + a * H u u ≠ 0 := by
    intro h0
    have h1 := congrArg hU.bar h0
    rw [map_add, map_one, map_mul, haσ, hHuu_fix, map_zero] at h1
    have h3 : (2 : AdjoinRoot r) = 0 := by linear_combination h0 + h1
    have h4 : algebraMap K (AdjoinRoot r) 2 = 2 := map_ofNat _ 2
    exact h2 ((algebraMap K (AdjoinRoot r)).injective (by rw [h4, h3, map_zero]))
  have hact : ∀ z : AdjoinRoot r,
      (((unitaryTransvection H hadd₂ hsm₂ he a : BlockGL x r) :
          Module.End (AdjoinRoot r) (primaryComponent x.toLinearMap r)) (z • u)) =
        ((1 + a * H u u) * z) • u + ((a * H u u * c) * z) • w' := by
    intro z
    have hHe : H (u + c • w') (z • u) = z * H u u := by
      rw [hadd₁, hsm₁', hsm₂, hsm₂, hHwu, mul_zero, mul_zero, add_zero]
    rw [unitaryTransvection_apply, hHe]
    module
  refine ⟨g.1, mem_specialBlock.mpr ⟨g.2, ?_⟩, u, w', hv1.1, hw1.1, hvQ, hwQ, hreg u hHuu,
    hreg w' hHww, 1 + a * H u u, a * H u u * c, hlam,
    mul_ne_zero (mul_ne_zero ha0 hHuu) hc0, fun z => ?_⟩
  · rw [blockDet_apply, hg]
    exact det_unitaryTransvection H hadd₂ hsm₂ he a
  · have h1 := coe_blockGL (Q := Q) (x := x) r g (z • u)
    rw [hg, hact, Submodule.coe_add] at h1
    exact h1.symm

end Mixing

end CFSG.LieType.SeitzGeneration.OrthBlk
