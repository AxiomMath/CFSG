module

public import CFSG.LieType.SeitzGeneration.OrthSdMixing

public section

namespace CFSG.LieType.SeitzGeneration.OrthBlk

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.ClassicalGroups.Orthogonal

section Family

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem exists_selfdual_mixing_family (hx : OddOrderIsometry Q p x) (hp2 : Odd p) {r : K[X]}
    [Fact (Irreducible r)] (hr : r ∈ primaryFactors x.toLinearMap) (hne1 : r ≠ X - 1)
    (hself : r = reciprocalPolynomial r) {S₁ S₂ : Submodule K V}
    (hS₂ : ∀ v ∈ S₂, x v ∈ S₂) (hperp : ∀ a ∈ S₁, ∀ b ∈ S₂, QuadraticMap.polar Q a b = 0)
    (u w : primaryComponent x.toLinearMap r) (hu : (u : V) ∈ S₁) (hw : (w : V) ∈ S₂)
    (hu0 : u ≠ 0) (hw0 : w ≠ 0) (hureg : PolarNondegOn Q (LinearMap.range (eline x r u)))
    (hwreg : PolarNondegOn Q (LinearMap.range (eline x r w))) :
    ∃ d : ℕ, r.natDegree = 2 * d ∧ ∃ c : AdjoinRoot r, c ≠ 0 ∧
      ∀ θ : AdjoinRoot r, frobPow K (AdjoinRoot r) d θ = -θ →
        ∃ g ∈ specialBlock Q x r,
          (∀ z : AdjoinRoot r, g (eline x r u z) =
            eline x r u ((1 + θ) * z) + eline x r w ((θ * c) * z)) ∧
          ∀ z z' : AdjoinRoot r, QuadraticMap.polar Q (eline x r u ((1 + θ) * z))
            (eline x r u ((1 + θ) * z')) =
            QuadraticMap.polar Q (eline x r u z) (eline x r u ((1 - θ ^ 2) * z')) := by
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
  have hpolar : ∀ (y : primaryComponent x.toLinearMap r) (z z' : AdjoinRoot r),
      QuadraticMap.polar Q (eline x r y z) (eline x r y z') =
        Algebra.trace K (AdjoinRoot r) (hU.bar z * H y y * z') := by
    intro y z z'
    have h1 := htr (z • y) y z'
    rw [hsm₁'] at h1
    exact h1.symm
  have hHnz : ∀ y : primaryComponent x.toLinearMap r, y ≠ 0 →
      PolarNondegOn Q (LinearMap.range (eline x r y)) → H y y ≠ 0 := by
    intro y hy0 hyreg h0
    apply hy0
    have h1 : eline x r y 1 = 0 := hyreg _ ⟨1, rfl⟩ (by
      rintro _ ⟨z, rfl⟩
      rw [hpolar, h0, mul_zero, zero_mul, map_zero])
    rw [eline_apply, one_smul] at h1
    exact Subtype.ext h1
  have hHuu : H u u ≠ 0 := hHnz u hu0 hureg
  have hHww : H w w ≠ 0 := hHnz w hw0 hwreg
  have hHuw : H u w = 0 := by
    refine eq_zero_of_trace_mul_eq_zero K (AdjoinRoot r) fun c => ?_
    rw [htr u w c]
    exact hperp _ hu _ (smul_mem_of_stable hS₂ c w hw)
  have hHwu : H w u = 0 := by rw [hsymm' u w, hHuw, map_zero]
  have hHuu_fix : hU.bar (H u u) = H u u := (hsymm' u u).symm
  have hHww_fix : hU.bar (H w w) = H w w := (hsymm' w w).symm
  obtain ⟨f₀, hf₀⟩ : ∃ f₀ : AdjoinRoot r, f₀ = -(H u u) / H w w := ⟨_, rfl⟩
  have hf₀0 : f₀ ≠ 0 := by
    rw [hf₀]
    exact div_ne_zero (neg_ne_zero.mpr hHuu) hHww
  have hf₀fix : hU.bar f₀ = f₀ := by
    rw [hf₀, map_div₀, map_neg, hHuu_fix, hHww_fix]
  obtain ⟨c, hc⟩ := hU.normHom_surjective ⟨f₀, hU.mem_fixedField.mpr hf₀fix⟩
  have hcn : c * hU.bar c = f₀ := congrArg Subtype.val hc
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hf₀0 (by rw [← hcn, zero_mul])
  have he : H (u + c • w) (u + c • w) = 0 := by
    simp only [hadd₁, hadd₂, hsm₁', hsm₂, hHuw, hHwu, mul_zero, add_zero, zero_add]
    have : hU.bar c * (c * H w w) = f₀ * H w w := by rw [← hcn]; ring
    rw [this, hf₀, div_mul_cancel₀ _ hHww, add_neg_cancel]
  refine ⟨d, hdeg, c, hc0, fun θ hθ => ?_⟩
  have hθ' : hU.bar θ = -θ := by rw [← hfb]; exact hθ
  obtain ⟨a, ha⟩ : ∃ a : AdjoinRoot r, a = θ * (H u u)⁻¹ := ⟨_, rfl⟩
  have haσ : hU.bar a = -a := by
    rw [ha, map_mul, map_inv₀, hHuu_fix, hθ', neg_mul]
  have haH : a * H u u = θ := by rw [ha, mul_assoc, inv_mul_cancel₀ hHuu, mul_one]
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
  have hact : ∀ z : AdjoinRoot r,
      (((unitaryTransvection H hadd₂ hsm₂ he a : BlockGL x r) :
          Module.End (AdjoinRoot r) (primaryComponent x.toLinearMap r)) (z • u)) =
        ((1 + θ) * z) • u + ((θ * c) * z) • w := by
    intro z
    have hHe : H (u + c • w) (z • u) = z * H u u := by
      rw [hadd₁, hsm₁', hsm₂, hsm₂, hHwu, mul_zero, mul_zero, add_zero]
    rw [unitaryTransvection_apply, hHe, ← haH]
    module
  refine ⟨g.1, mem_specialBlock.mpr ⟨g.2, ?_⟩, fun z => ?_, fun z z' => ?_⟩
  · rw [blockDet_apply, hg]
    exact det_unitaryTransvection H hadd₂ hsm₂ he a
  · have h1 := coe_blockGL (Q := Q) (x := x) r g (z • u)
    rw [hg, hact, Submodule.coe_add] at h1
    exact h1.symm
  · have hbar1 : hU.bar (1 + θ) = 1 - θ := by rw [map_add, map_one, hθ']; ring
    rw [hpolar, hpolar, map_mul hU.bar (1 + θ) z, hbar1]
    congr 1
    ring

end Family

section Theta

variable {K : Type} [Field K] [Finite K]

theorem exists_trace_zero_sq_not_mem {r : K[X]} [Fact (Irreducible r)] {d : ℕ} (hd : 2 ≤ d)
    (hfin : finrank K (AdjoinRoot r) = 2 * d) :
    ∃ θ : AdjoinRoot r, frobPow K (AdjoinRoot r) d θ = -θ ∧
      ∀ c : K, θ ^ 2 ≠ algebraMap K (AdjoinRoot r) c := by
  classical
  obtain ⟨ℓ, f, hU, hq, hbar⟩ := exists_unitaryFieldData K (AdjoinRoot r) hfin
  have hfb : ∀ z, frobPow K (AdjoinRoot r) d z = hU.bar z := fun z => by
    rw [frobPow_apply, hbar]
  obtain ⟨f₀, hf₀F, hf₀K⟩ : ∃ f₀ : AdjoinRoot r, hU.bar f₀ = f₀ ∧
      ∀ c : K, f₀ ≠ algebraMap K (AdjoinRoot r) c := by
    by_contra hcon
    push Not at hcon
    choose φ hφ using fun y : hU.fixedField => hcon y.1 (hU.mem_fixedField.mp y.2)
    have hinj : Function.Injective φ := fun y y' h => Subtype.ext (by rw [hφ y, hφ y', h])
    have h1 := Nat.card_le_card_of_injective φ hinj
    rw [hU.card_fixedField, pow_mul, ← hq] at h1
    have h2 : 1 < Nat.card K := Finite.one_lt_card
    have h3 : Nat.card K ^ 2 ≤ Nat.card K ^ d := Nat.pow_le_pow_right (by omega) hd
    nlinarith
  obtain ⟨θ₀, hθ₀, hθ₀0⟩ : ∃ θ₀ : AdjoinRoot r, hU.bar θ₀ = -θ₀ ∧ θ₀ ≠ 0 := by
    by_cases h2 : (2 : AdjoinRoot r) = 0
    · refine ⟨1, ?_, one_ne_zero⟩
      rw [map_one]
      linear_combination h2
    · obtain ⟨z, hz⟩ := hU.exists_bar_ne
      refine ⟨z - hU.bar z, ?_, sub_ne_zero.mpr (Ne.symm hz)⟩
      rw [map_sub, hU.bar_bar]
      ring
  by_contra hcon
  push Not at hcon
  have hsq : ∀ f : AdjoinRoot r, hU.bar f = f → ∃ c : K,
      (θ₀ * f) ^ 2 = algebraMap K (AdjoinRoot r) c := fun f hf =>
    (hcon (θ₀ * f) (by rw [hfb, map_mul, hθ₀, hf, neg_mul]))
  obtain ⟨μ, hμ⟩ := hsq 1 (map_one _)
  have hθ₀2 : θ₀ ^ 2 ≠ 0 := pow_ne_zero 2 hθ₀0
  have hμ0 : algebraMap K (AdjoinRoot r) μ ≠ 0 := by
    rw [mul_one] at hμ
    rw [← hμ]
    exact hθ₀2
  have hsq' : ∀ f : AdjoinRoot r, hU.bar f = f → ∃ c : K,
      f ^ 2 = algebraMap K (AdjoinRoot r) c := by
    intro f hf
    obtain ⟨c, hc⟩ := hsq f hf
    refine ⟨c / μ, ?_⟩
    rw [map_div₀, ← hc]
    rw [mul_one] at hμ
    rw [← hμ]
    field_simp
  obtain ⟨c₁, hc₁⟩ := hsq' f₀ hf₀F
  obtain ⟨c₂, hc₂⟩ := hsq' (1 + f₀) (by rw [map_add, map_one, hf₀F])
  by_cases h2K : (2 : K) = 0
  ·
    have : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2K
    obtain ⟨s, hs⟩ := isSquare_of_charTwo' c₁
    have h2E : (2 : AdjoinRoot r) = 0 := by
      have h4 : algebraMap K (AdjoinRoot r) 2 = 2 := map_ofNat _ 2
      rw [← h4, h2K, map_zero]
    refine hf₀K s ?_
    have h5 : (f₀ - algebraMap K (AdjoinRoot r) s) ^ 2 = 0 := by
      have : algebraMap K (AdjoinRoot r) c₁ = algebraMap K (AdjoinRoot r) s ^ 2 := by
        rw [hs, map_mul, sq]
      linear_combination hc₁ + this + (algebraMap K (AdjoinRoot r) s *
        (algebraMap K (AdjoinRoot r) s - f₀)) * h2E
    exact sub_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp h5)
  ·
    refine hf₀K ((c₂ - 1 - c₁) / 2) ?_
    have h2E : algebraMap K (AdjoinRoot r) 2 ≠ 0 := fun h =>
      h2K ((algebraMap K (AdjoinRoot r)).injective (by rw [h, map_zero]))
    have h4 : algebraMap K (AdjoinRoot r) 2 = 2 := map_ofNat _ 2
    rw [map_div₀, map_sub, map_sub, map_one, ← hc₁, ← hc₂, h4]
    have h2E' : (2 : AdjoinRoot r) ≠ 0 := by rwa [h4] at h2E
    field_simp
    ring

end Theta

section NotProportional

variable {K E V : Type} [Field K] [Field E] [Algebra K E] [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

theorem not_proportional_of_mixing (ιA ιB : E →ₗ[K] V) (g : V ≃ₗ[K] V)
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (lam mu ν : E)
    (hgact : ∀ z, g (ιA z) = ιA (lam * z) + ιB (mu * z))
    (hperp : ∀ z z', QuadraticMap.polar Q (ιA z) (ιB z') = 0)
    (hbal : ∀ z z', QuadraticMap.polar Q (ιA (lam * z)) (ιA (lam * z')) =
      QuadraticMap.polar Q (ιA z) (ιA (ν * z')))
    (hreg : PolarNondegOn Q (LinearMap.range ιA)) (hιA : Function.Injective ιA)
    (hν : ∀ c : K, 1 - ν ≠ algebraMap K E c) :
    ∀ z : E, z ≠ 0 → ∀ c : K, ∃ z' : E, QuadraticMap.polar Q (ιA z') (ιA z) ≠
      c * QuadraticMap.polar Q (ιB (mu * z')) (ιB (mu * z)) := by
  intro z hz c
  by_contra hcon
  push Not at hcon
  have key : ∀ z' : E, QuadraticMap.polar Q (ιB (mu * z')) (ιB (mu * z)) =
      QuadraticMap.polar Q (ιA z') (ιA z) - QuadraticMap.polar Q (ιA z') (ιA (ν * z)) := by
    intro z'
    have h1 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hgO (ιA z') (ιA z)
    rw [hgact, hgact, QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
      QuadraticMap.polar_add_right, hperp, QuadraticMap.polar_comm Q (ιB (mu * z')) (ιA (lam * z)),
      hperp, hbal, zero_add, add_zero] at h1
    linear_combination h1
  have hξ : ∀ z' : E, QuadraticMap.polar Q (ιA z') (ιA (z - c • z + c • (ν * z))) = 0 := by
    intro z'
    rw [map_add, map_sub, map_smul, map_smul, QuadraticMap.polar_add_right,
      QuadraticMap.polar_sub_right, polar_smul_right_eq, polar_smul_right_eq]
    have h1 := hcon z'
    rw [key z'] at h1
    linear_combination h1
  have hξ0 : ιA (z - c • z + c • (ν * z)) = 0 :=
    hreg _ ⟨_, rfl⟩ (by
      rintro _ ⟨z', rfl⟩
      rw [QuadraticMap.polar_comm]
      exact hξ z')
  have h2 : z - c • z + c • (ν * z) = 0 := hιA (by rw [hξ0, map_zero])
  rw [Algebra.smul_def, Algebra.smul_def] at h2
  have h3 : (1 - algebraMap K E c * (1 - ν)) * z = 0 := by linear_combination h2
  have h4 : algebraMap K E c * (1 - ν) = 1 := by
    have := (mul_eq_zero.mp h3).resolve_right hz
    linear_combination -this
  by_cases hc0 : c = 0
  · rw [hc0, map_zero, zero_mul] at h4
    exact zero_ne_one h4
  · apply hν c⁻¹
    rw [map_inv₀]
    exact eq_inv_of_mul_eq_one_right h4

end NotProportional

end CFSG.LieType.SeitzGeneration.OrthBlk
