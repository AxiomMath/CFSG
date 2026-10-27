module

public import CFSG.RankThree.PartOne.KC.OrthogonalBlockQuasisimple
import all CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434ClUnitary
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434ClNum
import CFSG.RankThree.PartOne.KC.OrthogonalFactorization
import CFSG.RankThree.PartOne.KC.OrthogonalInnerPlaneDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434.Cl

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.LocalAnalysis.ComponentInitial CFSG.Open

section SelfDual

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}

instance finite_linearEquiv_of_finite : Finite (V ≃ₗ[K] V) := by
  haveI : Finite V := Module.finite_of_finite K
  exact Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)

theorem selfDual_unitary_data (hx : OddOrderIsometry Q 5 x) {h : K[X]} [Fact (Irreducible h)]
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h) :
    ∃ (d ℓ f : ℕ) (hU : UnitaryFieldData ℓ (f * d) (AdjoinRoot h))
      (B : primaryComponent x.toLinearMap h →ₛₗ[hU.bar]
        primaryComponent x.toLinearMap h →ₗ[AdjoinRoot h] AdjoinRoot h),
      h.natDegree = 2 * d ∧ Nat.card K = ℓ ^ f ∧ ringChar K = ℓ ∧ 5 ∣ Nat.card K ^ d + 1 ∧
        B.IsSymm ∧ B.SeparatingLeft ∧
        Nonempty (↥(specialBlock Q x h) ≃* ↥(sesqSpecialUnitaryGroup B)) := by
  classical
  have hp2' : Odd 5 := by decide
  have hirr := irreducible_of_mem_primaryFactors hh
  obtain ⟨d, H, hdeg, hroot, hH, hadd1, hadd2, hleft, hright, hsymm⟩ :=
    hx.exists_selfDual_hermitian hp2' hh hne1 hself
  have hd : finrank K (AdjoinRoot h) = 2 * d := by
    rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hdeg]
  obtain ⟨ℓ, f, hU, hq0, hbar⟩ := exists_unitaryFieldData K (AdjoinRoot h) hd
  have hbar' : ∀ z, frobPow K (AdjoinRoot h) d z = hU.bar z := fun z => by
    rw [hbar, frobPow_apply]
  let B : primaryComponent x.toLinearMap h →ₛₗ[hU.bar]
      primaryComponent x.toLinearMap h →ₗ[AdjoinRoot h] AdjoinRoot h :=
    LinearMap.mk₂'ₛₗ hU.bar (RingHom.id _) H hadd1
      (fun c u w => by rw [hleft, smul_eq_mul, hbar']) hadd2
      (fun c u w => by rw [hright, smul_eq_mul, RingHom.id_apply])
  have hBH : ∀ u w, B u w = H u w := fun u w => rfl
  have hBsymm : B.IsSymm := ⟨fun u w => by rw [hBH, hBH, hsymm u w, hbar']⟩
  have hBl : B.SeparatingLeft := by
    intro u hu
    refine Subtype.ext (hx.eq_zero_of_polar_selfdual hh hself u.2 fun w hw => ?_)
    have h1 := hH u ⟨w, hw⟩ 1
    rw [mul_one, one_smul] at h1
    have h2 : H u ⟨w, hw⟩ = 0 := by rw [← hBH]; exact hu _
    rw [h2, map_zero] at h1
    exact h1.symm
  have hrange : (specialBlockGL Q x h).range = sesqSpecialUnitaryGroup B := by
    rw [range_specialBlockGL, sesqSpecialUnitaryGroup]
    congr 1
    ext γ
    rw [hx.mem_range_blockGL_selfDual_iff hh hne1 hself H hH, mem_sesqUnitaryGroup]
    exact Iff.rfl
  haveI := hU.finite
  haveI : Fact ℓ.Prime := ⟨hU.prime⟩
  haveI := hU.charP
  have hchar : ringChar K = ℓ := by
    rw [Algebra.ringChar_eq K (AdjoinRoot h)]
    exact ringChar.eq _ ℓ
  let e₁ : ↥(specialBlock Q x h) ≃* ↥(sesqSpecialUnitaryGroup B) :=
    (MonoidHom.ofInjective (hx.specialBlockGL_injective hh)).trans
      (MulEquiv.subgroupCongr hrange)
  exact ⟨d, ℓ, f, hU, B, hdeg, hq0, hchar, hx.dvd_card_pow_add_one Nat.prime_five hh hne1 hroot,
    hBsymm, hBl, ⟨e₁⟩⟩

theorem two_le_multiplicity_of_quasisimple (hx : OddOrderIsometry Q 5 x) {h : K[X]}
    [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap)
    (hq : CFSG.IsQuasisimple ↥(specialBlock Q x h)) :
    2 ≤ primaryMultiplicity x.toLinearMap h := by
  by_contra hlt
  have hpos := hx.primaryMultiplicity_pos hh
  have h1 : primaryMultiplicity x.toLinearMap h = 1 := by omega
  exact ne_bot_of_isQuasisimple hq (hx.specialBlock_eq_bot_of_finrank_eq_one hh h1)

theorem selfDual_a5 (hx : OddOrderIsometry Q 5 x) {h : K[X]} [Fact (Irreducible h)]
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h) (hℓ5 : ringChar K ≠ 5)
    (hq : CFSG.IsQuasisimple ↥(specialBlock Q x h))
    (h60 : Nat.card (↥(specialBlock Q x h) ⧸ Subgroup.center ↥(specialBlock Q x h)) = 60) :
    primaryMultiplicity x.toLinearMap h = 2 ∧
      ∃ d, h.natDegree = 2 * d ∧ Nat.card K ^ d = 4 := by
  classical
  obtain ⟨d, ℓ, f, hU, B, hdeg, hq0, hchar, -, hBsymm, hBl, ⟨e₁⟩⟩ :=
    selfDual_unitary_data hx hh hne1 hself
  haveI := hU.finite
  haveI : Fact ℓ.Prime := ⟨hU.prime⟩
  haveI := hU.charP
  have hm := two_le_multiplicity_of_quasisimple hx hh hq
  have hKd : Nat.card K ^ d = ℓ ^ (f * d) := by rw [hq0, ← pow_mul]
  rcases Nat.lt_or_ge (primaryMultiplicity x.toLinearMap h) 3 with hm3 | hm3
  · have hm2 : primaryMultiplicity x.toLinearMap h = 2 := by omega
    refine ⟨hm2, d, hdeg, ?_⟩
    have hV : finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h) = 2 := hm2
    obtain ⟨φ⟩ := CFSG.RankThree.Classical.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SL2 hU
      hBsymm hBl hV
    haveI : Finite hU.fixedField := inferInstance
    have hcardF : Nat.card hU.fixedField = ℓ ^ (f * d) := hU.card_fixedField
    have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) hU.fixedField ⧸
        Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) hU.fixedField)) = 60 := by
      rw [← card_quotient_center_of_mulEquiv (e₁.trans φ), h60]
    obtain ⟨-, h45⟩ := sl_a5 (le_refl 2) hSL
    rw [hcardF] at h45
    rcases h45 with h4 | h5
    · rw [hKd]
      exact h4
    · exact absurd (hchar ▸ prime_pow_eq_five hU.prime h5) hℓ5
  · exfalso
    have hE : Nat.card (AdjoinRoot h) = (ℓ ^ (f * d)) ^ 2 := by
      rw [hU.card, ← pow_mul, mul_comm]
    obtain ⟨e₀, he₀⟩ := hU.exists_orthonormal_basis hBsymm hBl
    obtain ⟨e₂⟩ := CFSG.RankThree.CentralLiftU.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SUid hU
      e₀ he₀
    have hS : CFSG.LieType.Universal.Unitary.SUid hU.barEquiv
        (primaryMultiplicity x.toLinearMap h) =
        CFSG.Open.StatedSU (primaryMultiplicity x.toLinearMap h) (ℓ ^ (f * d))
          (AdjoinRoot h) := by
      rw [CFSG.RankThree.CentralLiftU.barEquiv_eq_unitaryInvolution hU]
      exact CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hE _
    let e₃ : ↥(CFSG.Open.StatedSU (primaryMultiplicity x.toLinearMap h) (ℓ ^ (f * d))
        (AdjoinRoot h)) ≃* ↥(sesqSpecialUnitaryGroup B) :=
      (e₂.trans (MulEquiv.subgroupCongr hS)).symm
    have hSU : Nat.card (↥(CFSG.Open.StatedSU (primaryMultiplicity x.toLinearMap h) (ℓ ^ (f * d))
        (AdjoinRoot h)) ⧸ Subgroup.center ↥(CFSG.Open.StatedSU
          (primaryMultiplicity x.toLinearMap h) (ℓ ^ (f * d)) (AdjoinRoot h))) = 60 := by
      rw [card_quotient_center_of_mulEquiv (e₃.trans e₁.symm), h60]
    exact su_a5_false hU hm3 hSU

theorem paired_not_a5 (hx : OddOrderIsometry Q 5 x) {h : K[X]} [Fact (Irreducible h)]
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hne : h ≠ reciprocalPolynomial h) (hq : CFSG.IsQuasisimple ↥(specialBlock Q x h))
    (h60 : Nat.card (↥(specialBlock Q x h) ⧸ Subgroup.center ↥(specialBlock Q x h)) = 60) :
    False := by
  classical
  have hm := two_le_multiplicity_of_quasisimple hx hh hq
  have hbig : 5 < Nat.card (AdjoinRoot h) := hx.p_lt_card_adjoinRoot Nat.prime_five hh hne1
  let b : Module.Basis (Fin (primaryMultiplicity x.toLinearMap h)) (AdjoinRoot h)
      (primaryComponent x.toLinearMap h) := Module.finBasisOfFinrankEq _ _ rfl
  let e₁ : ↥(specialBlock Q x h) ≃*
      Matrix.SpecialLinearGroup (Fin (primaryMultiplicity x.toLinearMap h)) (AdjoinRoot h) :=
    ((MulEquiv.ofBijective (specialToSL Q x h)
      ⟨hx.specialToSL_injective hh, hx.specialToSL_surjective_paired hh hne⟩).trans
      (Matrix.SpecialLinearGroup.toLin_equiv b).symm)
  have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin (primaryMultiplicity x.toLinearMap h))
      (AdjoinRoot h) ⧸ Subgroup.center (Matrix.SpecialLinearGroup
        (Fin (primaryMultiplicity x.toLinearMap h)) (AdjoinRoot h))) = 60 := by
    rw [← card_quotient_center_of_mulEquiv e₁, h60]
  obtain ⟨-, h45⟩ := sl_a5 hm hSL
  omega

theorem five_dvd_card_specialBlock_selfDual (hx : OddOrderIsometry Q 5 x) {h : K[X]}
    [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h) (hm : 2 ≤ primaryMultiplicity x.toLinearMap h) :
    5 ∣ Nat.card ↥(specialBlock Q x h) := by
  classical
  obtain ⟨d, ℓ, f, hU, B, hdeg, hq0, hchar, h5, hBsymm, hBl, ⟨e₁⟩⟩ :=
    selfDual_unitary_data hx hh hne1 hself
  haveI := hU.finite
  have hcard := (CFSG.LinearGroups.unitary_full_group_order hU hBsymm hBl
    (n := primaryMultiplicity x.toLinearMap h) rfl (by omega)).2.1
  have hKd : Nat.card K ^ d = ℓ ^ (f * d) := by rw [hq0, ← pow_mul]
  rw [hKd] at h5
  have h5Z : (5 : ℤ) ∣ ((ℓ ^ (f * d) : ℕ) : ℤ) + 1 := by exact_mod_cast h5
  have h2 : (5 : ℤ) ∣ ((ℓ ^ (f * d) : ℕ) : ℤ) ^ 2 - (-1) ^ 2 := by
    have : ((ℓ ^ (f * d) : ℕ) : ℤ) ^ 2 - (-1) ^ 2 =
        (((ℓ ^ (f * d) : ℕ) : ℤ) + 1) * (((ℓ ^ (f * d) : ℕ) : ℤ) - 1) := by ring
    rw [this]
    exact Dvd.dvd.mul_right h5Z _
  have hprod : (5 : ℤ) ∣ ∏ i ∈ Finset.Icc 2 (primaryMultiplicity x.toLinearMap h),
      (((ℓ ^ (f * d) : ℕ) : ℤ) ^ i - (-1) ^ i) :=
    h2.trans (Finset.dvd_prod_of_mem (fun i : ℕ => ((ℓ ^ (f * d) : ℕ) : ℤ) ^ i - (-1) ^ i)
      (Finset.mem_Icc.mpr ⟨le_refl 2, hm⟩))
  have hSU : (5 : ℤ) ∣ (Nat.card ↥(sesqSpecialUnitaryGroup B) : ℤ) := by
    rw [hcard]
    exact Dvd.dvd.mul_left hprod _
  rw [Nat.card_congr e₁.toEquiv]
  exact_mod_cast hSU

theorem exists_orderOf_five_specialBlock (hx : OddOrderIsometry Q 5 x) {h : K[X]}
    [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h) (hm : 2 ≤ primaryMultiplicity x.toLinearMap h) :
    ∃ g ∈ specialBlock Q x h, orderOf g = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 5 (five_dvd_card_specialBlock_selfDual hx hh hne1
    hself hm)
  exact ⟨g.1, g.2, by rw [Subgroup.orderOf_coe]; exact hg⟩

theorem exists_scalar_block (hx : OddOrderIsometry Q 5 x) {h : K[X]} [Fact (Irreducible h)]
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h) :
    ∃ g : ↥(supportedBlock Q x h), g ^ 5 = 1 ∧
      blockDet Q x h g = AdjoinRoot.root h ^ primaryMultiplicity x.toLinearMap h ∧
      ∀ f : ↥(supportedBlock Q x h), Commute g f := by
  classical
  have hp2' : Odd 5 := by decide
  obtain ⟨d, H, hdeg, hroot, hH, -, -, hleft, hright, -⟩ :=
    hx.exists_selfDual_hermitian hp2' hh hne1 hself
  obtain ⟨hlam0, hord⟩ := hx.orderOf_root Nat.prime_five hh hne1
  have hlamp : AdjoinRoot.root h ^ 5 = 1 := root_pow_eq_one (hx.dvd_X_pow_sub_one hh)
  let c : (AdjoinRoot h)ˣ := Units.mk0 (AdjoinRoot.root h) hlam0
  have hγ : scalarGL x h c ∈ (blockGL Q x h).range := by
    rw [hx.mem_range_blockGL_selfDual_iff hh hne1 hself H hH]
    intro u w
    have hu : ((scalarGL x h c : BlockGL x h) : Module.End (AdjoinRoot h)
        (primaryComponent x.toLinearMap h)) u = AdjoinRoot.root h • u := rfl
    have hw : ((scalarGL x h c : BlockGL x h) : Module.End (AdjoinRoot h)
        (primaryComponent x.toLinearMap h)) w = AdjoinRoot.root h • w := rfl
    rw [hu, hw, hleft, hright, frobPow_apply, hroot, ← mul_assoc, inv_mul_cancel₀ hlam0, one_mul]
  obtain ⟨g, hg⟩ := hγ
  refine ⟨g, ?_, ?_, fun f => ?_⟩
  · apply hx.blockGL_injective hh
    rw [map_pow, hg, ← scalarGL_pow, map_one]
    have : c ^ 5 = 1 := Units.ext (by simpa [c] using hlamp)
    rw [this, scalarGL_one]
  · rw [blockDet_apply, hg, det_scalarGL]
    rfl
  · apply hx.blockGL_injective hh
    rw [map_mul, map_mul, hg]
    exact (Subgroup.mem_center_iff.mp (scalarGL_mem_center h c) _).symm

theorem selfDual_of_dvd_card_add_one (hx : OddOrderIsometry Q 5 x) (hq5 : 5 ∣ Nat.card K + 1)
    {h : K[X]} [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1) :
    h = reciprocalPolynomial h := by
  classical
  obtain ⟨hlam0, hord⟩ := hx.orderOf_root Nat.prime_five hh hne1
  have hlamp : AdjoinRoot.root h ^ 5 = 1 := root_pow_eq_one (hx.dvd_X_pow_sub_one hh)
  have hirr := irreducible_of_mem_primaryFactors hh
  have hmon := monic_of_mem_primaryFactors hh
  have h0 := hx.coeff_zero_ne hh
  let u : (AdjoinRoot h)ˣ := Units.mk0 (AdjoinRoot.root h) hlam0
  have hinv : ((u⁻¹ : (AdjoinRoot h)ˣ) : AdjoinRoot h) = AdjoinRoot.root h ^ Nat.card K := by
    have h1 : AdjoinRoot.root h ^ (Nat.card K + 1) = 1 := by
      obtain ⟨k, hk⟩ := hq5
      rw [hk, pow_mul, hlamp, one_pow]
    have hu : ((u : (AdjoinRoot h)ˣ) : AdjoinRoot h) = AdjoinRoot.root h := rfl
    rw [Units.val_inv_eq_inv_val, hu]
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_succ']
    exact h1
  have hfrob : aeval (AdjoinRoot.root h ^ Nat.card K) h = 0 := by
    have h1 := frobPow_apply K (AdjoinRoot h) 1 (AdjoinRoot.root h)
    rw [pow_one] at h1
    rw [← h1]
    have h2 := aeval_algHom_apply ((frobPow K (AdjoinRoot h) 1 : AdjoinRoot h ≃ₐ[K] AdjoinRoot h) :
      AdjoinRoot h →ₐ[K] AdjoinRoot h) (AdjoinRoot.root h) h
    have h3 : aeval (AdjoinRoot.root h) h = 0 := by
      rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
    simp only [AlgEquiv.coe_algHom] at h2
    rw [h2, h3, map_zero]
  have hrec : aeval (AdjoinRoot.root h) (reciprocalPolynomial h) = 0 := by
    have := aeval_reciprocalPolynomial_of_unit (A := AdjoinRoot h) u h
    have hu : ((u : (AdjoinRoot h)ˣ) : AdjoinRoot h) = AdjoinRoot.root h := rfl
    rw [hu] at this
    rw [this, hinv, hfrob, mul_zero, smul_zero]
  have hdvd : h ∣ reciprocalPolynomial h := by
    rw [AdjoinRoot.aeval_eq] at hrec
    exact AdjoinRoot.mk_eq_zero.mp hrec
  exact eq_of_monic_of_associated hmon (monic_reciprocalPolynomial h0)
    (hirr.associated_of_dvd (irreducible_reciprocalPolynomial hirr h0) hdvd)

theorem sum_natDegree_le (hx : OddOrderIsometry Q 5 x) :
    ∑ a ∈ primaryFactors x.toLinearMap, a.natDegree ≤ 5 := by
  have hprod := prod_primaryFactors hx.squarefree_minpoly
  have hne : ∀ a ∈ primaryFactors x.toLinearMap, a ≠ 0 := fun a ha =>
    (monic_of_mem_primaryFactors ha).ne_zero
  have h1 : (minpoly K x.toLinearMap).natDegree =
      ∑ a ∈ primaryFactors x.toLinearMap, a.natDegree := by
    rw [← hprod, natDegree_prod _ _ hne]
  rw [← h1]
  have hdvd : minpoly K x.toLinearMap ∣ (X ^ 5 - 1 : K[X]) := minpoly.dvd K _ hx.aeval_X_pow_sub_one
  have hX : (X ^ 5 - 1 : K[X]) ≠ 0 := by
    simpa using X_pow_sub_C_ne_zero (by norm_num : 0 < 5) (1 : K)
  calc (minpoly K x.toLinearMap).natDegree ≤ (X ^ 5 - 1 : K[X]).natDegree :=
      natDegree_le_of_dvd hdvd hX
    _ = 5 := by simpa using natDegree_X_pow_sub_C (n := 5) (r := (1 : K))

end SelfDual

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434.Cl
