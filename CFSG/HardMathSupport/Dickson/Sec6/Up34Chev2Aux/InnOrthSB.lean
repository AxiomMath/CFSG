module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnSpGen
public import CFSG.RankThree.PartOne.KC.OrthogonalBlockQuasisimple

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.OrthBlocks

open Polynomial Module CFSG CFSG.Open CFSG.Blueprint CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.LocalAnalysis.ComponentInitial
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2
open CFSG.ClassicalGroups.Orthogonal CFSG.ComponentClassification.CatLeaf

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}

section Paired


theorem specialBlock_central_of_paired (hO : LieOrderFormulasInput) {f₀ : ℕ} (hf₀ : 1 ≤ f₀)
    (hK : Nat.card K = 2 ^ f₀) (hx : OddOrderIsometry Q 3 x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1) (hne : h ≠ reciprocalPolynomial h)
    (hm : 2 ≤ primaryMultiplicity x.toLinearMap h)
    (hL : IsLThreeFour (↥(specialBlock Q x h) ⧸ Subgroup.center ↥(specialBlock Q x h))) :
    ∃ z ∈ specialBlock Q x h, (∀ g ∈ specialBlock Q x h, g * z = z * g) ∧ z ^ 3 = 1 ∧ z ≠ 1 := by
  have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have h4 : 4 ≤ Nat.card (AdjoinRoot h) := by
    have := hx.p_lt_card_adjoinRoot Nat.prime_three hh hne1
    omega
  let b : Module.Basis (Fin (primaryMultiplicity x.toLinearMap h)) (AdjoinRoot h)
      (primaryComponent x.toLinearMap h) := Module.finBasisOfFinrankEq _ _ rfl
  let e₁ : ↥(specialBlock Q x h) ≃*
      SpecialLinearGroup (AdjoinRoot h) (primaryComponent x.toLinearMap h) :=
    MulEquiv.ofBijective (specialToSL Q x h)
      ⟨hx.specialToSL_injective hh, hx.specialToSL_surjective_paired hh hne⟩
  let e1 : ↥(specialBlock Q x h) ≃*
      Matrix.SpecialLinearGroup (Fin (primaryMultiplicity x.toLinearMap h)) (AdjoinRoot h) :=
    e₁.trans (Matrix.SpecialLinearGroup.toLin_equiv b).symm
  have hE : Nat.card (AdjoinRoot h) = 2 ^ (f₀ * finrank K (AdjoinRoot h)) := by
    rw [Module.natCard_eq_pow_finrank (K := K), hK, ← pow_mul]
  have h4e : 4 ≤ 2 ^ (f₀ * finrank K (AdjoinRoot h)) := hE ▸ h4
  have he : 1 ≤ f₀ * finrank K (AdjoinRoot h) := by
    by_contra hlt
    have : f₀ * finrank K (AdjoinRoot h) = 0 := by omega
    rw [this] at h4e
    omega
  have hadm : StatedLieAdmissible .PSL (primaryMultiplicity x.toLinearMap h) 2
      (f₀ * finrank K (AdjoinRoot h)) :=
    ⟨Nat.prime_two, he, hm, fun hc => by have := (Prod.mk.inj hc).2; omega,
      fun hc => by have := (Prod.mk.inj hc).2; omega⟩
  obtain ⟨-, -, z, hzc, hz3, hz1⟩ := block_central_of_isLThreeFour hO hE e1 hadm hL
  refine ⟨z.1, z.2, fun g hg => ?_, congrArg Subtype.val hz3, fun h1 => hz1 (Subtype.ext h1)⟩
  exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hzc ⟨g, hg⟩)

end Paired

section SelfDual

theorem false_of_specialBlock_selfDual (hO : LieOrderFormulasInput) {f₀ : ℕ} (hf₀ : 1 ≤ f₀)
    (hK : Nat.card K = 2 ^ f₀) (hx : OddOrderIsometry Q 3 x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h) (hm : 2 ≤ primaryMultiplicity x.toLinearMap h)
    (hL : IsLThreeFour (↥(specialBlock Q x h) ⧸ Subgroup.center ↥(specialBlock Q x h))) :
    False := by
  classical
  have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hp2' : Odd 3 := by decide
  have hirr := irreducible_of_mem_primaryFactors hh
  obtain ⟨d, H, hdeg, hroot, hH, hadd1, hadd2, hleft, hright, hsymm⟩ :=
    hx.exists_selfDual_hermitian hp2' hh hne1 hself
  have hd : finrank K (AdjoinRoot h) = 2 * d := by
    rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hdeg]
  obtain ⟨ℓ, f, hU, hq, hbar⟩ := exists_unitaryFieldData K (AdjoinRoot h) hd
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
  have hd0 : d ≠ 0 := by
    rintro rfl
    have : 0 < finrank K (AdjoinRoot h) := Module.finrank_pos
    omega
  have hQ2 : 2 ≤ ℓ ^ (f * d) := by
    have h1 : Nat.card K ^ d = ℓ ^ (f * d) := by rw [hq, pow_mul]
    have h2 : Nat.card K ≤ Nat.card K ^ d := Nat.le_self_pow hd0 _
    have h3 : 1 < Nat.card K := Finite.one_lt_card
    omega
  let e₁ : ↥(specialBlock Q x h) ≃* ↥(sesqSpecialUnitaryGroup B) :=
    (MonoidHom.ofInjective (hx.specialBlockGL_injective hh)).trans
      (MulEquiv.subgroupCongr hrange)
  have hm' : finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h) =
      primaryMultiplicity x.toLinearMap h := rfl
  have hℓ2 : ℓ = 2 := by
    have hf1 : 1 ≤ f := by
      by_contra hlt
      have : f = 0 := by omega
      rw [this, pow_zero] at hq
      have := Finite.one_lt_card (α := K)
      omega
    have hdvd : ℓ ∣ 2 ^ f₀ := by
      rw [← hK, hq]
      exact dvd_pow_self ℓ (by omega)
    exact (Nat.prime_dvd_prime_iff_eq hU.prime Nat.prime_two).1
      (hU.prime.dvd_of_dvd_pow hdvd)
  subst hℓ2
  have hFfin : Finite ↥(sesqSpecialUnitaryGroup B) := by
    have : Finite V := Module.finite_of_finite K
    have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
      fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
    exact Finite.of_equiv _ e₁.toEquiv
  by_cases hexc : (primaryMultiplicity x.toLinearMap h = 2 ∧ 2 ^ (f * d) = 2) ∨
      (primaryMultiplicity x.toLinearMap h = 2 ∧ 2 ^ (f * d) = 3) ∨
      (primaryMultiplicity x.toLinearMap h = 3 ∧ 2 ^ (f * d) = 2)
  ·
    have hcard := (CFSG.LinearGroups.unitary_full_group_order hU hBsymm hBl hm' (by omega)).2.1
    have hsmall : Nat.card ↥(sesqSpecialUnitaryGroup B) < 20160 := by
      rcases hexc with ⟨hm2, hQ⟩ | ⟨hm2, hQ⟩ | ⟨hm2, hQ⟩
      · rw [hm2, hQ] at hcard
        have e : ((2 : ℕ) : ℤ) ^ (2 * (2 - 1) / 2) *
            ∏ i ∈ Finset.Icc 2 2, (((2 : ℕ) : ℤ) ^ i - (-1) ^ i) = 6 := by decide +kernel
        have h6 : Nat.card ↥(sesqSpecialUnitaryGroup B) = 6 := by exact_mod_cast hcard.trans e
        omega
      · rw [hm2, hQ] at hcard
        have e : ((3 : ℕ) : ℤ) ^ (2 * (2 - 1) / 2) *
            ∏ i ∈ Finset.Icc 2 2, (((3 : ℕ) : ℤ) ^ i - (-1) ^ i) = 24 := by decide +kernel
        have h24 : Nat.card ↥(sesqSpecialUnitaryGroup B) = 24 := by exact_mod_cast hcard.trans e
        omega
      · rw [hm2, hQ] at hcard
        have e : ((2 : ℕ) : ℤ) ^ (3 * (3 - 1) / 2) *
            ∏ i ∈ Finset.Icc 2 3, (((2 : ℕ) : ℤ) ^ i - (-1) ^ i) = 216 := by decide +kernel
        have h216 : Nat.card ↥(sesqSpecialUnitaryGroup B) = 216 := by
          exact_mod_cast hcard.trans e
        omega
    have h1 := card_eq_of_isLThreeFour hL
    haveI : Finite ↥(specialBlock Q x h) := Finite.of_equiv _ e₁.symm.toEquiv
    have h2 : Nat.card (↥(specialBlock Q x h) ⧸ Subgroup.center ↥(specialBlock Q x h)) ≤
        Nat.card ↥(specialBlock Q x h) :=
      Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
    rw [Nat.card_congr e₁.toEquiv] at h2
    omega
  · have hqq : (Module.finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h) = 2 →
          4 ≤ 2 ^ (f * d)) ∧
        (Module.finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h) = 3 →
          3 ≤ 2 ^ (f * d)) := by
      constructor <;> intro hm0 <;> omega
    exact not_isLThreeFour_of_equiv_sesqSU hO hU hBsymm hBl (by rw [hm']; exact hm) hqq e₁ hL

end SelfDual

end CFSG.HardMathSupport.Dickson.Sec6.OrthBlocks
