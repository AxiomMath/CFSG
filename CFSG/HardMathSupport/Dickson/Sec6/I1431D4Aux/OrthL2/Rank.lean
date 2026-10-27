module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PsuHRank
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryBCentralizer
public import CFSG.RankThree.PartOne.KC.OrthogonalBlockQuasisimple

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431.OrthL2

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs CFSG.Assembly.LowTwoRank
open CFSG.HardMathSupport.Dickson.Sec6.I1431 (isTypeL2_congr_of_central not_isTypeL2_specialLinear
  t6psuh_not_isTypeL2_sesqSpecialUnitary)

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem exists_selfDual_special_equiv (hx : OddOrderIsometry Q p x) (hp : p.Prime) (hp2 : p ≠ 2)
    {h : K[X]} [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h) :
    ∃ (ℓ f d : ℕ) (hU : UnitaryFieldData ℓ (f * d) (AdjoinRoot h))
      (B : primaryComponent x.toLinearMap h →ₛₗ[hU.bar] primaryComponent x.toLinearMap h →ₗ[AdjoinRoot h]
        AdjoinRoot h), B.IsSymm ∧ B.SeparatingLeft ∧ 2 ≤ ℓ ^ (f * d) ∧
        Nonempty (↥(specialBlock Q x h) ≃* ↥(sesqSpecialUnitaryGroup B)) := by
  classical
  have hp2' : Odd p := hp.odd_of_ne_two hp2
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
  exact ⟨ℓ, f, d, hU, B, hBsymm, hBl, hQ2,
    ⟨(MonoidHom.ofInjective (hx.specialBlockGL_injective hh)).trans
      (MulEquiv.subgroupCongr hrange)⟩⟩

theorem specialBlock_multiplicity_le_two
    (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (hx : OddOrderIsometry Q p x) (hp : p.Prime) (hp2 : p ≠ 2) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1) {r : ℕ} (hr : 10 ≤ r)
    (hT : IsTypeL2 r ↥(specialBlock Q x h)) : primaryMultiplicity x.toLinearMap h ≤ 2 := by
  classical
  by_contra hlt
  have hm3 : 3 ≤ primaryMultiplicity x.toLinearMap h := by omega
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  haveI : Finite (AdjoinRoot h) := Module.finite_of_finite K
  by_cases hself : h = reciprocalPolynomial h
  · obtain ⟨ℓ, f, d, hU, B, hBsymm, hBl, hQ2, ⟨e₁⟩⟩ :=
      exists_selfDual_special_equiv hx hp hp2 hh hne1 hself
    have hm' : finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h) =
        primaryMultiplicity x.toLinearMap h := rfl
    have hT' : IsTypeL2 r ↥(sesqSpecialUnitaryGroup B) :=
      p6_isTypeL2_of_equiv e₁ hT
    by_cases hexc : primaryMultiplicity x.toLinearMap h = 3 ∧ ℓ ^ (f * d) = 2
    ·
      have hcard := (CFSG.LinearGroups.unitary_full_group_order hU hBsymm hBl hm' (by omega)).2.1
      obtain ⟨hm3', hQ⟩ := hexc
      rw [hm3', hQ] at hcard
      have e : ((2 : ℕ) : ℤ) ^ (3 * (3 - 1) / 2) *
          ∏ i ∈ Finset.Icc 2 3, (((2 : ℕ) : ℤ) ^ i - (-1) ^ i) = 216 := by decide +kernel
      have h216 : Nat.card ↥(sesqSpecialUnitaryGroup B) = 216 := by
        exact_mod_cast hcard.trans e
      obtain ⟨-, hodd, heven⟩ := CFSG.HardMathSupport.Solomon.Proving.typeL2_card _ hT'
      have hle : Nat.card (↥(sesqSpecialUnitaryGroup B) ⧸
          Subgroup.center ↥(sesqSpecialUnitaryGroup B)) ≤ 216 := by
        rw [← h216]
        exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
      have h1 : 100 ≤ r * r := by nlinarith
      have h2 : r * 100 ≤ r * (r * r) := Nat.mul_le_mul_left r h1
      have h3 : r ^ 3 = r * (r * r) := by ring
      have h100 : 100 * r ≤ r ^ 3 := by rw [h3]; linarith
      rcases Nat.even_or_odd r with hev | hod
      · have := (heven hev).1
        omega
      · have := hodd hod
        omega
    · have hnq : ¬ (finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h) = 3 ∧
          ℓ ^ (f * d) = 2) := by
        rintro ⟨h3, h2⟩
        exact hexc ⟨h3, h2⟩
      exact t6psuh_not_isTypeL2_sesqSpecialUnitary hO hU hBsymm hBl (by rw [hm']; exact hm3) hnq
        hr hT'
  · have hne : h ≠ reciprocalPolynomial h := hself
    let b : Module.Basis (Fin (primaryMultiplicity x.toLinearMap h)) (AdjoinRoot h)
        (primaryComponent x.toLinearMap h) := Module.finBasisOfFinrankEq _ _ rfl
    let e₁ : ↥(specialBlock Q x h) ≃*
        SpecialLinearGroup (AdjoinRoot h) (primaryComponent x.toLinearMap h) :=
      MulEquiv.ofBijective (specialToSL Q x h)
        ⟨hx.specialToSL_injective hh, hx.specialToSL_surjective_paired hh hne⟩
    exact not_isTypeL2_specialLinear hO hm3 hr
      (p6_isTypeL2_of_equiv
        ((Matrix.SpecialLinearGroup.toLin_equiv b).trans e₁.symm).symm hT)

end CFSG.HardMathSupport.Dickson.Sec6.I1431.OrthL2
