module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2020OrthA1
public import CFSG.RankThree.PartOne.KC.OrthogonalBlockModels
public import CFSG.RankThree.PartOne.KC.LinearPlaneBlocks
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434ClOrth
public import CFSG.LocalAnalysis.GLTheoremA.S9.Basic
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorBasic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2020

open Polynomial Module CFSG.Open CFSG.Yardstones.Md0ec50421ce4
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal CFSG.GroupTheory
  CFSG.ComponentClassification.CatLeaf

variable {K V : Type} [Field K] [Fintype K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p q f : ℕ} {x : V ≃ₗ[K] V}

section Order

variable {h : K[X]}

private theorem card_pSimple_mul_two_of_sl2_model (hp : p.Prime) (hqodd : Odd q)
    (hqs : CFSG.IsQuasisimple ↥(specialBlock Q x h)) {X : Subgroup (ProjOrthDerived Q)}
    (hJ : GLAPComponent p X (componentImage Q x h)) {E : Type} [Field E] [Finite E] (f' : ℕ)
    (hE : Nat.card E = q ^ f')
    (eSL : ↥(specialBlock Q x h) ≃* Matrix.SpecialLinearGroup (Fin 2) E) :
    Nat.card (PSimple p (componentImage Q x h)) * 2 = q ^ f' * ((q ^ f') ^ 2 - 1) := by
  classical
  letI : Fintype E := Fintype.ofFinite E
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  haveI : Finite (ProjOrthDerived Q) := inferInstance
  have hle : specialBlock Q x h ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    (specialBlock_le_isometryCentralizer h).trans fun _ hg => (Subgroup.mem_inf.mp hg).1
  have hΩ : specialBlock Q x h ≤ orthDerived Q :=
    specialBlock_le_orthDerived_of_perfect hqs.1 hle
  have hqJ : CFSG.IsQuasisimple ↥(componentImage Q x h) :=
    isQuasisimple_map_projective hΩ hqs
  have hqJ' : CFSG.Open.IsQuasisimple ↥(componentImage Q x h) :=
    ⟨hqJ.1.commutator_eq_top, hqJ.2.1⟩
  obtain ⟨ePS⟩ := CFSG.LocalAnalysis.GLTheoremA.S9.nonempty_pSimple_equiv hp hJ hqJ'
  have hc : Nat.card (↥(componentImage Q x h) ⧸
      Subgroup.center ↥(componentImage Q x h)) =
      Nat.card (↥(specialBlock Q x h) ⧸ Subgroup.center ↥(specialBlock Q x h)) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434.Cl.card_quotient_center_map_projective
      hΩ hqs.1.commutator_eq_top
  have hoddE : Odd (Nat.card E) := by
    rw [hE]
    exact hqodd.pow
  have hF2 : ringChar E ≠ 2 := by
    intro h2
    have hEven : Fintype.card E % 2 = 0 := FiniteField.even_card_iff_char_two.mp h2
    rw [← Nat.card_eq_fintype_card] at hEven
    obtain ⟨k, hk⟩ := hoddE
    omega
  have hcard : Nat.card (PSimple p (componentImage Q x h)) =
      Nat.card (↥(specialBlock Q x h) ⧸ Subgroup.center ↥(specialBlock Q x h)) :=
    (Nat.card_congr ePS.toEquiv).trans hc
  have htwo : 2 * Nat.card (↥(specialBlock Q x h) ⧸
      Subgroup.center ↥(specialBlock Q x h)) = Nat.card E * (Nat.card E ^ 2 - 1) :=
    CFSG.ComponentClassification.ExcSelector.two_mul_card_centralQuotient_of_equiv_sl2 hF2 eSL
  calc
    Nat.card (PSimple p (componentImage Q x h)) * 2
        = Nat.card (↥(specialBlock Q x h) ⧸
            Subgroup.center ↥(specialBlock Q x h)) * 2 := by rw [hcard]
    _ = 2 * Nat.card (↥(specialBlock Q x h) ⧸
        Subgroup.center ↥(specialBlock Q x h)) := by rw [mul_comm]
    _ = Nat.card E * (Nat.card E ^ 2 - 1) := htwo
    _ = q ^ f' * ((q ^ f') ^ 2 - 1) := by rw [hE]

theorem card_pSimple_componentImage_of_mult_two (hp : p.Prime) (hp2 : p ≠ 2) (hq : q.Prime)
    (hq2 : q ≠ 2) (hring : ringChar K = q) (hcardK : Nat.card K = q ^ f)
    (hx : OddOrderIsometry Q p x) {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap)
    (hne1 : h ≠ X - 1) (hm : primaryMultiplicity x.toLinearMap h = 2)
    (hqs : CFSG.IsQuasisimple ↥(specialBlock Q x h)) {X : Subgroup (ProjOrthDerived Q)}
    (hJ : GLAPComponent p X (componentImage Q x h)) :
    ∃ f' : ℕ, 1 ≤ f' ∧ Nat.card (PSimple p (componentImage Q x h)) * 2 =
      (q ^ f') * ((q ^ f') ^ 2 - 1) := by
  classical
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hqodd : Odd q := hq.odd_of_ne_two hq2
  have hf1 : 1 ≤ f := by
    by_contra hf
    have hf0 : f = 0 := by omega
    rw [hf0, pow_zero] at hcardK
    have h2 : 1 < Nat.card K := Finite.one_lt_card
    omega
  by_cases hself : h = reciprocalPolynomial h
  · obtain ⟨ℓ, e, hU, ⟨eSL⟩⟩ :=
      hx.exists_specialBlock_mulEquiv_SL2_selfDual hp hp2 hh hne1 hself hm
    have hℓ : ℓ = q := by
      have h1 : ringChar (AdjoinRoot h) = ℓ := @ringChar.eq (AdjoinRoot h) _ ℓ hU.charP
      have h2 : ringChar K = ringChar (AdjoinRoot h) := Algebra.ringChar_eq K (AdjoinRoot h)
      omega
    have hE : Nat.card hU.fixedField = q ^ e := by
      rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.card_fixedField, hℓ]
    exact ⟨e, hU.one_le,
      card_pSimple_mul_two_of_sl2_model (f' := e) hp hqodd hqs hJ hE eSL⟩
  · obtain ⟨eSL⟩ := hx.nonempty_specialBlock_mulEquiv_SL_paired hh hself
    have eSL' : ↥(specialBlock Q x h) ≃*
        Matrix.SpecialLinearGroup (Fin 2) (AdjoinRoot h) := by
      have hm' : primaryMultiplicity (x : Module.End K V) h = 2 := hm
      rw [hm'] at eSL
      exact eSL
    have hdeg : 1 ≤ h.natDegree := (irreducible_of_mem_primaryFactors hh).natDegree_pos
    have hE : Nat.card (AdjoinRoot h) = q ^ (f * h.natDegree) := by
      rw [CFSG.RankThree.PartOne.KCLinPlane.natCard_adjoinRoot, hcardK, ← pow_mul]
    exact ⟨f * h.natDegree, Nat.mul_pos hf1 hdeg,
      card_pSimple_mul_two_of_sl2_model (f' := f * h.natDegree) hp hqodd hqs hJ hE eSL'⟩

end Order

section Cert


theorem not_jType_componentImage_of_mult_two' (hp : p.Prime) (hp2 : p ≠ 2) (hq : q.Prime)
    (hq2 : q ≠ 2) (hring : ringChar K = q) (hcardK : Nat.card K = q ^ f)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (hx : OddOrderIsometry Q p x) {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap)
    (hne1 : h ≠ X - 1) (hm : primaryMultiplicity x.toLinearMap h = 2)
    (hqs : CFSG.IsQuasisimple ↥(specialBlock Q x h)) {X : Subgroup (ProjOrthDerived Q)}
    (hJ : GLAPComponent p X (componentImage Q x h)) :
    ¬ JType p q (componentImage Q x h) :=
  not_jType_componentImage_of_mult_two hp hp2 hq hq2 hring hcardK hQ hT hx hh hne1 hm hqs
    (card_pSimple_componentImage_of_mult_two hp hp2 hq hq2 hring hcardK hx hh hne1 hm hqs hJ)

end Cert

end CFSG.LocalAnalysis.GLTheoremA.I2020
