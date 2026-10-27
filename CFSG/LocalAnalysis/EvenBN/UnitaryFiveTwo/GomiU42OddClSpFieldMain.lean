module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClSpField
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSpField
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddCl
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClDisp
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClSpArith

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.CatalogueBSymplecticB
open CFSG.ComponentClassification.CatalogueBAlternatingIsometry
open CFSG.ComponentClassification.CatFC
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

theorem u42_sp_field_false {r : ℕ} (hr : 2 ≤ r) {K : Type} [Field K] [Finite K] {f : ℕ}
    (hf : 1 ≤ f) (hK : Nat.card K = 3 ^ f) {α : MulAut (StatedProj (StatedSp r K))}
    (A : gsp r K) (σ : K ≃+* K) (hα : α = conjAut r K A * fieldAut r K σ) (hσ2 : σ ^ 2 = 1)
    (hσ : σ ≠ 1) (d : Kˣ)
    (hd : (A : GL (Fin r ⊕ Fin r) K) *
      CatalogueBHigherLinearField.glFieldEquiv (Fin r ⊕ Fin r) σ A =
        Matrix.GeneralLinearGroup.scalar (Fin r ⊕ Fin r) d)
    (hout : α ∉ inner (StatedProj (StatedSp r K)))
    {J : Subgroup ↥(fixedSubgroup α)} (h : U42Hyp α J) : False := by
  have : CharP K 3 := finite_field_prime_power_characteristic Nat.prime_three hf hK
  have hchar : ringChar K ≠ 2 := by
    rw [ringChar.eq K 3]
    norm_num
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hchar
  have hr1 : 1 ≤ r := by omega
  set μ := multiplierUnit A with hμdef
  have hμ := multiplierUnit_spec A
  let e := projectiveStatedEquiv (K := K) hr1
  have hint : ∀ x, e (α x) = projectiveSemilinearConjugation (pairedSympForm K r) σ
      (semilinearCoordMap (A : GL (Fin r ⊕ Fin r) K) σ) μ (semilinearCoordMap_smul _ σ)
      (semilinearCoordMap_form _ σ μ hμ) (e x) := by
    intro x
    rw [hα]
    exact projectiveStatedEquiv_conjAut_fieldAut hr1 A σ μ hμ x
  let Φ := CatalogueBOrthogonalFixedTransfer.fixedEquivOfIntertwining e α _ hint
  have hdim : 0 < Module.finrank K (Fin r ⊕ Fin r → K) := by
    rw [SymplecticFlag.finrank_standard]
    omega
  obtain ⟨-, -, -, ⟨b, c, hb, hc⟩, hall⟩ := odd_symplectic_quadratic_semilinear_descent σ hσ2 hσ
    h2 hdim (pairedSympForm K r) SymplecticFlag.pairedSympForm_isAlt
    SymplecticFlag.pairedSympForm_nondegenerate
    (semilinearCoordMap (A : GL (Fin r ⊕ Fin r) K) σ) μ d (semilinearCoordMap_smul _ σ)
    (semilinearCoordMap_form _ σ μ hμ) (semilinearCoordMap_sq _ σ hσ2 d hd)
  obtain ⟨-, -, -, -, hWfin, hWdim, -, halt, hnd, -, eC, -⟩ := hall b c hb hc
  have hcard := CatalogueBHigherLinearField.fixedField_card_square K σ hσ2 hσ
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1
    (show Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K σ) ∣ 3 ^ f from
      hK ▸ hcard ▸ dvd_pow_self _ two_ne_zero)
  have hfj : f = 2 * j := by
    have h1 : 3 ^ f = 3 ^ (2 * j) := by
      rw [← hK, hcard]
      change Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K σ) ^ 2 = _
      rw [hj, ← pow_mul, mul_comm]
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h1
  have hk : Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K σ) = 3 ^ (f / 2) := by
    rw [hj, hfj, Nat.mul_div_cancel_left _ two_pos]
  have hf2 : 1 ≤ f / 2 := by
    rw [hfj, Nat.mul_div_cancel_left _ two_pos]
    by_contra h0
    have hj0 : j = 0 := by omega
    rw [hj0, mul_zero] at hfj
    omega
  have hdim' := hWdim.trans SymplecticFlag.finrank_standard
  obtain ⟨eSp⟩ := OutcomeLocal.nonempty_altIsometry_mulEquiv_statedSp _ halt hnd hdim'
  let Θ := (semilinearFixedCentralizerEquiv (pairedSympForm K r) σ
    (semilinearCoordMap (A : GL (Fin r ⊕ Fin r) K) σ) μ (semilinearCoordMap_smul _ σ)
    (semilinearCoordMap_form _ σ μ hμ)).trans (eC.trans eSp)
  have hQfin : Finite ↥(fixedSubgroup (semilinearConjugation (pairedSympForm K r) σ
      (semilinearCoordMap (A : GL (Fin r ⊕ Fin r) K) σ) μ (semilinearCoordMap_smul _ σ)
      (semilinearCoordMap_form _ σ μ hμ))) :=
    Finite.of_equiv _ Θ.symm.toEquiv
  let π₀ := CatalogueBFixedCentralQuotient.fixedProjection (scalarSigns (pairedSympForm K r))
    (semilinearConjugation (pairedSympForm K r) σ
      (semilinearCoordMap (A : GL (Fin r ⊕ Fin r) K) σ) μ (semilinearCoordMap_smul _ σ)
      (semilinearCoordMap_form _ σ μ hμ))
    (semilinear_scalarSigns_invariant _ σ _ μ _ _)
  let φ := Φ.symm.toMonoidHom.comp π₀
  have hcardSigns : Nat.card ↥(scalarSigns (pairedSympForm K r)) ≤ 2 := by
    refine card_scalarSigns_le _ ?_
    rw [Nat.card_congr (statedSpIsometryEquiv (r := r) (K := K)).toEquiv.symm]
    exact Nat.card_pos.ne'
  have hker : Nat.card ↥φ.ker ≤ 2 := by
    refine le_trans (Nat.card_le_card_of_injective
      (fun x : ↥φ.ker => (⟨x.1.1, ?_⟩ : ↥(scalarSigns (pairedSympForm K r)))) ?_) hcardSigns
    · have hx : π₀ x.1 = 1 := by
        have h1 : Φ.symm (π₀ x.1) = 1 := x.2
        exact (map_eq_one_iff Φ.symm Φ.symm.injective).1 h1
      have hx' : x.1 ∈ π₀.ker := hx
      rw [CatalogueBFixedCentralQuotient.fixedProjection_kernel] at hx'
      exact hx'
    · intro x x' hxx
      have h1 := congrArg Subtype.val hxx
      exact Subtype.ext (Subtype.ext h1)
  have hdvdQ : Nat.card ↥(fixedSubgroup (semilinearConjugation (pairedSympForm K r) σ
      (semilinearCoordMap (A : GL (Fin r ⊕ Fin r) K) σ) μ (semilinearCoordMap_smul _ σ)
      (semilinearCoordMap_form _ σ μ hμ))) ∣ 103680 := by
    have h1 := h.card_dvd_mul φ
    have h3 : 0 < Nat.card ↥φ.ker := Nat.card_pos
    have h4 : Nat.card ↥φ.ker = 1 ∨ Nat.card ↥φ.ker = 2 := by omega
    rcases h4 with h4 | h4 <;> rw [h4] at h1
    · exact h1.trans (by norm_num)
    · exact h1
  have h3pow : 3 ^ (f / 2 * r ^ 2) ∣ Nat.card ↥(fixedSubgroup (semilinearConjugation
      (pairedSympForm K r) σ (semilinearCoordMap (A : GL (Fin r ⊕ Fin r) K) σ) μ
      (semilinearCoordMap_smul _ σ) (semilinearCoordMap_form _ σ μ hμ))) := by
    rw [Nat.card_congr Θ.toEquiv]
    exact three_pow_dvd_card_statedSp hk
  by_cases hbig : 5 ≤ f / 2 * r ^ 2
  · exact not_dvd_103680_of_three_pow_five ((pow_dvd_pow 3 hbig).trans h3pow) hdvdQ
  push Not at hbig
  have hr2 : r = 2 := by
    by_contra hne
    have : 3 ≤ r := by omega
    nlinarith
  have hf21 : f / 2 = 1 := by
    rw [hr2] at hbig
    omega
  have hk3 : Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K σ) = 3 := by
    rw [hk, hf21]; norm_num
  have hQcard : Nat.card ↥(fixedSubgroup (semilinearConjugation (pairedSympForm K r) σ
      (semilinearCoordMap (A : GL (Fin r ⊕ Fin r) K) σ) μ (semilinearCoordMap_smul _ σ)
      (semilinearCoordMap_form _ σ μ hμ))) = 51840 := by
    rw [Nat.card_congr Θ.toEquiv, hr2, card_statedSp_two, hk3]
    norm_num
  obtain ⟨g, hg⟩ := exists_isometry_conj_eq_neg (pairedSympForm K r)
    SymplecticFlag.pairedSympForm_isAlt SymplecticFlag.pairedSympForm_nondegenerate σ hσ2 hσ h2
    (semilinearCoordMap (A : GL (Fin r ⊕ Fin r) K) σ) μ d b c (semilinearCoordMap_smul _ σ)
    (semilinearCoordMap_form _ σ μ hμ) (semilinearCoordMap_sq _ σ hσ2 d hd) hb hc
  haveI : Finite ↥(isometryGroup (pairedSympForm K r)) :=
    Finite.of_equiv _ (statedSpIsometryEquiv (r := r) (K := K)).toEquiv
  have hne1 : negIsometry (pairedSympForm K r) ≠ 1 := by
    intro h1
    have h3 := congrArg (fun g : isometryGroup (pairedSympForm K r) =>
      g.val (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin r)) (1 : K))) h1
    have h4 := congrFun h3 (Sum.inl (⟨0, by omega⟩ : Fin r))
    simp [negIsometry_apply] at h4
    exact h2 (by linear_combination (-1 : K) * h4)
  have hZ2 : Nat.card ↥(scalarSigns (pairedSympForm K r)) = 2 := by
    rw [Nat.card_eq_two_iff]
    refine ⟨⟨1, Or.inl rfl⟩, ⟨negIsometry (pairedSympForm K r), Or.inr rfl⟩, ?_, ?_⟩
    · intro h1
      exact hne1 (congrArg Subtype.val h1).symm
    · ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      rcases z.2 with h1 | h1
      · exact Or.inl (Subtype.ext h1)
      · exact Or.inr (Subtype.ext h1)
  have hdisp := card_fixed_onQuotient_eq_of_displacement (scalarSigns (pairedSympForm K r))
    (scalarSigns_central (pairedSympForm K r)) (semilinearConjugation (pairedSympForm K r) σ
      (semilinearCoordMap (A : GL (Fin r ⊕ Fin r) K) σ) μ (semilinearCoordMap_smul _ σ)
      (semilinearCoordMap_form _ σ μ hμ)) (semilinear_scalarSigns_invariant _ σ _ μ _ _) hZ2
    (x := g) (z := negIsometry (pairedSympForm K r)) (Or.inr rfl) hne1 hg
  have h25920 := h.card_outer hout
  rw [Nat.card_congr Φ.toEquiv] at h25920
  have hdisp' : Nat.card ↥(fixedSubgroup (projectiveSemilinearConjugation (pairedSympForm K r) σ
      (semilinearCoordMap (A : GL (Fin r ⊕ Fin r) K) σ) μ (semilinearCoordMap_smul _ σ)
      (semilinearCoordMap_form _ σ μ hμ))) = 51840 := hdisp.trans hQcard
  omega

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
