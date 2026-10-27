module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofA6PSpInner
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofA6Split

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

open CFSG.ComponentClassification.CatalogueBSymplecticB
  CFSG.ComponentClassification.CatalogueBAlternatingIsometry
  CFSG.LocalAnalysis.ComponentInitial SymplecticFlag SymplecticHigher in
theorem a6_psp_field
    {r : ℕ} (hr : 2 ≤ r) {K : Type} [Field K] [Finite K]
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f)
    {α : MulAut (StatedProj (StatedSp r K))} (A : gsp r K) (σ : K ≃+* K)
    (hα : α = conjAut r K A * fieldAut r K σ) (hσ2 : σ ^ 2 = 1) (hσ : σ ≠ 1) (d : Kˣ)
    (hd : (A : GL (Fin r ⊕ Fin r) K) *
      CatalogueBHigherLinearField.glFieldEquiv (Fin r ⊕ Fin r) σ A =
        Matrix.GeneralLinearGroup.scalar (Fin r ⊕ Fin r) d)
    : A6CentreForm (fixedSubgroup α) := by
  intro L hL
  show A6Safe L
  have : CharP K p := finite_field_prime_power_characteristic hp hf hK
  have hchar : ringChar K ≠ 2 := by
    rw [ringChar.eq K p]
    exact hp2
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
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1
    (show Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K σ) ∣ p ^ f from
      hK ▸ hcard ▸ dvd_pow_self _ two_ne_zero)
  have hfj : f = 2 * j := by
    have h1 : p ^ f = p ^ (2 * j) := by
      rw [← hK, hcard]
      change Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K σ) ^ 2 = _
      rw [hj, ← pow_mul, mul_comm]
    exact Nat.pow_right_injective hp.two_le h1
  have hk : Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K σ) = p ^ (f / 2) := by
    rw [hj, hfj, Nat.mul_div_cancel_left _ two_pos]
  have hf2 : 1 ≤ f / 2 := by
    rw [hfj, Nat.mul_div_cancel_left _ two_pos]
    by_contra h0
    have hj0 : j = 0 := by omega
    rw [hj0, mul_zero] at hfj
    omega
  have hadm : StatedLieAdmissible .PSp r p (f / 2) := by
    refine ⟨hp, hf2, hr, fun h => ?_⟩
    have h1 : p ^ (f / 2) = 2 := (Prod.mk.inj h).2
    have hodd : Odd (p ^ (f / 2)) := (hp.eq_two_or_odd'.resolve_left hp2).pow
    rw [h1] at hodd
    exact absurd hodd (by decide)
  have hdim' := hWdim.trans SymplecticFlag.finrank_standard
  obtain ⟨eSp⟩ := OutcomeLocal.nonempty_altIsometry_mulEquiv_statedSp _ halt hnd hdim'
  let Θ := (semilinearFixedCentralizerEquiv (pairedSympForm K r) σ
    (semilinearCoordMap (A : GL (Fin r ⊕ Fin r) K) σ) μ (semilinearCoordMap_smul _ σ)
    (semilinearCoordMap_form _ σ μ hμ)).trans (eC.trans eSp)
  have hSpq := LieType.Universal.Symplectic.isQuasisimple_of_admissible r
    (CatalogueBLinearTwoDescent.fixedSubfield K σ) hadm hk
  have hCq := LocalCores.isQuasisimple_of_mulEquiv Θ.symm hSpq
  have hL' := LocalCores.isComponent_map_mulEquiv Φ hL
  obtain ⟨eZ⟩ := nonempty_centerQuotient_equiv_of_quotientFixed (scalarSigns (pairedSympForm K r))
    (scalarSigns_central _) _ (semilinear_scalarSigns_invariant _ σ _ μ _ _) hCq hL'
  let eL := L.equivMapOfInjective Φ.toMonoidHom Φ.injective
  let eTot : L ⧸ center L ≃*
      StatedSp r (CatalogueBLinearTwoDescent.fixedSubfield K σ) ⧸
        center (StatedSp r (CatalogueBLinearTwoDescent.fixedSubfield K σ)) :=
    ((QuotientGroup.congr _ _ eL (Subgroup.map_center_eq eL)).trans eZ).trans
      (QuotientGroup.congr _ _ Θ (Subgroup.map_center_eq Θ))
  exact a6Safe_of_quotient_lieModel eTot hadm hp2
    (Or.inl ⟨by decide, LieType.Universal.Symplectic.statedClassicalModel_center_quotient r _ hadm
      hk⟩) fun h => absurd h.1 (by decide)

open CFSG.LocalAnalysis.ComponentInitial SymplecticHigher in
theorem oddLieA6CentreFor_PSp
    : OddLieA6CentreFor .PSp := by
  intro J _ n p f hp hp2 hadm hm α hα
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_psp_of_lieModel' hadm hm
  have hf : 1 ≤ f := hadm.2.1
  have hn : 2 ≤ n := hadm.2.2.1
  have : CharP K p := finite_field_prime_power_characteristic hp hf hK
  have hchar : ringChar K ≠ 2 := by
    rw [ringChar.eq K p]
    exact hp2
  have hβ : orderOf (MulAut.congr e α) = 2 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective α).trans hα
  have hβ2 : MulAut.congr e α * MulAut.congr e α = 1 := by
    have h2 := pow_orderOf_eq_one (MulAut.congr e α)
    rw [hβ] at h2
    rw [← pow_two]
    exact h2
  have hβ1 : MulAut.congr e α ≠ 1 := fun h => by
    rw [h, orderOf_one] at hβ
    exact absurd hβ (by norm_num)
  obtain ⟨A, σ, hAσ, hσ2, ⟨d, hd⟩, -, -⟩ :=
    (CatalogueBSymplecticRepresentation.odd_symplectic_automorphism_semilinear_representation
      hchar hn).2.2 _ hβ2 hβ1
  refine a6CentreForm_of_mulEquiv (fixedSubgroupCongrEquiv e α) ?_
  by_cases hσ : σ = 1
  · subst hσ
    rw [map_one, mul_one] at hAσ
    have hord : orderOf (conjAut n K A) = 2 := hAσ ▸ hβ
    exact a6CentreForm_of_mulEquiv (MulEquiv.subgroupCongr (congrArg fixedSubgroup hAσ))
      (a6_inner_psp hp hp2 hK hadm A hord)
  · exact a6_psp_field hn hp hp2 hf hK A σ hAσ hσ2 hσ d hd

end CFSG.ComponentClassification.CatLeafProof
