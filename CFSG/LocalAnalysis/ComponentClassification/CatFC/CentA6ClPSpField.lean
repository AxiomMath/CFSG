module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSpModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDescent
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBDescent
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTIUnitarySocleForms

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBSymplecticB

theorem card_scalarSigns_le {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) :
    Nat.card ↥(CatalogueBAlternatingIsometry.isometryGroup B) ≠ 0 →
      Nat.card ↥(scalarSigns B) ≤ 2 := by
  intro _
  classical
  have : Nat.card ↥(scalarSigns B) ≤ Nat.card Bool := by
    refine Nat.card_le_card_of_injective (fun g => decide (g.1 = 1)) ?_
    intro g g' h
    apply Subtype.ext
    by_cases hg : g.1 = 1
    · have hg' : g'.1 = 1 := by simpa [hg] using h.symm
      rw [hg, hg']
    · have hg' : g'.1 ≠ 1 := by
        intro h'
        simp [hg, h'] at h
      rw [g.2.resolve_left hg, g'.2.resolve_left hg']
  simpa using this

open CFSG.ComponentClassification.CatalogueBAlternatingIsometry
  CFSG.LocalAnalysis.ComponentInitial SymplecticFlag SymplecticHigher in
theorem a6_field_false {r : ℕ} (hr : 2 ≤ r) {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 3 ^ f) {α : MulAut (StatedProj (StatedSp r K))} (A : gsp r K)
    (σ : K ≃+* K) (hα : α = conjAut r K A * fieldAut r K σ) (hσ2 : σ ^ 2 = 1) (hσ : σ ≠ 1)
    (d : Kˣ)
    (hd : (A : GL (Fin r ⊕ Fin r) K) *
      CatalogueBHigherLinearField.glFieldEquiv (Fin r ⊕ Fin r) σ A =
        Matrix.GeneralLinearGroup.scalar (Fin r ⊕ Fin r) d)
    {D : Subgroup (fixedSubgroup α)} (h : A6Hyp α D) : False := by
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
  have hSpq := LieType.Universal.Symplectic.isQuasisimple r
    (CatalogueBLinearTwoDescent.fixedSubfield K σ) hr1 (by
      by_cases h4 : 4 ≤ Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K σ)
      · exact Or.inl (Or.inr h4)
      · refine Or.inr (Or.inl ⟨?_, hr⟩)
        rw [hk]
        have h3 : 3 ≤ 3 ^ (f / 2) := Nat.le_self_pow (by omega) 3
        rw [hk] at h4
        omega)
  have hCq := LocalCores.isQuasisimple_of_mulEquiv Θ.symm hSpq
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
  have hperf : commutator ↥(fixedSubgroup (semilinearConjugation (pairedSympForm K r) σ
      (semilinearCoordMap (A : GL (Fin r ⊕ Fin r) K) σ) μ (semilinearCoordMap_smul _ σ)
      (semilinearCoordMap_form _ σ μ hμ))) = ⊤ := Group.isPerfect_def.mp hCq.1
  have h27 : 27 ∣ Nat.card ↥(fixedSubgroup (semilinearConjugation (pairedSympForm K r) σ
      (semilinearCoordMap (A : GL (Fin r ⊕ Fin r) K) σ) μ (semilinearCoordMap_smul _ σ)
      (semilinearCoordMap_form _ σ μ hμ))) := by
    rw [Nat.card_congr Θ.toEquiv]
    refine (pow_dvd_pow 3 (?_ : 3 ≤ f / 2 * r ^ 2)).trans (three_pow_dvd_card_statedSp hk)
    calc 3 ≤ 4 := by norm_num
      _ ≤ r ^ 2 := by nlinarith
      _ ≤ f / 2 * r ^ 2 := Nat.le_mul_of_pos_left _ hf2
  have := h.perfect_dvd φ hperf hker
  have h2' := h27.trans this
  revert h2'
  norm_num

end CFSG.ComponentClassification.CatFC
