module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClOmBase
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClOmOrd
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDescent
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClOmArith

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank Module
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed
open CFSG.ComponentClassification.CatalogueBOrthogonalFixedTransfer
open CFSG.LocalAnalysis.ComponentInitial (finite_field_prime_power_characteristic)

open CatalogueBOrthogonalDescent CatalogueBLinearTwoDescent CatalogueBOrthogonalFieldFixed in
theorem u42_omega_field_false {K : Type} [Field K] [Finite K] {d f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 3 ^ f) (hd : 7 ≤ d) {Q : QuadraticForm K (Fin d → K)}
    (hQ : Q.polarBilin.Nondegenerate) (hidx : (orthogonalDerived Q).index = 4)
    (g : similarityPairs Q) (hσ2 : g.val.right ^ 2 = 1) (hσ : g.val.right ≠ 1) (c : Kˣ)
    (hc : g.val.left * CatalogueBHigherLinearField.glFieldAut (Fin d) K g.val.right g.val.left =
      Matrix.GeneralLinearGroup.scalar (Fin d) c)
    {J : Subgroup (fixedSubgroup (matrixProjectiveConjugationHom Q g))}
    (hJ : U42Hyp (matrixProjectiveConjugationHom Q g) J) : False := by
  have : CharP K 3 := finite_field_prime_power_characteristic Nat.prime_three hf hK
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K 3]; norm_num)
  have hd0 : 0 < d := by omega
  have : Nontrivial (Fin d → K) :=
    Module.nontrivial_of_finrank_pos (R := K) (by rw [Module.finrank_fin_fun]; exact hd0)
  set σ := g.val.right with hσdef
  set τ₀ := coordinateSemilinearMap g.val with hτ₀
  set μ := multiplier Q g with hμ
  have hsemi : ∀ a x, τ₀ (a • x) = σ a • τ₀ x := coordinateSemilinearMap_smul g.val
  have hsim : ∀ x, Q (τ₀ x) = (μ : K) * σ (Q x) := multiplier_spec Q g
  have hsquare : ∀ x, τ₀ (τ₀ x) = (c : K) • x := coordinateSemilinearMap_sq_apply g.val c hσ2 hc
  have hex := exists_ne_zero_of_polarBilin_nondegenerate Q hQ hd0
  haveI : Finite (matrixProjectiveDerived Q) := by
    haveI := u42_finite_orthogonalGroup Q
    exact Finite.of_equiv _ (projectiveEquiv Q hex).symm.toEquiv
  obtain ⟨J', hJ'⟩ := U42Hyp.of_intertwining (projectiveEquiv Q hex) _ _
    (projectiveEquiv_conjugation Q hex g) hJ
  have hbounds := u42_omega_fixed_bounds Q h2 hidx (semilinearConjugation Q σ τ₀ μ hsemi hsim)
    (semilinear_orthogonalDerived_invariant Q σ τ₀ μ hsemi hsim)
    (semilinear_scalarSigns_invariant Q σ τ₀ μ hsemi hsim) hJ'
  have hsym : LinearMap.BilinForm.IsSymm Q.polarBilin :=
    ⟨fun x y => QuadraticMap.polar_comm Q x y⟩
  have hform := semilinear_polar_similarity Q σ τ₀ μ hsim
  have hfixed := square_scalar_fixed σ τ₀ (c : K) hsemi hsquare
  have hmu := square_multiplier_identity σ hσ2 Q.polarBilin hQ τ₀ (μ : K) (c : K) hform hsquare
  obtain ⟨b, c', hb, hc'⟩ := exists_normalizing_units σ hσ2 hσ μ c hfixed hmu
  let T := normalizedOperator τ₀ b
  let hs := normalizedOperator_semilinear σ τ₀ b hsemi
  let hf' := normalized_form_identity σ Q.polarBilin τ₀ μ b c' hform hc'
  have hT := normalizedOperator_involutive σ τ₀ c b hsemi hsquare hb
  let : Module.Finite (fixedSubfield K σ) (fixedSubspace σ T hs) := by
    obtain ⟨e, d', hd'⟩ := exists_fixedSpace_basis σ hσ2 hσ h2 T hT hs
    exact Module.Finite.of_basis d'
  have hnd := descendedBilinear_nondegenerate σ T hs Q.polarBilin c' hf' hσ2 hσ h2 hT hsym hQ
  have hQ0 : (descendedQuadratic σ T hs Q.polarBilin c' hf').polarBilin.Nondegenerate := by
    rw [descendedQuadratic_polarBilin σ T hs Q.polarBilin c' hf' hsym h2]
    exact hnd
  let e : semilinearOrthogonalCentralizer Q τ₀ ≃*
      TauCeti.QuadraticMap.orthogonalGroup
        (originalDescendedQuadratic σ τ₀ b hsemi Q.polarBilin μ c' hform hc') := by
    exact Eq.ndrec (motive := fun R : QuadraticForm K (Fin d → K) =>
      semilinearOrthogonalCentralizer R τ₀ ≃*
        TauCeti.QuadraticMap.orthogonalGroup
          (originalDescendedQuadratic σ τ₀ b hsemi Q.polarBilin μ c' hform hc'))
      (originalDescentCentralizerEquiv σ τ₀ b hsemi Q.polarBilin μ c' hform hc'
        hσ2 hσ h2 hsym c hsquare hb) (originalQuadratic_polar_eq Q h2)
  let Θ := (semilinearFixedCentralizerEquiv Q σ τ₀ μ hsemi hsim).trans e
  have hcard := CatalogueBHigherLinearField.fixedField_card_square K σ hσ2 hσ
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1
    (show Nat.card (fixedSubfield K σ) ∣ 3 ^ f from
      hK ▸ hcard ▸ dvd_pow_self _ two_ne_zero)
  have hfj : f = 2 * j := by
    have h1 : 3 ^ f = 3 ^ (2 * j) := by
      rw [← hK, hcard]
      change Nat.card (fixedSubfield K σ) ^ 2 = _
      rw [hj, ← pow_mul, mul_comm]
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h1
  have hk : Nat.card (fixedSubfield K σ) = 3 ^ (f / 2) := by
    rw [hj, hfj, Nat.mul_div_cancel_left _ two_pos]
  have hf2 : 1 ≤ f / 2 := by omega
  have hdimW : finrank (fixedSubfield K σ) (fixedSubspace σ T hs) = d := by
    rw [fixedSubspace_finrank σ hσ2 hσ h2 T hT hs, Module.finrank_fin_fun]
  have d3 := u42_three_pow_dvd_card_orthogonalGroup (K := fixedSubfield K σ)
    (W := fixedSubspace σ T hs) hf2 hk hQ0 hdimW hd0
  rw [← Nat.card_congr Θ.toEquiv] at d3
  have hexp : 5 ≤ f / 2 * ((d - 1) ^ 2 / 4) := by
    have : 9 ≤ (d - 1) ^ 2 / 4 := by
      rw [Nat.le_div_iff_mul_le (by norm_num)]
      obtain ⟨s, rfl⟩ : ∃ s, d = s + 7 := ⟨d - 7, by omega⟩
      rw [show s + 7 - 1 = s + 6 by omega]
      nlinarith
    nlinarith
  exact not_dvd_414720_of_three_pow_five ((pow_dvd_pow 3 hexp).trans d3) hbounds.2.1

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
