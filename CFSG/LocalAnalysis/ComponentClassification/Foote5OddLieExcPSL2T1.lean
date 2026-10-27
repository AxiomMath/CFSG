module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneX10T1Desc
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcPSL2Ord

public noncomputable section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.Exc

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof
open CFSG.RankThree.PartOne.KCOrthogonalDescent CFSG.RankThree.Classical2
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.ToralSign CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped MatrixGroups
open CFSG.ComponentClassification.Burgoyne.X10

open CatalogueBOrthogonalDescent CatalogueBLinearTwoDescent CatalogueBOrthogonalFieldFixed
  CatalogueBOrthogonalLinearFixed CatalogueBOrthogonalFixedTransfer in
theorem noPSL2Odd_omega_field_ten (hO : LieOrderFormulasInput) {K : Type} [Field K] [Finite K]
    {d p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) (hdim : d = 2 * 5)
    {Q : QuadraticForm K (Fin d → K)} (hQ : Q.polarBilin.Nondegenerate)
    (g : similarityPairs Q) (hσ2 : g.val.right ^ 2 = 1) (hσ : g.val.right ≠ 1) (c : Kˣ)
    (hc : g.val.left * CatalogueBHigherLinearField.glFieldAut (Fin d) K g.val.right g.val.left =
      Matrix.GeneralLinearGroup.scalar (Fin d) c)
    {L : Subgroup (fixedSubgroup (matrixProjectiveConjugationHom Q g))} (hL : IsComponent L) :
    NoPSL2Odd L := by
  have : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K p]; exact hp2)
  have hd : 0 < d := by omega
  have : Nontrivial (Fin d → K) :=
    Module.nontrivial_of_finrank_pos (R := K) (by rw [Module.finrank_fin_fun]; exact hd)
  set σ := g.val.right with hσdef
  set τ₀ := coordinateSemilinearMap g.val with hτ₀
  set μ := multiplier Q g with hμ
  have hsemi : ∀ a x, τ₀ (a • x) = σ a • τ₀ x := coordinateSemilinearMap_smul g.val
  have hsim : ∀ x, Q (τ₀ x) = (μ : K) * σ (Q x) := multiplier_spec Q g
  have hsquare : ∀ x, τ₀ (τ₀ x) = (c : K) • x := coordinateSemilinearMap_sq_apply g.val c hσ2 hc
  let Φ := semilinearFixedEquiv Q (exists_ne_zero_of_polarBilin_nondegenerate Q hQ hd) g
  have hL' := LocalCores.isComponent_map_mulEquiv Φ hL
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
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1
    (show Nat.card (fixedSubfield K σ) ∣ p ^ f from
      hK ▸ hcard ▸ dvd_pow_self _ two_ne_zero)
  have hfj : f = 2 * j := by
    have h1 : p ^ f = p ^ (2 * j) := by
      rw [← hK, hcard]
      change Nat.card (fixedSubfield K σ) ^ 2 = _
      rw [hj, ← pow_mul, mul_comm]
    exact Nat.pow_right_injective hp.two_le h1
  have hk : Nat.card (fixedSubfield K σ) = p ^ (f / 2) := by
    rw [hj, hfj, Nat.mul_div_cancel_left _ two_pos]
  have hf2 : 1 ≤ f / 2 := by omega
  have hdimW : Module.finrank (fixedSubfield K σ) (fixedSubspace σ T hs) = 2 * 5 := by
    rw [fixedSubspace_finrank σ hσ2 hσ h2 T hT hs, Module.finrank_fin_fun]
    exact hdim
  obtain ⟨hΩq, τ', hτ', hadm, hlie⟩ := orthogonal_derived_lieModel_even hp hp2 hf2 hk
    (originalDescendedQuadratic σ τ₀ b hsemi Q.polarBilin μ c' hform hc') hQ0 hdimW (by norm_num)
  have hD : IsQuasisimple (commutator (fixedSubgroup
      (semilinearConjugation Q σ τ₀ μ hsemi hsim))) :=
    LocalCores.isQuasisimple_of_mulEquiv (commutatorEquiv Θ).symm hΩq
  have hDN : ∀ x ∈ commutator (fixedSubgroup (semilinearConjugation Q σ τ₀ μ hsemi hsim)),
      (x : TauCeti.QuadraticMap.orthogonalGroup Q) ∈ orthogonalDerived Q := by
    intro x hx
    have h1 : (x : TauCeti.QuadraticMap.orthogonalGroup Q) ∈
        (commutator (fixedSubgroup (semilinearConjugation Q σ τ₀ μ hsemi hsim))).map
          (fixedSubgroup (semilinearConjugation Q σ τ₀ μ hsemi hsim)).subtype :=
      Subgroup.mem_map_of_mem _ hx
    rw [map_commutator_eq, Subgroup.range_subtype] at h1
    exact Subgroup.commutator_mono le_top le_top h1
  obtain ⟨eZ⟩ := nonempty_centerQuotient_equiv_of_normalQuotientFixed (orthogonalDerived Q)
    (scalarSigns Q) (scalarSigns_central Q) (semilinearConjugation Q σ τ₀ μ hsemi hsim)
    (semilinear_orthogonalDerived_invariant Q σ τ₀ μ hsemi hsim)
    (semilinear_scalarSigns_invariant Q σ τ₀ μ hsemi hsim) hDN hD hL'
  let eL := L.equivMapOfInjective Φ.toMonoidHom Φ.injective
  let eTot := ((QuotientGroup.congr _ _ eL (Subgroup.map_center_eq eL)).trans eZ).trans
    (QuotientGroup.congr _ _ (commutatorEquiv Θ) (Subgroup.map_center_eq (commutatorEquiv Θ)))
  have hct : ExcCompTag τ' 5 := by
    rcases hτ' with rfl | rfl <;> (unfold ExcCompTag; decide)
  exact noPSL2Odd_of_lieModel hO hp2 hct (fun h => absurd h.2 (by norm_num)) hadm
    (LieType.CurtisTits.lieModel_of_mulEquiv eTot.symm hlie)

theorem noPSL2Odd_of_root_fixed (hO : LieOrderFormulasInput) {K : Type} [Field K] [Finite K]
    {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f)
    (α : MulAut (matrixProjectiveDerived (coordinateQuadPlus 5 K))) (hα2 : α ^ 2 = 1)
    {N : Matrix (Fin (2 * 5)) (Fin (2 * 5)) K} (hN2 : N * N = 0) (hN : N ≠ 0)
    (r : K → matrixDerived (coordinateQuadPlus 5 K))
    (hr : ∀ c, (((r c : matrixDerived (coordinateQuadPlus 5 K)) : GL (Fin (2 * 5)) K) :
      Matrix (Fin (2 * 5)) (Fin (2 * 5)) K) = 1 + c • N)
    (w : K → matrixProjectiveDerived (coordinateQuadPlus 5 K)) (φ₀ : K → K)
    (hinto : ∀ c, ∃ c', w c = matrixProjectiveProjection _ (r c'))
    (honto : ∀ c', ∃ c, w c = matrixProjectiveProjection _ (r c'))
    (hact : ∀ c, α (w c) = w (φ₀ c))
    (h1 : Nat.card {c : K // φ₀ c = c} ≠ 1) (hKc : Nat.card {c : K // φ₀ c = c} ≠ Nat.card K)
    (L : Subgroup (fixedSubgroup α)) (hL : IsComponent L) : NoPSL2Odd L := by
  have hstated : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadPlus 5 K))) .POmegaPlus
      5 p f := ⟨⟨hp, hf, by norm_num⟩, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨-, hnd, hT, -, hAP, -⟩ := coordinate_model_witness_plus hstated K hK (MulEquiv.refl _)
  have hmem : α ∈ matrixProjectiveImage (coordinateQuadPlus 5 K) := by
    rw [RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_plus K 5 le_rfl]
    exact Subgroup.mem_top α
  obtain ⟨g, rfl⟩ := hmem
  have hgg : matrixProjectiveConjugationHom _ (g * g) = 1 := by rw [map_mul, ← sq, hα2]
  obtain ⟨hσ2', c, hc⟩ :=
    (RankThree.Classical.SteinbergBY.matrixProjectiveConjugationHom_eq_one_iff _ hnd hT hAP
      (g * g)).mp hgg
  have hσ2 : g.val.right ^ 2 = 1 := by
    rw [← (CatalogueBOrthogonalInvolutionRepresentation.sq_val _ g).2]
    exact hσ2'
  have hc' : g.val.left * CatalogueBHigherLinearField.glFieldAut (Fin (2 * 5)) K g.val.right
      g.val.left = Matrix.GeneralLinearGroup.scalar (Fin (2 * 5)) c := by
    rw [← (CatalogueBOrthogonalInvolutionRepresentation.sq_val _ g).1, hc]
  have hσ : g.val.right ≠ 1 :=
    right_ne_one_of_root_action (by norm_num) hN2 hN r hr g w φ₀ hinto honto hact h1 hKc
  exact noPSL2Odd_omega_field_ten hO hp hp2 hf hK rfl hnd g hσ2 hσ c hc' hL

end CFSG.ComponentClassification.Foote5.OddLieCore.Exc
