module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneX10Typed
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddCentralFixed
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddOmegaForms

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.X10

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof
open CFSG.RankThree.PartOne.KCOrthogonalDescent CFSG.RankThree.Classical2
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData

theorem orthogonal_derived_lieModel_even {k W : Type} [Field k] [Finite k] [AddCommGroup W]
    [Module k W] [FiniteDimensional k W] {p e n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e)
    (hk : Nat.card k = p ^ e) (Q₀ : QuadraticForm k W) (hQ₀ : Q₀.polarBilin.Nondegenerate)
    (hd : Module.finrank k W = 2 * n) (hn : 4 ≤ n) :
    IsQuasisimple (commutator (TauCeti.QuadraticMap.orthogonalGroup Q₀)) ∧
      ∃ τ' : StatedLieTag, (τ' = .POmegaPlus ∨ τ' = .POmegaMinus) ∧ StatedLieAdmissible τ' n p e ∧
        Blueprint.LieModel (commutator (TauCeti.QuadraticMap.orthogonalGroup Q₀) ⧸
          center (commutator (TauCeti.QuadraticMap.orthogonalGroup Q₀))) τ' n p e := by
  have : CharP k p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp he hk
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq k p]; exact hp2)
  obtain ⟨m, δ, hδ, ⟨H⟩⟩ := exists_regular_split Q₀ hQ₀
  have hfin := H.finrank_eq
  obtain ⟨hm3, τ', hτ', htag, hadm, hstated⟩ : 3 ≤ m ∧ ∃ τ' : StatedLieTag,
      (τ' = .POmegaPlus ∨ τ' = .POmegaMinus) ∧ τ' ∈ Blueprint.classicalTags ∧
        StatedLieAdmissible τ' n p e ∧ StatedClassicalModel (ProjOrthDerived Q₀) τ' n p e := by
    rcases (show δ = 0 ∨ δ = 2 by omega) with hδ0 | hδ2
    ·
      have hmn : m = n := by omega
      have H' : HypSplit Q₀ n 0 := by rw [← hmn, ← hδ0]; exact H
      let bk := H'.b.reindex (HypSplit.plusEquiv n)
      have e1 := projOrthDerivedEquiv (Q₁ := CFSG.LieType.Universal.Spin.quadPlus n k)
        bk.equivFun 1 (fun w => by
          rw [show (CFSG.LieType.Universal.Spin.quadPlus n k) (bk.equivFun w) =
            StatedQuadPlus n k (bk.equivFun w) from
            congrFun (CFSG.LieType.Universal.Spin.coe_quadPlus n k) _, Units.val_one, one_mul]
          exact H'.displayPlus w)
      exact ⟨by omega, .POmegaPlus, Or.inl rfl, by decide, ⟨hp, he, hn⟩, ⟨hp, he, hn⟩, k,
        inferInstance, inferInstance, hk, ⟨e1.trans
          (CFSG.RankThree.CentralLift.nonempty_statedProj_mulEquiv_projOrthDerived
            (CFSG.LieType.Universal.Spin.coe_quadPlus n k)).some.symm⟩⟩
    ·
      have hmn : m = n - 1 := by omega
      have H' : HypSplit Q₀ (n - 1) 2 := by rw [← hmn, ← hδ2]; exact H
      have hα : Q₀ (H'.b (.inr (.inr 0))) ≠ 0 := H'.Q_tail_two_ne_zero
      let u : kˣ := Units.mk0 _ hα
      have hu : (u : k) = Q₀ (H'.b (.inr (.inr 0))) := rfl
      let t₀ := H'.b (.inr (.inr 0))
      let t₁ := H'.b (.inr (.inr 1))
      let b' : k := ((u⁻¹ : kˣ) : k) * QuadraticMap.polar Q₀ t₀ t₁
      let c' : k := ((u⁻¹ : kˣ) : k) * Q₀ t₁
      have hroot : ∀ r : k, r ^ 2 + b' * r + c' ≠ 0 := by
        intro r hr
        have h1 : Q₀ (∑ j, (![r, 1] : Fin 2 → k) j • H'.b (.inr (.inr j))) = 0 := by
          rw [H'.tail_two]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          have h2 : (u : k) * (r ^ 2 + b' * r + c') = 0 := by rw [hr, mul_zero]
          have h3 : (u : k) * (r ^ 2 + b' * r + c') =
              r ^ 2 * Q₀ t₀ + 1 ^ 2 * Q₀ t₁ + r * 1 * QuadraticMap.polar Q₀ t₀ t₁ := by
            have h4 : (u : k) * ((u⁻¹ : kˣ) : k) = 1 := Units.mul_inv u
            simp only [b', c']
            rw [hu] at h4 ⊢
            linear_combination (Q₀ t₁ + r * QuadraticMap.polar Q₀ t₀ t₁) * h4
          rw [← h3]
          exact h2
        have h5 := H'.aniso _ h1
        exact one_ne_zero (congrFun h5 1)
      let bk := H'.scaled u
      have e1 := projOrthDerivedEquiv (Q₁ := CFSG.LieType.Universal.Spin.quadMinus n k b' c')
        bk.equivFun u⁻¹ (fun w => by
          rw [show (CFSG.LieType.Universal.Spin.quadMinus n k b' c') (bk.equivFun w) =
            StatedQuadMinus n k b' c' (bk.equivFun w) from
            congrFun (CFSG.LieType.Universal.Spin.coe_quadMinus n k b' c') _]
          exact H'.displayMinus u hu w)
      exact ⟨by omega, .POmegaMinus, Or.inr rfl, by decide, ⟨hp, he, hn⟩, ⟨hp, he, hn⟩, k,
        inferInstance, inferInstance, hk, b', c', hroot, ⟨e1.trans
          (CFSG.RankThree.CentralLift.nonempty_statedProj_mulEquiv_projOrthDerived
            (CFSG.LieType.Universal.Spin.coe_quadMinus n k b' c')).some.symm⟩⟩
  obtain ⟨T, hT, hTQ⟩ := H.exists_totallySingular_three hm3
  have hq := (CatalogueBOrthogonal.high_Witt_orthogonal_p_components Q₀ h2 hQ₀ hT.ge hTQ).1
  have : IsSimpleGroup (ProjOrthDerived Q₀) :=
    (LieType.Simplicity.fam_classical_converse _ ⟨τ', n, p, e, hstated⟩).2.2
  obtain ⟨eP⟩ := nonempty_centerQuotient_equiv_projOrthDerived Q₀ hq
  exact ⟨hq, τ', hτ', hadm, LieType.CurtisTits.lieModel_of_mulEquiv eP.symm
    (Or.inl ⟨htag, hstated⟩)⟩

open CatalogueBOrthogonalDescent CatalogueBLinearTwoDescent CatalogueBOrthogonalFieldFixed
  CatalogueBOrthogonalLinearFixed CatalogueBOrthogonalFixedTransfer in
theorem excCompModel_omega_field_ten {K : Type} [Field K] [Finite K] {d p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) (hdim : d = 2 * 5)
    {Q : QuadraticForm K (Fin d → K)} (hQ : Q.polarBilin.Nondegenerate)
    (g : similarityPairs Q) (hσ2 : g.val.right ^ 2 = 1) (hσ : g.val.right ≠ 1) (c : Kˣ)
    (hc : g.val.left * CatalogueBHigherLinearField.glFieldAut (Fin d) K g.val.right g.val.left =
      Matrix.GeneralLinearGroup.scalar (Fin d) c)
    {L : Subgroup (fixedSubgroup (matrixProjectiveConjugationHom Q g))} (hL : IsComponent L) :
    ExcCompModel p L := by
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
  exact ⟨τ', 5, f / 2, hct, hadm, LieType.CurtisTits.lieModel_of_mulEquiv eTot.symm hlie⟩

end CFSG.ComponentClassification.Burgoyne.X10
