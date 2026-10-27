module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10LinOrthHigh
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516LeafExcOrd
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddCentralFixed

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData

open CatalogueBOrthogonalDescent CatalogueBLinearTwoDescent CatalogueBOrthogonalFieldFixed
  CatalogueBOrthogonalLinearFixed CatalogueBOrthogonalFixedTransfer in
theorem odd_omega_field_modelIn {K : Type} [Field K] [Finite K] {d p f n : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f)
    (hdim : d = 2 * n + 1 ∧ 3 ≤ n ∨ d = 2 * n ∧ 4 ≤ n)
    {Q : QuadraticForm K (Fin d → K)} (hQ : Q.polarBilin.Nondegenerate)
    (g : similarityPairs Q) (hσ2 : g.val.right ^ 2 = 1) (hσ : g.val.right ≠ 1) (c : Kˣ)
    (hc : g.val.left * CatalogueBHigherLinearField.glFieldAut (Fin d) K g.val.right g.val.left =
      Matrix.GeneralLinearGroup.scalar (Fin d) c)
    {L : Subgroup (fixedSubgroup (matrixProjectiveConjugationHom Q g))} (hL : IsComponent L) :
    X10Lin.ModelIn p (X10Lin.orthTuples d (f / 2)) L := by
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
  have hdimW : Module.finrank (fixedSubfield K σ) (fixedSubspace σ T hs) = 2 * n + 1 ∧ 3 ≤ n ∨
      Module.finrank (fixedSubfield K σ) (fixedSubspace σ T hs) = 2 * n ∧ 4 ≤ n := by
    rw [fixedSubspace_finrank σ hσ2 hσ h2 T hT hs, Module.finrank_fin_fun]
    exact hdim
  obtain ⟨hΩq, hmodel⟩ := X10Lin.centralModel_orthogonal_derived hp hp2 hf2 hk
    (originalDescendedQuadratic σ τ₀ b hsemi Q.polarBilin μ c' hform hc') hQ0 hdimW
  rw [fixedSubspace_finrank σ hσ2 hσ h2 T hT hs, Module.finrank_fin_fun] at hmodel
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
  exact hmodel.of_centerQuotient_equiv eTot

end CFSG.ComponentClassification.CatLeafProof

namespace CFSG.ComponentClassification.GSThmB.Orth516

open CFSG CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.Burgoyne.X10 (prod_pow_sub_one_le mul_le_pow)

theorem sum_two_mul_Icc (m : ℕ) : ∑ i ∈ Finset.Icc 1 m, 2 * i = m * (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    ring

theorem prod_two_mul_le (Q m : ℕ) :
    ∏ i ∈ Finset.Icc 1 m, (Q ^ (2 * i) - 1) ≤ Q ^ (m * (m + 1)) := by
  rw [← sum_two_mul_Icc]
  exact prod_pow_sub_one_le Q _ fun i => 2 * i

theorem false_of_l4u4_of_orthTuples (hO : LieOrderFormulasInput) {X : Type} [Group X]
    {p f d e : ℕ} (hp2 : p ≠ 2) (hf : 1 ≤ f) (hd : 7 ≤ d)
    (hM : X10Lin.ModelIn p (X10Lin.orthTuples d e) X)
    (hX : (p ^ f % 4 = 3 ∧ Blueprint.LieModel (X ⧸ Subgroup.center X) .PSL 4 p f) ∨
      (p ^ f % 4 = 1 ∧ Blueprint.LieModel (X ⧸ Subgroup.center X) .PSU 4 p f)) : False := by
  obtain ⟨τ', n', e', hT, hadm', hX'⟩ := hM
  have hp : p.Prime := hadm'.1
  have hQ3 : 3 ≤ p ^ e' := Burgoyne.X10.three_le_pow hp hp2 hadm'.2.1
  rcases hT with ⟨h3, -⟩ | ⟨h4, -⟩ | ⟨h5, -⟩ | ⟨h6, -⟩ | ⟨-, -, heq⟩ | ⟨-, -, heq | heq⟩
  · omega
  · omega
  · omega
  · omega
  ·
    obtain rfl : τ' = .POmegaOdd := (Prod.mk.inj heq).1
    have hn : 3 ≤ n' := hadm'.2.2.1
    have hb : lieOrderCofactor .POmegaOdd n' (p ^ e') ≤ 1 * (p ^ e') ^ (n' ^ 2 + n') := by
      rw [one_mul, show n' ^ 2 + n' = n' * (n' + 1) by ring]
      exact prod_two_mul_le _ n'
    refine Pump516.false_of_l4u4_of_cofactor_le (N := n' ^ 2) (C := n' ^ 2 + n') (c := 1) hO
      hp2 hf hadm' hX' hX rfl hb fun _ => ⟨by nlinarith, ?_⟩
    have hk : 3 ≤ 3 * n' ^ 2 - 2 * (n' ^ 2 + n') := by
      have : 3 + 2 * (n' ^ 2 + n') ≤ 3 * n' ^ 2 := by nlinarith
      omega
    exact Pump516.sixteen_lt_pow hQ3 hk
  ·
    obtain rfl : τ' = .POmegaPlus := (Prod.mk.inj heq).1
    have hn : 4 ≤ n' := hadm'.2.2
    obtain ⟨m, rfl⟩ : ∃ m, n' = m + 1 := ⟨n' - 1, by omega⟩
    have hb : lieOrderCofactor .POmegaPlus (m + 1) (p ^ e') ≤
        1 * (p ^ e') ^ ((m + 1) ^ 2) := by
      rw [one_mul, show (m + 1) ^ 2 = (m + 1) + m * (m + 1) by ring]
      simp only [lieOrderCofactor, Nat.add_sub_cancel]
      exact mul_le_pow (Nat.sub_le _ _) (prod_two_mul_le _ m)
    refine Pump516.false_of_l4u4_of_cofactor_le (N := (m + 1) * m) (C := (m + 1) ^ 2) (c := 1)
      hO hp2 hf hadm' hX' hX (by simp [lieSylowExponent]) hb fun _ => ⟨by nlinarith, ?_⟩
    have hk : 3 ≤ 3 * ((m + 1) * m) - 2 * (m + 1) ^ 2 := by
      have : 3 + 2 * (m + 1) ^ 2 ≤ 3 * ((m + 1) * m) := by nlinarith
      omega
    exact Pump516.sixteen_lt_pow hQ3 hk
  ·
    obtain rfl : τ' = .POmegaMinus := (Prod.mk.inj heq).1
    have hn : 4 ≤ n' := hadm'.2.2
    obtain ⟨m, rfl⟩ : ∃ m, n' = m + 1 := ⟨n' - 1, by omega⟩
    have hb : lieOrderCofactor .POmegaMinus (m + 1) (p ^ e') ≤
        2 * (p ^ e') ^ ((m + 1) ^ 2) := by
      rw [show (m + 1) ^ 2 = (m + 1) + m * (m + 1) by ring, pow_add]
      simp only [lieOrderCofactor, Nat.add_sub_cancel]
      have h1 : (p ^ e') ^ (m + 1) + 1 ≤ 2 * (p ^ e') ^ (m + 1) := by
        have := Nat.one_le_pow (m + 1) (p ^ e') (by omega)
        omega
      calc ((p ^ e') ^ (m + 1) + 1) * ∏ i ∈ Finset.Icc 1 m, ((p ^ e') ^ (2 * i) - 1)
          ≤ (2 * (p ^ e') ^ (m + 1)) * (p ^ e') ^ (m * (m + 1)) :=
            Nat.mul_le_mul h1 (prod_two_mul_le _ m)
        _ = 2 * ((p ^ e') ^ (m + 1) * (p ^ e') ^ (m * (m + 1))) := by ring
    refine Pump516.false_of_l4u4_of_cofactor_le (N := (m + 1) * m) (C := (m + 1) ^ 2) (c := 2)
      hO hp2 hf hadm' hX' hX (by simp [lieSylowExponent]) hb fun _ => ⟨by nlinarith, ?_⟩
    have hk : 4 ≤ 3 * ((m + 1) * m) - 2 * (m + 1) ^ 2 := by
      have : 4 + 2 * (m + 1) ^ 2 ≤ 3 * ((m + 1) * m) := by nlinarith
      omega
    calc 16 * 2 ^ 2 < 3 ^ 4 := by norm_num
      _ ≤ (p ^ e') ^ 4 := Nat.pow_le_pow_left hQ3 4
      _ ≤ (p ^ e') ^ (3 * ((m + 1) * m) - 2 * (m + 1) ^ 2) :=
          Nat.pow_le_pow_right (by omega) hk

end CFSG.ComponentClassification.GSThmB.Orth516
