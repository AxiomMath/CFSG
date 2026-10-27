module

public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorOrthFour
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorOrthUnitary
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorOrthField
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorOrthPaired
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentDisplayed
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorOrthSplit

public noncomputable section

namespace CFSG.ComponentClassification.OddClassSelector

open Subgroup Module QuadraticMap Matrix CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.RestrictedStd
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.LocalAnalysis.ComponentInitial.OddOrthogonal (commutant mem_commutant)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {K : Type} [Field K] [Finite K] {d : ℕ}

theorem orth_core_false {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hK : Nat.card K = ℓ ^ e) (hd : 7 ≤ d) {Q : QuadraticForm K (Fin d → K)}
    (hQ : Q.polarBilin.Nondegenerate)
    (hU : d = 8 → ∃ U : Submodule K (Fin d → K), finrank K U = 4 ∧ ∀ x ∈ U, Q x = 0)
    (g : similarityPairs Q) (hσ2 : g.val.right ^ 2 = 1) (c : Kˣ)
    (hc : g.val.left * CatalogueBHigherLinearField.glFieldAut (Fin d) K g.val.right g.val.left =
      GeneralLinearGroup.scalar (Fin d) c)
    (hlin : g.val.right = 1 → ∀ a : Kˣ, GeneralLinearGroup.scalar (Fin d) a ≠ g.val.left)
    {X : Subgroup (matrixProjectiveDerived Q)}
    (hX : CFSG.Assembly.IsComponentOf X (fixedSubgroup (matrixProjectiveConjugationHom Q g)))
    (hs : SmallSource X) (hW : NoTightWitness X) : False := by
  classical
  have : CharP K ℓ := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hℓ he hK
  have hk2 : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hk2
  have hdV : finrank K (Fin d → K) = d := Module.finrank_fin_fun K
  obtain ⟨Y, hY, hYΩ, ⟨σ, hσs, hσk⟩, hN⟩ := orth_lift Q g hσ2 ⟨c, hc⟩ hX
  have hN' := hN hW
  by_cases hσ1 : g.val.right = 1
  swap
  · exact orth_field_false hℓ hℓ2 he hK hd hQ g hσ2 hσ1 c hc hY σ hσk hs
  set A := g.val.left with hAdef
  set Aₗ := matrixLinearEquiv A with hAₗ
  have hτ : ∀ v, coordinateSemilinearMap g.val v = Aₗ v := by
    intro v
    rw [coordinateSemilinearMap_apply, hσ1]
    rfl
  have hcomm : commutant (coordinateSemilinearMap g.val) =
      CatalogueBProjectiveInvolution.operatorCentralizer Aₗ.toLinearMap := by
    ext u
    rw [mem_commutant]
    change _ ↔ ∀ x, u (Aₗ x) = Aₗ (u x)
    simp only [hτ]
  rw [hcomm] at hY
  have hAA : A * A = GeneralLinearGroup.scalar (Fin d) c := by
    rw [← hc, hσ1, map_one, MulAut.one_apply]
  have hsquare : ∀ x, Aₗ (Aₗ x) = (c : K) • x := by
    intro x
    rw [← LinearEquiv.mul_apply, hAₗ, ← matrixLinearEquiv_mul, hAA]
    exact LocalAnalysis.ComponentInitial.OddOrthogonal.matrixLinearEquiv_scalar c x
  set μ := multiplier Q g with hμdef
  have hQA : ∀ v, Q (Aₗ v) = (μ : K) * Q v := by
    intro v
    have := multiplier_spec Q g v
    rw [hτ v, hσ1] at this
    exact this
  have hsim : ∀ x y, Q.polarBilin (Aₗ x) (Aₗ y) = (μ : K) * Q.polarBilin x y := by
    intro x y
    rw [polarBilin_apply_apply, polarBilin_apply_apply, polar, polar, ← map_add, hQA, hQA, hQA]
    ring
  have hnonscalar : ∀ c' : K, Aₗ.toLinearMap ≠ c' • (1 : Module.End K (Fin d → K)) := by
    intro c' h
    have hc0 : c' ≠ 0 := by
      rintro rfl
      have h0 := LinearMap.congr_fun h (Pi.single ⟨0, by omega⟩ 1)
      rw [zero_smul, LinearMap.zero_apply, LinearEquiv.coe_coe,
        LinearEquiv.map_eq_zero_iff] at h0
      simpa using congrFun h0 ⟨0, by omega⟩
    apply hlin hσ1 (Units.mk0 c' hc0)
    apply matrixLinearIso.injective
    refine LinearEquiv.ext fun v => ?_
    change matrixLinearEquiv (GeneralLinearGroup.scalar (Fin d) (Units.mk0 c' hc0)) v = Aₗ v
    rw [LocalAnalysis.ComponentInitial.OddOrthogonal.matrixLinearEquiv_scalar]
    have := LinearMap.congr_fun h v
    rw [LinearEquiv.coe_coe] at this
    rw [this]
    rfl
  obtain ⟨hpm, -, -, -⟩ :=
    CatalogueBOrthogonalScalarSquareStructure.scalar_square_centralizer_structure ℓ e hℓ hℓ2 he
      hK (by omega) Q hQ Aₗ c μ hsquare hsim hnonscalar
  have hN1 : ∀ t s : (Fin d → K) ≃ₗ[K] (Fin d → K),
      t ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ →
      s ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ →
      t * t = 1 → (∀ c : K, (t : (Fin d → K) →ₗ[K] (Fin d → K)) ≠ c • LinearMap.id) →
      (∀ y ∈ Y, y * t = t * y) → s * t = t * s → s ∈ normalizer (Y : Set _) := by
    intro t s ht hs' htt htn htY hst
    refine hN' t s ht hs' ⟨1, ?_⟩ htn htY hst
    rw [htt, one_smul]
    rfl
  by_cases hsq : IsSquare (c : K)
  · obtain ⟨b0, hb0⟩ := hsq
    have hb00 : b0 ≠ 0 := by
      rintro rfl
      exact Units.ne_zero c (by rw [hb0, mul_zero])
    have hb : (c : K) = ((Units.mk0 b0 hb00 : Kˣ) : K) ^ 2 := by
      rw [Units.val_mk0, hb0, _root_.sq]
    rcases hpm with h1 | h1
    · exact orth_split_false hℓ hℓ2 he hK (by omega) hQ Aₗ c μ hsquare hsim hnonscalar _ hb h1
        hY σ hσk hs hN1
    · exact orth_paired_false hℓ hℓ2 he hK (by omega) hQ Aₗ c μ hsquare hsim hnonscalar _ hb h1
        hY σ hσk hs
  · rcases hpm with h1 | h1
    · by_cases h10 : 10 ≤ d
      · exact orth_ext_false hℓ hℓ2 he hK (by omega) hQ Aₗ c μ hsquare hsim hnonscalar hsq h1
          hY σ hσk hs
      · exact orth_ext_small_false hℓ hℓ2 he hK (by omega) (by omega)
          (fun h8 => hU (by omega)) hQ Aₗ c μ hsquare hsim hnonscalar hsq h1 hY hYΩ hN'
    · exact orth_unitary_false hℓ hℓ2 he hK (by omega) hQ Aₗ c μ hsquare hsim hnonscalar hsq h1
        hY σ hσs hσk hs

omit [Finite K] in
theorem exists_totallySingular_coordinateQuadPlus (n : ℕ)
    (hnd : (polarBilin (CatalogueBOrthogonalPointData.coordinateQuadPlus n K)).Nondegenerate) :
    ∃ U : Submodule K (Fin (2 * n) → K), finrank K U = n ∧
      ∀ x ∈ U, CatalogueBOrthogonalPointData.coordinateQuadPlus n K x = 0 := by
  have h := CFSG.RankThree.PartOne.KCOrthogonalDescent.sourceWittIndex_coordinateQuadPlus n K hnd
  have hmem := Nat.sSup_mem (s := {d | ∃ W : Submodule K (Fin (2 * n) → K),
      (∀ w ∈ W, CatalogueBOrthogonalPointData.coordinateQuadPlus n K w = 0) ∧ finrank K W = d})
    ⟨0, ⊥, fun w hw => by rw [(Submodule.mem_bot K).mp hw, QuadraticMap.map_zero],
      finrank_bot K _⟩ (CFSG.Blueprint.EvenSource.sourceWittIndex_bddAbove _)
  obtain ⟨W, hW, hWd⟩ := hmem
  refine ⟨W, ?_, hW⟩
  rw [hWd]
  exact h

theorem orth_socle_false {A : Type} [Group A] {W : Subgroup A} [W.Normal]
    (hWs : IsSimpleGroup W) (hWnab : ∃ x y : W, x * y ≠ y * x)
    (hCW : centralizer (W : Set A) = ⊥) {a : A} (ha : orderOf a = 2) {L : Subgroup A}
    (hLCW : CFSG.Assembly.IsComponentOf L (W ⊓ centralizer {a}))
    (hstd : CFSG.IsStandardSubgroup L) (hs : SmallSource L) {ℓ e : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e) (hK : Nat.card K = ℓ ^ e) (hd : 7 ≤ d)
    {Q : QuadraticForm K (Fin d → K)} (hQ : Q.polarBilin.Nondegenerate)
    (hU : d = 8 → ∃ U : Submodule K (Fin d → K), finrank K U = 4 ∧ ∀ x ∈ U, Q x = 0)
    (hrep : CatalogueBOrthogonalInvolutionRepresentation.SemilinearRepresentation Q)
    (θ : W ≃* matrixProjectiveDerived Q) : False := by
  have : IsSimpleGroup (matrixProjectiveDerived Q) := θ.symm.isSimpleGroup
  have hnab : ∃ x y : matrixProjectiveDerived Q, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hWnab
    refine ⟨θ x, θ y, fun h => hxy (θ.injective ?_)⟩
    rw [map_mul, map_mul, h]
  have hZ := OutcomeLocal.center_eq_bot_of_isSimpleGroup hnab
  obtain ⟨ρ, X, hinj, hinn, hX, hLX, ⟨eLX⟩⟩ := fixed_component_of_socle hCW θ hZ hLCW
  have hW := noTightWitness_of_isStandardSubgroup hinj hinn (conj_injective hZ) hstd hLX
  have hαα : ρ a * ρ a = 1 := by
    rw [← map_mul, ← pow_two, ← ha, pow_orderOf_eq_one, map_one]
  have hα1 : ρ a ≠ 1 := by
    intro h
    have h1 : orderOf (ρ a) = orderOf a := orderOf_injective ρ hinj a
    rw [h, orderOf_one, ha] at h1
    exact absurd h1 (by norm_num)
  obtain ⟨β, g, hβg, hσ2, ⟨c, hc⟩, hlin, -⟩ := hrep.2 (ρ a) hαα hα1
  have hX₁ := isComponentOf_map_symm β hX
  rw [hβg] at hX₁
  exact orth_core_false hℓ hℓ2 he hK hd hQ hU g hσ2 c hc hlin hX₁
    (smallSource_of_mulEquiv (eLX.trans (X.equivMapOfInjective _ β.symm.injective)) hs)
    (hW.map β.symm)

end CFSG.ComponentClassification.OddClassSelector
