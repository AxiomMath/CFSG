module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4EUAnti
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorOrthField
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorOrthLift
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorOrthPaired
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorOrthUnitary

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.Cov

open Subgroup Module QuadraticMap Matrix CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.RestrictedStd
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare
  CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareField
open CFSG.LocalAnalysis.ComponentInitial.OddOrthogonal (commutant mem_commutant)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OddClassSelector

variable {K : Type} [Field K] [Finite K]

section Ext

variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem ext_minus_component {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hK : Nat.card K = ℓ ^ e) (h8 : finrank K V = 8)
    (hnoU : ¬ ∃ U : Submodule K V, finrank K U = 4 ∧ ∀ x ∈ U, Q x = 0)
    (hQ : Q.polarBilin.Nondegenerate)
    (A : V ≃ₗ[K] V) (d μ : Kˣ) (hsquare : ∀ x : V, A (A x) = (d : K) • x)
    (hsim : ∀ x y : V, Q.polarBilin (A x) (A y) = (μ : K) * Q.polarBilin x y)
    (hnonscalar : ∀ c : K, A.toLinearMap ≠ c • (1 : Module.End K V))
    (hnsq : ¬ IsSquare (d : K)) (hμ : (μ : K) / (d : K) = 1)
    {Y : Subgroup (V ≃ₗ[K] V)}
    (hY : CFSG.Assembly.IsComponentOf Y (TauCeti.QuadraticMap.orthogonalGroup Q ⊓
      CatalogueBProjectiveInvolution.operatorCentralizer A.toLinearMap))
    {X : Type*} [Group X] (σ : Y →* X) (hσs : Function.Surjective σ)
    (hσk : σ.ker ≤ center Y) :
    ∃ (E' : Type) (_ : Field E') (_ : Finite E'), Nat.card E' = Nat.card K ^ 4 ∧
      Nonempty (X ⧸ center X ≃* GorensteinWalter.PSL2 E') := by
  classical
  have : CharP K ℓ := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hℓ he hK
  have hk2 : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hk2
  obtain ⟨-, -, -, hns4⟩ :=
    CatalogueBOrthogonalScalarSquareStructure.scalar_square_centralizer_structure ℓ e hℓ hℓ2 he
      hK (by omega) Q hQ A d μ hsquare hsim hnonscalar
  have h4 := hns4 hnsq
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  let : Field (scalarAlgebra A.toLinearMap) := scalarField A.toLinearMap d hnsq
    (CatalogueBOrthogonalScalarSquareStructure.original_endomorphism_square A d hsquare)
  let : Module (scalarAlgebra A.toLinearMap) V := evaluationModule A.toLinearMap
  obtain ⟨⟨-, hfin, -, -, -, hcoord, -, hfinKE, hcard, -, -, -, -, -, -, -, -, -, htower, hfinE,
    hfinrank, -⟩, hpos, -⟩ := h4
  obtain ⟨-, -, -, hQEnd, hBE, hQE, eO, -, -, -, -⟩ := hpos hμ
  have := hfin
  have : IsScalarTower K (scalarAlgebra A.toLinearMap) V := htower
  have : FiniteDimensional (scalarAlgebra A.toLinearMap) V := hfinE
  have hE4 : finrank (scalarAlgebra A.toLinearMap) V = 4 := by omega
  have hoddE : Odd (Nat.card (scalarAlgebra A.toLinearMap)) := by
    rw [hcard]
    exact ((hℓ.odd_of_ne_two hℓ2).pow).pow
  have h2E : (2 : scalarAlgebra A.toLinearMap) ≠ 0 :=
    CatalogueBOddQuadratic.two_ne_zero_of_odd_card hoddE
  obtain ⟨hquasi, E', _, _, hE', ⟨eC⟩⟩ :=
    Catalog7L4EU.commutator_equiv_psl_of_nonsplit _ hQEnd hoddE hE4 (by
      rintro ⟨S, hS2, hSQ⟩
      apply hnoU
      refine ⟨S.restrictScalars K, ?_, fun x hx => ?_⟩
      · rw [((Submodule.restrictScalarsEquiv K _ V S).restrictScalars K).finrank_eq,
          ← Module.finrank_mul_finrank K (scalarAlgebra A.toLinearMap) S, hfinKE, hS2]
      · have h0 := hSQ x hx
        rw [hQE] at h0
        have h1 := (div_eq_zero_iff.mp h0).resolve_right h2E
        rw [hBE] at h1
        have hz : coordinateElement A.toLinearMap (Q.polarBilin x x)
            ((d : K)⁻¹ * Q.polarBilin (A x) x) = coordinateElement A.toLinearMap 0 0 := by
          simp only [coordinateElement, Algebra.smul_def, map_zero, zero_mul, add_zero]
          exact h1
        obtain ⟨p, -, huniq⟩ := hcoord (coordinateElement A.toLinearMap 0 0)
        have hp1 := huniq ⟨Q.polarBilin x x, (d : K)⁻¹ * Q.polarBilin (A x) x⟩ hz
        have hp2 := huniq ⟨0, 0⟩ rfl
        have hpp := congrArg Prod.fst (hp1.trans hp2.symm)
        simp only at hpp
        rw [polarBilin_apply_apply, polar_self, two_smul] at hpp
        have h3 : (2 : K) * Q x = 0 := by rw [two_mul]; exact hpp
        exact (mul_eq_zero.mp h3).resolve_left h2)
  obtain ⟨hle, hY₁, ⟨eY⟩⟩ := isComponent_operatorCentralizer hY
  have hY' := LocalAnalysis.ComponentInitial.isComponent_map_of_isComponent eO hY₁
  have hYeq := LocalAnalysis.ComponentInitial.eq_commutator_of_isComponent hY' hquasi
  have hEcard : Nat.card E' = Nat.card K ^ 4 := by
    rw [hE', hcard, hK]
    ring
  have h3 : 3 < Nat.card E' := by
    have h3K : 3 ≤ Nat.card K := by
      rw [hK]
      have h3p : 3 ≤ ℓ := by have := hℓ.two_le; omega
      exact h3p.trans (Nat.le_self_pow (by omega) ℓ)
    rw [hEcard]
    exact Nat.lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_left h3K 4)
  have : Group.IsPerfect Y := (Group.isPerfect_def).2 hY.2.2.1
  refine ⟨E', inferInstance, inferInstance, hEcard, ?_⟩
  exact Catalog7L4EU.center_quotient_equiv_of_psl h3 σ hσs hσk
    ((eY.symm.trans (((Y.comap (TauCeti.QuadraticMap.orthogonalGroup Q).subtype).subgroupOf
      (orthogonalOperatorCentralizer Q A.toLinearMap)).equivMapOfInjective eO.toMonoidHom
        eO.injective)).trans ((MulEquiv.subgroupCongr hYeq).trans eC))

end Ext

theorem orth_core_minus8 {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hK : Nat.card K = ℓ ^ e) {d : ℕ} (hd : d = 8) {Q : QuadraticForm K (Fin d → K)}
    (hQ : Q.polarBilin.Nondegenerate)
    (hnoU : ¬ ∃ U : Submodule K (Fin d → K), finrank K U = 4 ∧ ∀ x ∈ U, Q x = 0)
    (g : similarityPairs Q) (hσ2 : g.val.right ^ 2 = 1) (c : Kˣ)
    (hc : g.val.left * CatalogueBHigherLinearField.glFieldAut (Fin d) K g.val.right g.val.left =
      GeneralLinearGroup.scalar (Fin d) c)
    (hlin : g.val.right = 1 → ∀ a : Kˣ, GeneralLinearGroup.scalar (Fin d) a ≠ g.val.left)
    {X : Subgroup (matrixProjectiveDerived Q)}
    (hX : CFSG.Assembly.IsComponentOf X (fixedSubgroup (matrixProjectiveConjugationHom Q g)))
    (hs : SmallSource X) (hW : NoTightWitness X) :
    ∃ (E' : Type) (_ : Field E') (_ : Finite E'), Nat.card E' = Nat.card K ^ 4 ∧
      Nonempty (↥X ⧸ center ↥X ≃* GorensteinWalter.PSL2 E') := by
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
  · exact (orth_field_false hℓ hℓ2 he hK (by omega) hQ g hσ2 hσ1 c hc hY σ hσk hs).elim
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
    · exact (orth_split_false hℓ hℓ2 he hK (by omega) hQ Aₗ c μ hsquare hsim hnonscalar _ hb h1
        hY σ hσk hs hN1).elim
    · exact (orth_paired_false hℓ hℓ2 he hK (by omega) hQ Aₗ c μ hsquare hsim hnonscalar _ hb h1
        hY σ hσk hs).elim
  · rcases hpm with h1 | h1
    · exact ext_minus_component hℓ hℓ2 he hK (by omega) hnoU hQ Aₗ c μ hsquare hsim hnonscalar
        hsq h1 hY σ hσs hσk
    · exact (orth_unitary_false hℓ hℓ2 he hK (by omega) hQ Aₗ c μ hsquare hsim hnonscalar hsq h1
        hY σ hσs hσk hs).elim

end CFSG.ComponentClassification.GSThmB.Cov
