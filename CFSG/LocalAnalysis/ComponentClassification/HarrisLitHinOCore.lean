module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinOExtD
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorOrthField
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorOrthPaired
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorOrthUnitary

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.Hin

open Subgroup Module QuadraticMap Matrix CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.RestrictedStd
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.OddClassSelector
open CFSG.LocalAnalysis.ComponentInitial.OddOrthogonal (commutant mem_commutant)
open CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquare (orthogonalOmega)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare
  CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareField

variable {K : Type} [Field K] [Finite K] {d : ℕ}

theorem orth_rank_of_component {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hK : Nat.card K = ℓ ^ e) (hd : 7 ≤ d) {Q : QuadraticForm K (Fin d → K)}
    (hQ : Q.polarBilin.Nondegenerate) (hP : ThreePairs Q)
    (hd8 : d = 8 → (∃ U : Submodule K (Fin d → K), finrank K U = 4 ∧ ∀ x ∈ U, Q x = 0) ∨
      ∀ x ∈ orthogonalOmega Q, ∀ r : K, (∀ v, x v = r • v) → x = 1)
    (hker : ∀ g' : similarityPairs Q, matrixProjectiveConjugationHom Q g' = 1 ↔
      g'.val.right = 1 ∧ ∃ a : Kˣ, GeneralLinearGroup.scalar (Fin d) a = g'.val.left)
    (g : similarityPairs Q) (hσ2 : g.val.right ^ 2 = 1) (c : Kˣ)
    (hc : g.val.left * CatalogueBHigherLinearField.glFieldAut (Fin d) K g.val.right g.val.left =
      GeneralLinearGroup.scalar (Fin d) c)
    (hlin : g.val.right = 1 → ∀ a : Kˣ, GeneralLinearGroup.scalar (Fin d) a ≠ g.val.left)
    {X : Subgroup (matrixProjectiveDerived Q)}
    (hX : CFSG.Assembly.IsComponentOf X (fixedSubgroup (matrixProjectiveConjugationHom Q g)))
    (hs : SmallSource X) :
    (∃ E' : Subgroup (matrixProjectiveDerived Q),
      E' ≤ fixedSubgroup (matrixProjectiveConjugationHom Q g) ∧ ElemTwo E' ∧ 16 ≤ Nat.card E') ∨
    (matrixProjectiveConjugationHom Q g ∉
        (MulAut.conj : matrixProjectiveDerived Q →* MulAut (matrixProjectiveDerived Q)).range ∧
      ∃ E' : Subgroup (matrixProjectiveDerived Q),
        E' ≤ fixedSubgroup (matrixProjectiveConjugationHom Q g) ∧ ElemTwo E' ∧
          8 ≤ Nat.card E') := by
  classical
  have : CharP K ℓ := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hℓ he hK
  have hk2 : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hk2
  have hdV : finrank K (Fin d → K) = d := Module.finrank_fin_fun K
  obtain ⟨Y, hY, -, ⟨σ, hσs, hσk⟩, -⟩ := orth_lift Q g hσ2 ⟨c, hc⟩ hX
  by_cases hσ1 : g.val.right = 1
  swap
  · exact (orth_field_false hℓ hℓ2 he hK hd hQ g hσ2 hσ1 c hc hY σ hσk hs).elim
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
  have hcomA : ∀ x : (Fin d → K) ≃ₗ[K] (Fin d → K), x * Aₗ = Aₗ * x →
      x ∈ commutant (coordinateSemilinearMap g.val) := fun x hx =>
    mem_commutant.mpr fun v => by rw [hτ, hτ]; exact LinearEquiv.congr_fun hx v
  obtain ⟨hpm, -, hsq, hns4⟩ :=
    CatalogueBOrthogonalScalarSquareStructure.scalar_square_centralizer_structure ℓ e hℓ hℓ2 he
      hK (by omega) Q hQ Aₗ c μ hsquare hsim hnonscalar
  by_cases hsqc : IsSquare (c : K)
  · obtain ⟨b0, hb0⟩ := hsqc
    have hb00 : b0 ≠ 0 := by
      rintro rfl
      exact Units.ne_zero c (by rw [hb0, mul_zero])
    have hb : (c : K) = ((Units.mk0 b0 hb00 : Kˣ) : K) ^ 2 := by
      rw [Units.val_mk0, hb0, _root_.sq]
    rcases hpm with h1 | h1
    ·
      left
      obtain ⟨hMF, -, -, hpos, -⟩ := hsq _ hb
      obtain ⟨horth, hndP, hndN, -⟩ := hpos h1
      have hb1 : (b0 : K) ≠ 0 := hb00
      have hAM : ∀ m ∈ positiveSquareKernel Aₗ ((Units.mk0 b0 hb00 : Kˣ) : K),
          Aₗ m = b0 • m := by
        intro m hm
        have h0 := LinearMap.mem_ker.mp hm
        rw [Units.val_mk0, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
          sub_eq_zero] at h0
        calc Aₗ m = b0 • (b0⁻¹ • Aₗ m) := by rw [smul_smul, mul_inv_cancel₀ hb1, one_smul]
          _ = b0 • m := by rw [show b0⁻¹ • Aₗ m = m from h0]
      have hAF : ∀ f ∈ negativeSquareKernel Aₗ ((Units.mk0 b0 hb00 : Kˣ) : K),
          Aₗ f = -b0 • f := by
        intro f hf
        have h0 := LinearMap.mem_ker.mp hf
        rw [Units.val_mk0, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
          add_eq_zero_iff_eq_neg] at h0
        calc Aₗ f = b0 • (b0⁻¹ • Aₗ f) := by rw [smul_smul, mul_inv_cancel₀ hb1, one_smul]
          _ = -b0 • f := by rw [show b0⁻¹ • Aₗ f = -f from h0, smul_neg, neg_smul]
      obtain ⟨E, hEΩ, hE2, hE16, hEA, hEZ⟩ := exists_elemTwo_split h2 hQ hP (by omega) hMF
        (fun x hx y hy => horth x hx y hy) hndP hndN hAM hAF
      obtain ⟨E', hE', hE'2, hcard⟩ := exists_elemTwo_fix Q g
        (fun x hx => ⟨hEΩ hx, hcomA x (hEA x hx)⟩) hE2 hEZ
      exact ⟨E', hE', hE'2, hE16.trans hcard⟩
    · exact (orth_paired_false hℓ hℓ2 he hK (by omega) hQ Aₗ c μ hsquare hsim hnonscalar _ hb h1
        hY σ hσk hs).elim
  · rcases hpm with h1 | h1
    · by_cases h10 : 10 ≤ d
      · exact (orth_ext_false hℓ hℓ2 he hK (by omega) hQ Aₗ c μ hsquare hsim hnonscalar hsqc h1
          hY σ hσk hs).elim
      have h4 := hns4 hsqc
      have : Nontrivial (Fin d → K) := Module.nontrivial_of_finrank_pos (R := K) (by omega)
      let : Field (scalarAlgebra Aₗ.toLinearMap) := scalarField Aₗ.toLinearMap c hsqc
        (CatalogueBOrthogonalScalarSquareStructure.original_endomorphism_square Aₗ c hsquare)
      let : Module (scalarAlgebra Aₗ.toLinearMap) (Fin d → K) := evaluationModule Aₗ.toLinearMap
      obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hfinrank, -⟩, -, -⟩ :=
        h4
      have h8 : d = 8 := by omega
      have hμc : (μ : K) = c := (div_eq_one_iff_eq (Units.ne_zero c)).mp h1
      rcases hd8 h8 with hU | hZ
      · exact Or.inl (exists_elemTwo_ext_plus hℓ hℓ2 he hK h8 hQ hU g hτ c μ hsquare hsim
          hnonscalar hsqc h1)
      · refine Or.inr ⟨conjugationHom_not_mem_range hker g hsqc (fun v => ?_) ?_,
          exists_elemTwo_ext_minus h2 hQ hP h8 hZ g hτ c μ hsquare hsim hsqc h1⟩
        · rw [hτ, hQA, hμc]
        · obtain ⟨P₁, -, -, -, -, -⟩ := hP
          refine ⟨P₁.e + P₁.f, ?_⟩
          rw [QuadraticMap.map_add Q, P₁.Q_e, P₁.Q_f, P₁.polar_ef]
          norm_num
    · exact (orth_unitary_false hℓ hℓ2 he hK (by omega) hQ Aₗ c μ hsquare hsim hnonscalar hsqc
        h1 hY σ hσs hσk hs).elim

end CFSG.ComponentClassification.HarrisLit.Hin
