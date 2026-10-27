module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4O8f
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4O8d
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OIUf

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OIO

open CFSG Subgroup Module Matrix
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare
open CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit
open CFSG.ComponentClassification.OddSelector (rowOAction)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

attribute [local instance] GSThmB.Catalog7Std.Om8.finite_linearEquiv

variable {K : Type} [Field K] [Finite K] {b c : K}

theorem exists_model {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e)
    (hK : Nat.card K = p ^ e) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hQ0 : ∃ v, Q8 K b c v ≠ 0) (φ : MulAut (G0 K b c)) (hφ2 : φ ^ 2 = 1) (hφ1 : φ ≠ 1)
    (J' : Subgroup (G0 K b c)) (hJφ : J' ≤ OutInv.fixSub φ)
    (hJ : IsComponent (J'.subgroupOf (OutInv.fixSub φ)))
    (hJm : Blueprint.LieModel (J' ⧸ center J') .PSL 2 p (2 * (2 * e))) :
    ∃ (A : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) (μ c₀ : Kˣ)
      (hsim : ∀ x, Q8 K b c (A x) = (μ : K) * Q8 K b c x),
      (∀ x, A (A x) = (c₀ : K) • x) ∧ (μ : K) = c₀ ∧
      (∀ a : K, A.toLinearMap ≠ a • (1 : Module.End K (Fin (2 * 4) → K))) ∧
      (∀ x, theta K b c hQ0 (φ x) =
        projectiveConjugation (Q8 K b c) A μ hsim (theta K b c hQ0 x)) ∧
      (∃ gφ : similarityPairs (Q8 K b c),
        matrixProjectiveConjugationHom (Q8 K b c) gφ = MulAut.congr (psiC K b c) φ ∧
          gφ.val.right = 1 ∧ A = matrixLinearEquiv gφ.val.left) ∧
      ∃ hns : ¬ IsSquare (c₀ : K),
        letI : Fact (¬ IsSquare (c₀ : K)) := ⟨hns⟩
        ∃ (δ : (extension (c₀ : K))ˣ) (_ : ¬ IsSquare (δ : extension (c₀ : K)))
          (h2 : (2 : extension (c₀ : K)) ≠ 0) (d : (extension (c₀ : K))ˣ)
          (χ : (Fin (2 * 4) → K) ≃ₗ[K] (Fin 4 → extension (c₀ : K)))
          (y : SpecialLinearGroup (Fin 2) (extension (δ : extension (c₀ : K))) →*
            orthogonalDerived (Q8 K b c)),
          (∀ v, χ (A v) = (QuadraticAlgebra.omega : extension (c₀ : K)) • χ v) ∧
          (∀ v, Q8 K b c v =
            ((d : extension (c₀ : K)) * OIL.qf (δ : extension (c₀ : K)) (χ v)).re) ∧
          (∀ h v, (y h).val.val v =
            χ.symm ((OIU.Umat δ h2 h : Matrix (Fin 4) (Fin 4) (extension (c₀ : K))) *ᵥ χ v)) ∧
          ∀ x, x ∈ J' ↔ ∃ h, QuotientGroup.mk'
            ((scalarSigns (Q8 K b c)).subgroupOf (orthogonalDerived (Q8 K b c))) (y h) =
              theta K b c hQ0 x := by
  obtain ⟨A, μ, c₀, hsim, hsq, hμc, hns, hφ, hgφ⟩ :=
    exists_simil K b c hp hp2 he hK hirr hQ0 φ hφ2 hφ1
  have hsqc := not_isSquare hp hp2 he hK hirr hQ0 φ A μ c₀ hsim hsq hμc hns hφ J' hJφ hJ hJm
  obtain ⟨M, hM, -, hJM⟩ := exists_lift hQ0 φ A μ hsim hφ J' hJφ hJ
  refine ⟨A, μ, c₀, hsim, hsq, hμc, hns, hφ, hgφ, hsqc, ?_⟩
  have : Fact (¬ IsSquare (c₀ : K)) := ⟨hsqc⟩
  have hc₀ : (c₀ : K) ≠ 0 := Units.ne_zero c₀
  have hμd : (μ : K) / (c₀ : K) = 1 := by rw [hμc]; exact div_self hc₀
  have hadj := positive_square_adjoint (Q8 K b c) A (c₀ : K) (μ : K) hc₀ hsq
    (polar_similarity (Q8 K b c) A μ hsim) hμd
  have hodd : Odd (Nat.card K) := by rw [hK]; exact (hp.odd_of_ne_two hp2).pow
  have h2K : (2 : K) ≠ 0 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  have himage := image_eq_commutator hp hp2 he hK hirr A μ c₀ hsim hsq hadj h2K M hM
  have hstated := stated K b c hp he hK hirr
  obtain ⟨-, hnd, -⟩ := CatalogueBOrthogonalPointData.coordinate_model_witness_minus hstated K hK
    b c hirr (MulEquiv.refl _)
  have hnp := GSThmB.Catalog7Std.Om8.not_isPlusType_coordinateQuadMinus 4 (by norm_num) hirr
  let := modE A (c₀ : K) hsq
  let := isScalarTower A (c₀ : K) hsq
  let := finite_extension (c₀ : K)
  let : FiniteDimensional (extension (c₀ : K)) (Fin (2 * 4) → K) :=
    Module.Finite.of_restrictScalars_finite K _ _
  have hQE := formE_nondegenerate A (c₀ : K) hsq (Q8 K b c) hc₀ hadj h2K hnd
  have hdim : finrank K (Fin (2 * 4) → K) = 8 := by simp
  have hdimE : finrank (extension (c₀ : K)) (Fin (2 * 4) → K) = 4 := by
    have := finrank_E A (c₀ : K) hsq
    omega
  have hno := formE_not_split A (c₀ : K) hsq (Q8 K b c) hc₀ hadj h2K hdim hnp
  have hEodd : Odd (Nat.card (extension (c₀ : K))) := by
    rw [card_extension]
    exact hodd.pow
  obtain ⟨δ, hδ, d, ψ, e', hψ, he', hcomm, -, -⟩ :=
    LocalAnalysis.ComponentInitial.orthogonal_nonsplit_four_derived hEodd
      (formE A (c₀ : K) hsq (Q8 K b c) hc₀ hadj) hQE hdimE hno
  have : Fact (¬ IsSquare (δ : extension (c₀ : K))) := ⟨hδ⟩
  let cE := centEquivE A (c₀ : K) hsq (Q8 K b c) hc₀ hadj h2K
  let ρ := specialRho (δ : extension (c₀ : K))
    (CatalogueBOddQuadratic.two_ne_zero_of_odd_card hEodd)
  obtain ⟨y, hyv, hya, hyb⟩ := exists_hom_of_image (fixedCentralizerEquiv (Q8 K b c) A μ hsim)
    (fun g => rfl) cE e' ρ M (fun g => (Iff.of_eq (congrArg (fun S => g ∈ S) hcomm.symm)).trans
      (himage g))
  have hJy : ∀ x, x ∈ J' ↔ ∃ h, QuotientGroup.mk'
      ((scalarSigns (Q8 K b c)).subgroupOf (orthogonalDerived (Q8 K b c))) (y h) =
        theta K b c hQ0 x := by
    intro x
    rw [hJM x]
    constructor
    · rintro ⟨m, hm, hmx⟩
      obtain ⟨h, hh⟩ := hya m hm
      exact ⟨h, hh ▸ hmx⟩
    · rintro ⟨h, hhx⟩
      obtain ⟨m, hm, hh⟩ := hyb h
      exact ⟨m, hm, hh ▸ hhx⟩
  have hyv' : ∀ h v, (y h).val.val v = ψ.symm (rowOAction δ h (ψ v)) := fun h v => by
    have h1 : (ρ h).val (ψ v) = ψ ((e'.symm (ρ h)).val v) :=
      (congrArg (fun g => g.val (ψ v)) (e'.apply_symm_apply (ρ h)).symm).trans
        ((he' (e'.symm (ρ h)) (ψ v)).trans
          (congrArg (fun w => ψ ((e'.symm (ρ h)).val w)) (ψ.symm_apply_apply v)))
    have h2 : (y h).val.val v = (e'.symm (ρ h)).val v := by
      rw [hyv]
      exact centEquivE_symm_apply A (c₀ : K) hsq (Q8 K b c) hc₀ hadj h2K _ v
    exact h2.trans ((ψ.symm_apply_apply _).symm.trans (congrArg ψ.symm h1.symm))
  let hc := hermitianCoordinates (δ : extension (c₀ : K))
    (CatalogueBOddQuadratic.two_ne_zero_of_odd_card hEodd)
  let χE : (Fin (2 * 4) → K) ≃ₗ[extension (c₀ : K)] (Fin 4 → extension (c₀ : K)) := ψ.trans hc.symm
  have hχE : ∀ v, χE.restrictScalars K v = hc.symm (ψ v) := fun v => rfl
  have hχEs : ∀ x, (χE.restrictScalars K).symm x = ψ.symm (hc x) := fun x => rfl
  refine ⟨δ, hδ, CatalogueBOddQuadratic.two_ne_zero_of_odd_card hEodd, d, χE.restrictScalars K, y,
    fun v => ?_, fun v => ?_, fun h v => ?_, fun x => ?_⟩
  · calc χE.restrictScalars K (A v) = hc.symm (ψ (A v)) := hχE _
      _ = hc.symm (ψ ((QuadraticAlgebra.omega : extension (c₀ : K)) • v)) :=
          congrArg (fun X => hc.symm (ψ X)) (omega_smul A (c₀ : K) hsq v).symm
      _ = hc.symm ((QuadraticAlgebra.omega : extension (c₀ : K)) • ψ v) :=
          congrArg hc.symm (ψ.map_smul _ _)
      _ = (QuadraticAlgebra.omega : extension (c₀ : K)) • hc.symm (ψ v) := hc.symm.map_smul _ _
      _ = _ := congrArg _ (hχE v).symm
  · have h1 : hermitianForm (δ : extension (c₀ : K)) (ψ v) =
        OIL.qf (δ : extension (c₀ : K)) (χE.restrictScalars K v) :=
      (congrArg (hermitianForm (δ : extension (c₀ : K))) (hc.apply_symm_apply (ψ v)).symm).trans
        ((OIL.hermitianForm_coord (δ : extension (c₀ : K))
          (CatalogueBOddQuadratic.two_ne_zero_of_odd_card hEodd) (hc.symm (ψ v))).trans
          (congrArg _ (hχE v).symm))
    calc Q8 K b c v = (formE A (c₀ : K) hsq (Q8 K b c) hc₀ hadj v).re :=
          (re_formE A (c₀ : K) hsq (Q8 K b c) hc₀ hadj h2K v).symm
      _ = ((d : extension (c₀ : K)) * hermitianForm (δ : extension (c₀ : K)) (ψ v)).re :=
          congrArg QuadraticAlgebra.re (hψ v)
      _ = _ := congrArg (fun t => ((d : extension (c₀ : K)) * t).re) h1
  · calc (y h).val.val v = ψ.symm (rowOAction δ h (ψ v)) := hyv' h v
      _ = ψ.symm (hc (hc.symm (rowOAction δ h (ψ v)))) :=
          congrArg ψ.symm (hc.apply_symm_apply _).symm
      _ = ψ.symm (hc (hc.symm (rowOAction δ h (hc (hc.symm (ψ v)))))) :=
          congrArg (fun X => ψ.symm (hc (hc.symm (rowOAction δ h X))))
            (hc.apply_symm_apply (ψ v)).symm
      _ = ψ.symm (hc ((OIU.Umat δ (CatalogueBOddQuadratic.two_ne_zero_of_odd_card hEodd) h :
            Matrix (Fin 4) (Fin 4) (extension (c₀ : K))) *ᵥ hc.symm (ψ v))) :=
          congrArg (fun X => ψ.symm (hc X)) (OIU.Umat_mulVec δ _ h (hc.symm (ψ v))).symm
      _ = _ := (hχEs _).symm.trans
          (congrArg (fun Y => (χE.restrictScalars K).symm
            ((OIU.Umat δ (CatalogueBOddQuadratic.two_ne_zero_of_odd_card hEodd) h :
              Matrix (Fin 4) (Fin 4) (extension (c₀ : K))) *ᵥ Y)) (hχE v).symm)
  · exact hJy x

end OIO

end CFSG.ComponentClassification.CatFactsL4U4
