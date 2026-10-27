module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4OutII

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsSp4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag Subgroup
open CatalogueBSymplecticB CatalogueBAlternatingIsometry

variable {K : Type} [Field K]

theorem ivk714_fixOf_conjSp_nonsquare_sl2 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) (A : gsp 2 K) {d : K} (hd0 : d ≠ 0) (hdsq : ∀ l : K, l ^ 2 ≠ d)
    (hAA : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = d • 1)
    (hμ : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ * formJ 2 K *
      ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = d • formJ 2 K) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E), Nat.card E = (p ^ f) ^ 2 ∧
      Nonempty (↥(fixOf (conjSp 2 K A)) ≃* Matrix.SpecialLinearGroup (Fin 2) E) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hp.pos f).ne')
  set Ag : LinearMap.GeneralLinearGroup K (Fin 2 ⊕ Fin 2 → K) :=
    LinearMap.GeneralLinearGroup.ofLinearEquiv (matrixLinIso (A : GL (Fin 2 ⊕ Fin 2) K))
    with hAgdef
  have hAg : ∀ v, (Ag : Module.End K (Fin 2 ⊕ Fin 2 → K)) v =
      ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v := fun v => rfl
  have hdim : Module.finrank K (Fin 2 ⊕ Fin 2 → K) = 2 * 2 := finrank_standard
  have hAns : ∀ c : K, (Ag : Module.End K (Fin 2 ⊕ Fin 2 → K)) ≠ c • 1 := by
    intro c hc
    apply hdsq c
    set e : Fin 2 ⊕ Fin 2 → K := Pi.single (Sum.inl 0) 1 with he
    have h1 : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ e =
        c • e := by
      have := LinearMap.congr_fun hc e
      rwa [hAg] at this
    have h2 : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
        (((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ e) =
        d • e := by rw [mulVec_mulVec, hAA, smul_mulVec, one_mulVec]
    rw [h1, mulVec_smul, h1, smul_smul] at h2
    have h3 := congrFun h2 (Sum.inl 0)
    simp only [he, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h3
    rw [sq]
    exact h3
  have hAA' : (Ag : Module.End K (Fin 2 ⊕ Fin 2 → K)) * (Ag : Module.End K (Fin 2 ⊕ Fin 2 → K)) =
      d • 1 := by
    apply LinearMap.ext
    intro v
    rw [Module.End.mul_apply, hAg, hAg, mulVec_mulVec, hAA, smul_mulVec, one_mulVec]
    rfl
  have hμ' : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ *
      formJ 2 K * ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      ((Units.mk0 d hd0 : Kˣ) : K) • formJ 2 K := by rw [Units.val_mk0]; exact hμ
  have hAμ : ∀ v w, pairedSympForm K 2 ((Ag : Module.End K (Fin 2 ⊕ Fin 2 → K)) v)
      ((Ag : Module.End K (Fin 2 ⊕ Fin 2 → K)) w) = d * pairedSympForm K 2 v w := fun v w =>
    matrix_similitude _ (Units.mk0 d hd0) hμ' v w
  obtain ⟨-, -, hnonsplit⟩ := UnitaryHigher.odd_symplectic_scalar_square_centralizer_structure
    hp hp2 hf hK (r := 2) (by norm_num) hdim SymplecticFlag.pairedSympForm_isAlt
    SymplecticFlag.pairedSympForm_nondegenerate
    hAns hd0 hAA' hAμ
  obtain ⟨-, hF, hcard, hfinrank, -, -, -, -, hpos, -⟩ := hnonsplit hdsq
  obtain ⟨BE, -, hBEalt, hBEnd, -, hiff⟩ := hpos (div_self hd0)
  let : Field (UnitaryHigher.scalarSquareField (Ag : Module.End K (Fin 2 ⊕ Fin 2 → K))) :=
    hF.toField
  have hEodd : Odd (Nat.card (UnitaryHigher.scalarSquareField
      (Ag : Module.End K (Fin 2 ⊕ Fin 2 → K)))) := by
    rw [hcard]
    exact ((hp.odd_of_ne_two hp2).pow).pow
  have hEfin := finite_of_odd_card hEodd
  have : Module.Finite (UnitaryHigher.scalarSquareField (Ag : Module.End K (Fin 2 ⊕ Fin 2 → K)))
      (Fin 2 ⊕ Fin 2 → K) :=
    CatalogueBOrthogonalScalarSquareField.evaluationModule_finite _
  let e := (fixOfConjSpEquiv A).trans (evaluationIsometryEquiv (pairedSympForm K 2) Ag
    (isometryGroup BE) (fun φ => ∀ v w, BE (φ v) (φ w) = BE v w) (mem_isometryGroup_iff BE) hiff)
  obtain ⟨eSL⟩ := exists_planeIsometryEquivSL BE hBEalt hBEnd hfinrank
  exact ⟨UnitaryHigher.scalarSquareField (Ag : Module.End K (Fin 2 ⊕ Fin 2 → K)), hF.toField,
    hEfin, hcard, ⟨e.trans eSL⟩⟩

end CFSG.ComponentClassification.CatFactsSp4
