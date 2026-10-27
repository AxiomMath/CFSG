module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4FixQS
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinearBranches
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBStated

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsSp4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag Subgroup
open CatalogueBSymplecticB CatalogueBAlternatingIsometry

variable {K : Type} [Field K]

theorem conjSp_eq_iff (A : gsp 2 K) (g : StatedSp 2 K) :
    conjSp 2 K A g = g ↔ ∀ x, matrixLinIso (g : GL (Fin 2 ⊕ Fin 2) K)
      (matrixLinIso (A : GL (Fin 2 ⊕ Fin 2) K) x) =
      matrixLinIso (A : GL (Fin 2 ⊕ Fin 2) K) (matrixLinIso (g : GL (Fin 2 ⊕ Fin 2) K) x) := by
  set A' : GL (Fin 2 ⊕ Fin 2) K := (A : GL (Fin 2 ⊕ Fin 2) K) with hA'
  set g' : GL (Fin 2 ⊕ Fin 2) K := (g : GL (Fin 2 ⊕ Fin 2) K) with hg'
  have key : conjSp 2 K A g = g ↔ g' * A' = A' * g' := by
    constructor
    · intro h
      have h' : A' * g' * A'⁻¹ = g' := congrArg Subtype.val h
      calc g' * A' = A' * g' * A'⁻¹ * A' := by rw [h']
        _ = A' * g' := by group
    · intro h
      apply Subtype.ext
      change A' * g' * A'⁻¹ = g'
      rw [← h, mul_inv_cancel_right]
  rw [key]
  constructor
  · intro h x
    have := congrArg (fun M => matrixLinIso M x) h
    simpa only [map_mul, LinearEquiv.mul_apply] using this
  · intro h
    apply matrixLinIso.injective
    rw [map_mul, map_mul]
    exact LinearEquiv.ext h

theorem map_fixOf_conjSp (A : gsp 2 K) :
    (fixOf (conjSp 2 K A)).map (statedSpIsometryEquiv (r := 2) (K := K)).toMonoidHom =
      symplecticOperatorCentralizer (pairedSympForm K 2)
        ((LinearMap.GeneralLinearGroup.ofLinearEquiv
          (matrixLinIso (A : GL (Fin 2 ⊕ Fin 2) K)) : LinearMap.GeneralLinearGroup K _) :
            Module.End K _) := by
  ext h
  rw [mem_map_equiv, mem_fixOf, conjSp_eq_iff, mem_symplecticOperatorCentralizer_iff]
  simp only [statedSpIsometryEquiv_symm_val, MulEquiv.apply_symm_apply]
  rfl

@[expose] def fixOfConjSpEquiv (A : gsp 2 K) :
    fixOf (conjSp 2 K A) ≃* symplecticOperatorCentralizer (pairedSympForm K 2)
        ((LinearMap.GeneralLinearGroup.ofLinearEquiv
          (matrixLinIso (A : GL (Fin 2 ⊕ Fin 2) K)) : LinearMap.GeneralLinearGroup K _) :
            Module.End K _) :=
  ((statedSpIsometryEquiv (r := 2) (K := K)).subgroupMap (fixOf (conjSp 2 K A))).trans
    (MulEquiv.subgroupCongr (map_fixOf_conjSp A))

theorem fixOf_conjSp_nonsquare {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) (A : gsp 2 K) {d : K} (hd0 : d ≠ 0) (hdsq : ∀ l : K, l ^ 2 ≠ d)
    (hAA : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = d • 1)
    (hμ : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ * formJ 2 K *
      ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = d • formJ 2 K) :
    CFSG.IsQuasisimple (fixOf (conjSp 2 K A)) ∧
      Nat.card (fixOf (conjSp 2 K A)) = (p ^ f) ^ 2 * (((p ^ f) ^ 2) ^ 2 - 1) := by
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
  have := finite_of_odd_card hEodd
  have : Module.Finite (UnitaryHigher.scalarSquareField (Ag : Module.End K (Fin 2 ⊕ Fin 2 → K)))
      (Fin 2 ⊕ Fin 2 → K) :=
    CatalogueBOrthogonalScalarSquareField.evaluationModule_finite _
  let e := (fixOfConjSpEquiv A).trans (evaluationIsometryEquiv (pairedSympForm K 2) Ag
    (isometryGroup BE) (fun φ => ∀ v w, BE (φ v) (φ w) = BE v w) (mem_isometryGroup_iff BE) hiff)
  have hq3 : 3 ≤ p ^ f := by
    have := hp.two_le
    have h3 : 3 ≤ p := by omega
    calc 3 ≤ p := h3
      _ ≤ p ^ f := Nat.le_self_pow (by omega) p
  refine ⟨(isQuasisimple_congr e).mpr (isometry_quasisimple BE hBEalt hBEnd (by omega) hEodd
    (Or.inr (by rw [hcard]; nlinarith))), ?_⟩
  rw [Nat.card_congr e.toEquiv, isometryGroup,
    SymplecticFlag.card_isometryGroup 1 BE hBEalt hBEnd (by omega), hcard]
  simp

end CFSG.ComponentClassification.CatFactsSp4
