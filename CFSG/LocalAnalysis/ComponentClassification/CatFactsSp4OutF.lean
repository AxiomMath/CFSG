module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBDescent
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4FixQS
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBStated

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsSp4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag Subgroup
open CatalogueBSymplecticB CatalogueBAlternatingIsometry

variable {K : Type} [Field K]

theorem conjSp_fieldSp_eq_iff (A : gsp 2 K) (σ : K ≃+* K) (g : StatedSp 2 K) :
    (conjSp 2 K A * fieldSp 2 K σ) g = g ↔
      ∀ x, matrixLinIso (g : GL (Fin 2 ⊕ Fin 2) K)
        (semilinearCoordMap (A : GL (Fin 2 ⊕ Fin 2) K) σ x) =
        semilinearCoordMap (A : GL (Fin 2 ⊕ Fin 2) K) σ
          (matrixLinIso (g : GL (Fin 2 ⊕ Fin 2) K) x) := by
  set A' : GL (Fin 2 ⊕ Fin 2) K := (A : GL (Fin 2 ⊕ Fin 2) K) with hA'
  set gm : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
    ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) with hgm
  have hval : ((((conjSp 2 K A * fieldSp 2 K σ) g : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      (A' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * gm.map σ *
        ((A'⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
    rw [MulAut.mul_apply, coe_conjSp, Units.val_mul, Units.val_mul, coe_fieldSp]
  have key : (conjSp 2 K A * fieldSp 2 K σ) g = g ↔
      gm * (A' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        (A' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * gm.map σ := by
    constructor
    · intro h
      have h' : (A' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * gm.map σ *
          ((A'⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = gm := by
        rw [← hval, h]
      calc gm * (A' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
          A' * gm.map σ * ((A'⁻¹ : GL (Fin 2 ⊕ Fin 2) K) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * A' := by rw [h']
        _ = A' * gm.map σ := by rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    · intro h
      apply Subtype.ext
      apply Units.ext
      rw [hval, ← h, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [key]
  simp only [matrixLinIso_apply, semilinearCoordMap_apply, coord_mulVec, mulVec_mulVec]
  constructor
  · intro h x
    rw [h]
  · intro h
    ext i j
    have := congrFun (h (fun k => σ.symm ((Pi.single j 1 : Fin 2 ⊕ Fin 2 → K) k))) i
    have hσ : (fun k => σ (σ.symm ((Pi.single j 1 : Fin 2 ⊕ Fin 2 → K) k))) = Pi.single j 1 :=
      funext fun k => σ.apply_symm_apply _
    rw [hσ, mulVec_single_one_apply', mulVec_single_one_apply'] at this
    exact this

theorem map_fixOf_conjSp_fieldSp (A : gsp 2 K) (σ : K ≃+* K) :
    (fixOf (conjSp 2 K A * fieldSp 2 K σ)).map
        (statedSpIsometryEquiv (r := 2) (K := K)).toMonoidHom =
      semilinearSymplecticCentralizer (pairedSympForm K 2)
        (semilinearCoordMap (A : GL (Fin 2 ⊕ Fin 2) K) σ) := by
  ext h
  rw [mem_map_equiv, mem_fixOf, conjSp_fieldSp_eq_iff, mem_semilinearSymplecticCentralizer_iff]
  simp only [statedSpIsometryEquiv_symm_val, MulEquiv.apply_symm_apply]

theorem fixOf_conjSp_fieldSp [Finite K] (hodd : Odd (Nat.card K)) (A : gsp 2 K)
    (σ : K ≃+* K) (hσ2 : σ ^ 2 = 1) (hσ1 : σ ≠ 1) (d : Kˣ)
    (hd : (A : GL (Fin 2 ⊕ Fin 2) K) *
        CatalogueBHigherLinearField.glFieldEquiv (Fin 2 ⊕ Fin 2) σ (A : GL (Fin 2 ⊕ Fin 2) K) =
      GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) d) :
    CFSG.IsQuasisimple (fixOf (conjSp 2 K A * fieldSp 2 K σ)) ∧
      Nat.card (fixOf (conjSp 2 K A * fieldSp 2 K σ)) =
        Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K σ) ^ 4 *
          ((Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K σ) ^ 2 - 1) *
            (Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K σ) ^ 4 - 1)) := by
  have h2 := two_ne_zero_of_odd_card hodd
  set μ := multiplierUnit A with hμdef
  have hμ := multiplierUnit_spec A
  have hdim : 0 < Module.finrank K (Fin 2 ⊕ Fin 2 → K) := by rw [finrank_standard]; norm_num
  obtain ⟨-, -, -, ⟨b, c, hb, hc⟩, hall⟩ := odd_symplectic_quadratic_semilinear_descent σ hσ2
    hσ1 h2 hdim (pairedSympForm K 2) SymplecticFlag.pairedSympForm_isAlt
    SymplecticFlag.pairedSympForm_nondegenerate (semilinearCoordMap (A : GL (Fin 2 ⊕ Fin 2) K) σ)
    μ d (semilinearCoordMap_smul _ σ) (semilinearCoordMap_form _ σ μ hμ)
    (semilinearCoordMap_sq _ σ hσ2 d hd)
  obtain ⟨-, -, -, -, hfin, hfinrank, -, hB0alt, hB0nd, -, e₂, -⟩ := hall b c hb hc
  let e₁ : fixOf (conjSp 2 K A * fieldSp 2 K σ) ≃* semilinearSymplecticCentralizer
      (pairedSympForm K 2) (semilinearCoordMap (A : GL (Fin 2 ⊕ Fin 2) K) σ) :=
    ((statedSpIsometryEquiv (r := 2) (K := K)).subgroupMap _).trans
      (MulEquiv.subgroupCongr (map_fixOf_conjSp_fieldSp A σ))
  let e := e₁.trans e₂
  have hkodd := CatalogueBOrthogonalFieldFixed.subfield_card_odd hodd
    (CatalogueBLinearTwoDescent.fixedSubfield K σ)
  rw [finrank_standard] at hfinrank
  refine ⟨(isQuasisimple_congr e).mpr (isometry_quasisimple _ hB0alt hB0nd (by omega) hkodd
    (Or.inl (by omega))), ?_⟩
  rw [Nat.card_congr e.toEquiv, isometryGroup,
    SymplecticFlag.card_isometryGroup 2 _ hB0alt hB0nd (by omega)]
  simp [Finset.prod_Icc_succ_top]

end CFSG.ComponentClassification.CatFactsSp4
