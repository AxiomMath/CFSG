module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.OrthAux.Layer
public import CFSG.RankThree.PartOne.S11c.Sec66ClassCommon
public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.LieArith
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldCentralizer

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923.OrthAux

open Matrix QuadraticMap
open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCOrthogonalSubfield CFSG.RankThree.PartOne.Sec66T
  CFSG.ComponentClassification.CatLeaf
open CFSG.LieType.Universal.Spin (quadOdd quadPlus quadMinus coe_quadOdd coe_quadPlus coe_quadMinus)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
  (statedProjectiveReindexEquiv)
open CFSG.HardMathSupport.Dickson.Sec6.I923

section Abstract

variable {K : Type} [Field K] [Finite K] {k : Subfield K} {d : ℕ}
  {Q₀ : QuadraticForm k (Fin d → k)} {Q : QuadraticForm K (Fin d → K)} {σ : K ≃+* K} {p : ℕ}

theorem noL2Layer_fieldAutT (S : SubfieldSetup k Q₀ Q σ p)
    (hL2 : ∀ r : ℕ, 10 ≤ r → ¬ IsTypeL2 r (matrixProjectiveDerived Q₀)) :
    NoL2Layer (fieldAutT Q σ S.hQσ) := by
  have hd : 0 < d := three_le_of_totallySingular k S.hT₀
  obtain ⟨hsimp, hnonab⟩ := matrix_simple_nonabelian hd S.hnd₀ S.hT₀
  have e := inclEquiv k S.hext hd
  have hJs : IsSimpleGroup ↥(subfieldDerivedImage k S.hext) := e.symm.isSimpleGroup
  have hJnab : ∃ a b : ↥(subfieldDerivedImage k S.hext), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    exact ⟨e a, e b, fun h => hab (e.injective (by rw [map_mul, map_mul]; exact h))⟩
  have hfix : fixSubgroup (fieldAutT Q σ S.hQσ) = subfieldFixedGroup k Q₀ Q :=
    Subgroup.ext fun t => fieldAutT_apply_iff S t
  have hJn := subfieldDerivedImage_normal k S.hext
  haveI := hJn
  have hquot := fixedGroup_quotient_isPGroup k S.hext S.hnd₀ S.hT₀
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := IsPGroup.isNilpotent hquot
  refine noL2Layer_of_fix_eq _ _ _ hfix (subfieldDerivedImage_le k S.hext) inferInstance hJs
    hJnab fun r hr hT => hL2 r hr ?_
  exact l2fld_isTypeL2_of_mulEquiv e.symm hT

end Abstract

section Tags

variable {K : Type} [Field K] [Finite K] {k : Subfield K} {σ : K ≃+* K} {p : ℕ}

theorem noL2Layer_fieldAutT_odd (hO : LieOrderFormulasInput) {n ℓ e : ℕ}
    (hadm : StatedLieAdmissible .POmegaOdd n ℓ e) (hk : Nat.card k = ℓ ^ e)
    (S : SubfieldSetup k (coordinateQuadOdd n k) (coordinateQuadOdd n K) σ p) :
    NoL2Layer (fieldAutT (coordinateQuadOdd n K) σ S.hQσ) := by
  refine noL2Layer_fieldAutT S fun r hr => ?_
  have hd := three_le_of_totallySingular k S.hT₀
  have hmodel : LieModel (matrixProjectiveDerived (coordinateQuadOdd n k)) .POmegaOdd n ℓ e :=
    (lieModel_classical_iff (by decide)).mpr ⟨hadm, ↥k, inferInstance, inferInstance, hk,
      ⟨(statedProjectiveReindexEquiv (oddIndexEquiv n) (quadOdd n k) (coe_quadOdd n k)).symm⟩⟩
  exact not_typeL2_of_lieModel hO hadm hmodel (by decide) (by simp)
    (center_matrix_eq_bot hd S.hnd₀ S.hT₀) hr

theorem noL2Layer_fieldAutT_plus (hO : LieOrderFormulasInput) {n ℓ e : ℕ}
    (hadm : StatedLieAdmissible .POmegaPlus n ℓ e) (hk : Nat.card k = ℓ ^ e)
    (S : SubfieldSetup k (coordinateQuadPlus n k) (coordinateQuadPlus n K) σ p) :
    NoL2Layer (fieldAutT (coordinateQuadPlus n K) σ S.hQσ) := by
  refine noL2Layer_fieldAutT S fun r hr => ?_
  have hd := three_le_of_totallySingular k S.hT₀
  have hmodel : LieModel (matrixProjectiveDerived (coordinateQuadPlus n k)) .POmegaPlus n ℓ e :=
    (lieModel_classical_iff (by decide)).mpr ⟨hadm, ↥k, inferInstance, inferInstance, hk,
      ⟨(statedProjectiveReindexEquiv (plusIndexEquiv n) (quadPlus n k) (coe_quadPlus n k)).symm⟩⟩
  exact not_typeL2_of_lieModel hO hadm hmodel (by decide) (by simp)
    (center_matrix_eq_bot hd S.hnd₀ S.hT₀) hr

theorem noL2Layer_fieldAutT_minus (hO : LieOrderFormulasInput) {n ℓ e : ℕ} (hn : 1 ≤ n)
    (hadm : StatedLieAdmissible .POmegaMinus n ℓ e) (hk : Nat.card k = ℓ ^ e) (b c : k)
    (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0)
    (S : SubfieldSetup k (coordinateQuadMinus n k hn b c)
      (coordinateQuadMinus n K hn (b : K) (c : K)) σ p) :
    NoL2Layer (fieldAutT (coordinateQuadMinus n K hn (b : K) (c : K)) σ S.hQσ) := by
  refine noL2Layer_fieldAutT S fun r hr => ?_
  have hd := three_le_of_totallySingular k S.hT₀
  have hmodel : LieModel (matrixProjectiveDerived (coordinateQuadMinus n k hn b c)) .POmegaMinus n
      ℓ e :=
    (lieModel_classical_iff (by decide)).mpr ⟨hadm, ↥k, inferInstance, inferInstance, hk, b, c,
      hirr, ⟨(statedProjectiveReindexEquiv (minusIndexEquiv n hn) (quadMinus n k b c)
        (coe_quadMinus n k b c)).symm⟩⟩
  exact not_typeL2_of_lieModel hO hadm hmodel (by decide) (by simp)
    (center_matrix_eq_bot hd S.hnd₀ S.hT₀) hr

end Tags

end CFSG.HardMathSupport.Dickson.Sec6.I923.OrthAux
