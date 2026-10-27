module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Layer
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.OrthAux.Layer
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldCentralizer
public import CFSG.RankThree.PartOne.S11c.Sec66ClassCommon

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.OutSpOrth

open Matrix QuadraticMap
open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.CaseThreeNs
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.UniquenessMaximal
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCOrthogonalSubfield CFSG.RankThree.PartOne.Sec66T
  CFSG.ComponentClassification.CatLeaf CFSG.LocalAnalysis.GLTheoremB
open CFSG.LieType.Universal.Spin (quadOdd quadPlus quadMinus coe_quadOdd coe_quadPlus coe_quadMinus)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
  (statedProjectiveReindexEquiv)
open CFSG.HardMathSupport.Dickson.Sec6 CFSG.HardMathSupport.Dickson.Sec6.I923
open CFSG.HardMathSupport.Dickson.Sec6.I923.OrthAux
open scoped commutatorElement

section Abstract

theorem noL34Layer_of_congr {P P' : Type} [Group P] [Finite P] [Group P'] (e : P ≃* P')
    {ψ : MulAut P} (h : NoL34Layer (MulAut.congr e ψ)) : NoL34Layer ψ := by
  haveI : Finite P' := Finite.of_equiv P e.toEquiv
  exact noL34Layer_congr e h

theorem noL34Layer_of_normal_simple {P : Type} [Group P] [Finite P] (δ : MulAut P)
    (J : Subgroup P) (hJC : J ≤ fixSubgroup δ) [(J.subgroupOf (fixSubgroup δ)).Normal]
    (hsol : Group.IsSolvable (↥(fixSubgroup δ) ⧸ J.subgroupOf (fixSubgroup δ)))
    (hs : IsSimpleGroup ↥J) (hnab : ∃ a b : ↥J, a * b ≠ b * a)
    (hL34 : ¬ IsLThreeFour ↥J) : NoL34Layer δ := by
  intro A hA hT
  have hq : CFSG.Open.IsQuasisimple ↥J := isQuasisimple_of_simple hnab
  have hAD : A ≤ fixSubgroup δ := hA.1
  have hAJ : A ≤ J :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfect_le_of_solvable_quotient hJC hsol
      hAD (glaPComponent_perfect hA)
  have hsn : IsSubnormal A J := isSubnormal_of_le_of_le hA.2.1 hAJ hJC
  have hAeq : A = J :=
    Lemma510Ns.eq_of_isSubnormal_of_quasisimple hq hsn (glaPComponent_perfect hA)
      (glaPComponent_ne_bot hA)
  have hAq := isQuasisimple_barOf_of_glaPComponent Nat.prime_three hA
  subst hAeq
  have hcore : GLAPPrimeCore 3 ↥A = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (GLAPPrimeCore 3 ↥A) with h | h
    · exact h
    · exfalso
      have hsub : Subsingleton (barOf 3 A) := by
        refine ⟨fun a b => ?_⟩
        induction a using QuotientGroup.induction_on with
        | H a =>
          induction b using QuotientGroup.induction_on with
          | H b =>
            rw [QuotientGroup.eq]
            rw [h]
            exact Subgroup.mem_top _
      have hs2 : Subsingleton (barOf 3 A ⧸ Subgroup.center (barOf 3 A)) :=
        (QuotientGroup.mk'_surjective (Subgroup.center (barOf 3 A))).subsingleton
      exact (not_nontrivial_iff_subsingleton.2 hs2) hAq.2.toNontrivial
  have e : barOf 3 A ≃* ↥A :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans (QuotientGroup.quotientBot (G := ↥A))
  exact hL34 (IsLThreeFour.of_mulEquiv e hT)

theorem noL34Layer_of_fixed_normal_simple {P : Type} [Group P] [Finite P] (δ : MulAut P)
    (N J : Subgroup P) (hfix : fixSubgroup δ = N) (hJN : J ≤ N) [(J.subgroupOf N).Normal]
    (hsol : Group.IsSolvable (↥N ⧸ J.subgroupOf N))
    (hs : IsSimpleGroup ↥J) (hnab : ∃ a b : ↥J, a * b ≠ b * a)
    (hL34 : ¬ IsLThreeFour ↥J) : NoL34Layer δ := by
  subst hfix
  exact noL34Layer_of_normal_simple δ J hJN hsol hs hnab hL34

end Abstract

section Field

variable {K : Type} [Field K] [Finite K] {k : Subfield K} {d : ℕ}
  {Q₀ : QuadraticForm k (Fin d → k)} {Q : QuadraticForm K (Fin d → K)} {σ : K ≃+* K} {p : ℕ}

theorem noL34Layer_fieldAutT (S : SubfieldSetup k Q₀ Q σ p)
    (hL34 : ¬ IsLThreeFour (matrixProjectiveDerived Q₀)) :
    NoL34Layer (fieldAutT Q σ S.hQσ) := by
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
  refine noL34Layer_of_fixed_normal_simple _ _ _ hfix (subfieldDerivedImage_le k S.hext)
    inferInstance hJs hJnab fun hT => hL34 ?_
  exact IsLThreeFour.of_mulEquiv e.symm hT

end Field

section Tags

variable {K : Type} [Field K] [Finite K] {k : Subfield K} {σ : K ≃+* K} {p : ℕ}

theorem noL34Layer_fieldAutT_odd (hO : LieOrderFormulasInput) {n ℓ e : ℕ}
    (hadm : StatedLieAdmissible .POmegaOdd n ℓ e) (hℓ2 : ℓ ≠ 2) (hk : Nat.card k = ℓ ^ e)
    (S : SubfieldSetup k (coordinateQuadOdd n k) (coordinateQuadOdd n K) σ p) :
    NoL34Layer (fieldAutT (coordinateQuadOdd n K) σ S.hQσ) := by
  refine noL34Layer_fieldAutT S ?_
  have hmodel : LieModel (matrixProjectiveDerived (coordinateQuadOdd n k)) .POmegaOdd n ℓ e :=
    (lieModel_classical_iff (by decide)).mpr ⟨hadm, ↥k, inferInstance, inferInstance, hk,
      ⟨(statedProjectiveReindexEquiv (oddIndexEquiv n) (quadOdd n k) (coe_quadOdd n k)).symm⟩⟩
  exact not_isLThreeFour_of_lieModel_odd hO hℓ2 hmodel

theorem noL34Layer_fieldAutT_plus (hO : LieOrderFormulasInput) {n ℓ e : ℕ}
    (hadm : StatedLieAdmissible .POmegaPlus n ℓ e) (hℓ2 : ℓ ≠ 2) (hk : Nat.card k = ℓ ^ e)
    (S : SubfieldSetup k (coordinateQuadPlus n k) (coordinateQuadPlus n K) σ p) :
    NoL34Layer (fieldAutT (coordinateQuadPlus n K) σ S.hQσ) := by
  refine noL34Layer_fieldAutT S ?_
  have hmodel : LieModel (matrixProjectiveDerived (coordinateQuadPlus n k)) .POmegaPlus n ℓ e :=
    (lieModel_classical_iff (by decide)).mpr ⟨hadm, ↥k, inferInstance, inferInstance, hk,
      ⟨(statedProjectiveReindexEquiv (plusIndexEquiv n) (quadPlus n k) (coe_quadPlus n k)).symm⟩⟩
  exact not_isLThreeFour_of_lieModel_odd hO hℓ2 hmodel

theorem noL34Layer_fieldAutT_minus (hO : LieOrderFormulasInput) {n ℓ e : ℕ} (hn : 1 ≤ n)
    (hadm : StatedLieAdmissible .POmegaMinus n ℓ e) (hℓ2 : ℓ ≠ 2) (hk : Nat.card k = ℓ ^ e)
    (b c : k) (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0)
    (S : SubfieldSetup k (coordinateQuadMinus n k hn b c)
      (coordinateQuadMinus n K hn (b : K) (c : K)) σ p) :
    NoL34Layer (fieldAutT (coordinateQuadMinus n K hn (b : K) (c : K)) σ S.hQσ) := by
  refine noL34Layer_fieldAutT S ?_
  have hmodel : LieModel (matrixProjectiveDerived (coordinateQuadMinus n k hn b c)) .POmegaMinus n
      ℓ e :=
    (lieModel_classical_iff (by decide)).mpr ⟨hadm, ↥k, inferInstance, inferInstance, hk, b, c,
      hirr, ⟨(statedProjectiveReindexEquiv (minusIndexEquiv n hn) (quadMinus n k b c)
        (coe_quadMinus n k b c)).symm⟩⟩
  exact not_isLThreeFour_of_lieModel_odd hO hℓ2 hmodel

end Tags

end CFSG.HardMathSupport.Dickson.Sec6.OutSpOrth
