module

public import CFSG.GH74.Generic.BProg.B2.PumpupTableL2
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLOrthData
import CFSG.GH74.Generic.S1.Exo.Q3HNoQ8L2

public section

namespace CFSG.GH74.Generic.BProg.B2.PumpupTableOmega3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
  CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification CFSG.ComponentClassification.Burgoyne.PSL
  CFSG.GH74.Generic.BProg.B2.PumpupTableBasic CFSG.GH74.Generic.BProg.B2.PumpupTableL2
open scoped Matrix MatrixGroups

theorem ker_traceZero_action {K : Type} [Field K] :
    (CatalogueBOrthogonal.traceZeroOrthogonalAction.comp
      (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin 2) K →* GL (Fin 2) K)).ker =
      center (Matrix.SpecialLinearGroup (Fin 2) K) := by
  ext A
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply,
    CatalogueBOrthogonal.traceZeroOrthogonalAction_eq_one_iff,
    Matrix.SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_, ?_⟩
    · have hd := congrArg Matrix.det (congrArg Units.val hc)
      rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hd
      rw [Fintype.card_fin]
      rw [hd]
      exact A.2
    · exact congrArg Units.val hc
  · rintro ⟨r, hr, hrA⟩
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [Fintype.card_fin, zero_pow (by norm_num)] at hr
      exact zero_ne_one hr
    refine ⟨Units.mk0 r hr0, Units.ext ?_⟩
    rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
    exact hrA

noncomputable def traceZeroSpecialImageEquiv (K : Type) [Field K] :
    ↥(traceZeroSpecialImage K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
  (QuotientGroup.quotientKerEquivRange (CatalogueBOrthogonal.traceZeroOrthogonalAction.comp
      (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin 2) K →* GL (Fin 2) K))).symm.trans
    (QuotientGroup.quotientMulEquivOfEq ker_traceZero_action)

theorem omega3_equiv_psl2 {K : Type} [Field K] [Finite K] (hK : ringChar K ≠ 2)
    (h3 : Nat.card K ≠ 3) (R : GL (Fin 3) K) (hR : (R : Matrix (Fin 3) (Fin 3) K)ᵀ = R) :
    Nonempty (↥(⁅CatalogueBGraphForm.isometryGroup 3 K R, CatalogueBGraphForm.isometryGroup 3 K R⁆ :
      Subgroup (GL (Fin 3) K)) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) := by
  have hodd := CatalogueBLinearHigherB.odd_card_of_ringChar_ne_two K hK
  have hQnd := CatalogueBLinearHigherB.polarBilin_matrixQuadraticForm_nondegenerate hK R hR
  have hdim : Module.finrank K (Fin 3 → K) = 3 := Module.finrank_fin_fun K
  obtain ⟨d, ψ, e, -, -, hcomm, -, -⟩ := orthogonal_three_derived hodd h3
    (CatalogueBLinearHigherB.matrixQuadraticForm R) hQnd hdim
  set eI := isoOrthGL hK R hR with heI
  let eA : ↥(commutator (TauCeti.QuadraticMap.orthogonalGroup
      (CatalogueBLinearHigherB.matrixQuadraticForm R))) ≃*
      ↥(⁅CatalogueBGraphForm.isometryGroup 3 K R, CatalogueBGraphForm.isometryGroup 3 K R⁆ :
        Subgroup (GL (Fin 3) K)) :=
    (((commutator (TauCeti.QuadraticMap.orthogonalGroup
      (CatalogueBLinearHigherB.matrixQuadraticForm R))).equivMapOfInjective _ eI.injective).trans
      (((commutator (TauCeti.QuadraticMap.orthogonalGroup
        (CatalogueBLinearHigherB.matrixQuadraticForm R))).map eI.toMonoidHom).equivMapOfInjective _
        (CatalogueBGraphForm.isometryGroup 3 K R).subtype_injective)).trans
      (MulEquiv.subgroupCongr (trans_commutator eI))
  let eB : ↥(commutator (TauCeti.QuadraticMap.orthogonalGroup
      (CatalogueBLinearHigherB.matrixQuadraticForm R))) ≃* ↥(traceZeroSpecialImage K) :=
    (MulEquiv.subgroupCongr hcomm).trans
      ((traceZeroSpecialImage K).equivMapOfInjective e.symm.toMonoidHom e.symm.injective).symm
  exact ⟨(eA.symm.trans eB).trans (traceZeroSpecialImageEquiv K)⟩

theorem lieModel_psl2_of_equiv {X : Type} [Group X] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (h4 : 4 ≤ p ^ f) {F : Type} [Field F] [Finite F] (hF : Nat.card F = p ^ f)
    (e : X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) : LieModel X .PSL 2 p f := by
  have hadm : StatedLieAdmissible .PSL 2 p f := by
    refine ⟨hp, hf, le_rfl, ?_, ?_⟩
    · intro h
      have := congrArg Prod.snd h
      simp only at this
      omega
    · intro h
      have := congrArg Prod.snd h
      simp only at this
      omega
  exact Or.inl ⟨by decide, hadm, F, inferInstance, inferInstance, hF,
    ⟨e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 F)⟩⟩

section Certified


theorem false_of_psl2_component {N : Type} [Group N] [Finite N] {H L : Subgroup N} {t : N}
    (hs : ShapeInCent H t L) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hL : LieModel ↥L .PSL 2 p f) :
    False := by
  obtain ⟨Z, _, hZo, hZn, hsh⟩ := hs.shape
  have hst := stated_of_lieModel (Or.inl rfl) hL
  rcases hsh with h1 | h3 | h4 | h5
  · obtain ⟨ψ, hψ⟩ := q8_in_H_of_shape (le_refl L) hZn hZo (exists_q8_of_shape13 (Or.inl h1))
    exact CFSG.GH74.Generic.S1.Exo.no_q8_of_psl2_model hp hp2 hst ψ hψ
  · obtain ⟨ψ, hψ⟩ := q8_in_H_of_shape (le_refl L) hZn hZo (exists_q8_of_shape13 (Or.inr h3))
    exact CFSG.GH74.Generic.S1.Exo.no_q8_of_psl2_model hp hp2 hst ψ hψ
  · exact (rankCertified_in_H_of_shape (le_refl L) hZn
      (rankCertified_of_shape45 (Or.inl h4))).not_sectionalTwoRankLE
      (sectionalTwoRankLE_two_of_psl2_model hp2 hL)
  · exact (rankCertified_in_H_of_shape (le_refl L) hZn
      (rankCertified_of_shape45 (Or.inr h5))).not_sectionalTwoRankLE
      (sectionalTwoRankLE_two_of_psl2_model hp2 hL)

end Certified

end CFSG.GH74.Generic.BProg.B2.PumpupTableOmega3
