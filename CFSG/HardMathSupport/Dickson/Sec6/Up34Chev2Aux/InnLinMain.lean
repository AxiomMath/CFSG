module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnLin
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Bridge
public import CFSG.RankThree.PartOne.KC.LinearCommutantSemi
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Basic
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Split

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification
  CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2 CFSG.ComponentClassification.CatLeaf
  CFSG.RankThree.PartOne.Sec66T

namespace Up34Chev2

section Model

variable {n e : ℕ} {K : Type} [Field K] [Finite K]

theorem slConjugation_toGL (g u : Matrix.SpecialLinearGroup (Fin n) K) :
    CatalogueBHigherLinearAction.slConjugation n K (Matrix.SpecialLinearGroup.toGL g) u =
      g * u * g⁻¹ := by
  apply Subtype.ext
  rw [CatalogueBHigherLinearAction.slConjugation_matrix, ← map_inv,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  rfl

theorem not_up34Pumpup_conjAut_psl (hO : LieOrderFormulasInput)
    (hn : 4 ≤ n) (hK : Nat.card K = 2 ^ e) (A : GL (Fin n) K) :
    ¬ Up34Pumpup (LinearFlag.projectiveSL n K) (LinearFlag.conjAut n K A) := by
  intro hpump
  have h1 : LinearFlag.conjAut n K (A ^ 3) = 1 := by rw [map_pow]; exact hpump.1
  obtain ⟨c, hc⟩ := (CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff (by omega) (A ^ 3)).1 h1
  exact ((up34Pumpup_iff _).1 hpump).2.2 (noL34Layer_conjAut_psl_two hO hn hK hc.symm)

theorem not_up34Pumpup_conj_psl (hO : LieOrderFormulasInput)
    (hn : 4 ≤ n) (hK : Nat.card K = 2 ^ e) (y : LinearFlag.projectiveSL n K) :
    ¬ Up34Pumpup (LinearFlag.projectiveSL n K) (MulAut.conj y) := by
  obtain ⟨g, rfl⟩ := LinearFlag.proj_surjective n K y
  have : MulAut.conj (LinearFlag.proj n K g) =
      LinearFlag.conjAut n K (Matrix.SpecialLinearGroup.toGL g) := by
    ext z
    obtain ⟨u, rfl⟩ := LinearFlag.proj_surjective n K z
    rw [LinearFlag.conjAut_proj, slConjugation_toGL, MulAut.conj_apply, map_mul, map_mul, map_inv]
  rw [this]
  exact not_up34Pumpup_conjAut_psl hO hn hK _

end Model

noncomputable def statedProjSLEquiv_c2 (n : ℕ) (K : Type) [Field K] :
    StatedProj (StatedSL n K) ≃* LinearFlag.projectiveSL n K :=
  (projectiveSpecialLinearGroupEquivStatedProj n K).symm.trans
    (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K)

section Closed


theorem up34C2Inn_AHigh_holds : Up34Chev2Inn FamAHigh := by
  intro S _ _ hs hnab d hF hc ⟨e⟩ x hpump
  obtain ⟨d, hv⟩ := d
  cases d with
  | A r q =>
    have hr : 3 ≤ r := hF
    have hp : q.p = 2 := hc
    have hm := blueprintLieModel_A r q hv e
    obtain ⟨-, K, _, _, hK, ⟨e0⟩⟩ := (lieModel_classical_iff (by decide)).mp hm
    rw [hp] at hK
    let e' : S ≃* LinearFlag.projectiveSL (r + 1) K := e0.trans (statedProjSLEquiv_c2 (r + 1) K)
    haveI : Finite (LinearFlag.projectiveSL (r + 1) K) := Finite.of_equiv S e'.toEquiv
    have hpump' := hpump.of_congr e'
    rw [CFSG.RankThree.PartTwo.KFacts.congr_mulAutConj] at hpump'
    exact not_up34Pumpup_conj_psl CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
      (by omega) hK (e' x) hpump'
  | _ => exact hF.elim

end Closed

end Up34Chev2

end CFSG.HardMathSupport.Dickson.Sec6
