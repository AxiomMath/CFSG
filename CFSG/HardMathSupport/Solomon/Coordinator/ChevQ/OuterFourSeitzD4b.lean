module

public import CFSG.RankThree.PartOne.KC.CommonEigenbasis
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434G28Check

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitz2

open CFSG.Open

section Escape

open CFSG.RankThree.PartTwo Matrix

theorem exists_conj_diagonal_of_pow_eq_one {ι : Type} [Fintype ι] [DecidableEq ι] {E' : Type}
    [Field E'] {p : ℕ} [NeZero p] {ω : E'} (hω : IsPrimitiveRoot ω p) (B : Matrix ι ι E')
    (hB : B ^ p = 1) :
    ∃ (T : GL ι E') (d : ι → E'),
      (T : Matrix ι ι E') * B * ((T⁻¹ : GL ι E') : Matrix ι ι E') = diagonal d ∧
        ∀ i, d i ^ p = 1 := by
  obtain ⟨b, μ, hb⟩ := CFSG.RankThree.PartOne.exists_basis_common_eigenvectors_of_pow_eq_one hω
    (fun _ : Unit => Matrix.toLinAlgEquiv' B) (fun _ _ => Commute.refl _)
    (fun _ => by rw [← map_pow, hB, map_one])
  let e : Fin (Module.finrank E' (ι → E')) ≃ ι :=
    (finCongr (Module.finrank_pi E')).trans (Fintype.equivFin ι).symm
  let b' : Module.Basis ι E' (ι → E') := b.reindex e
  let d : ι → E' := fun i => μ () (e.symm i)
  have hb' : ∀ j, B.mulVec (b' j) = d j • b' j := by
    intro j
    have := hb () (e.symm j)
    simpa [b', d, Module.Basis.reindex_apply] using this
  let P : Matrix ι ι E' := (Pi.basisFun E' ι).toMatrix b'
  have hPi : Invertible P := Module.Basis.invertibleToMatrix (Pi.basisFun E' ι) b'
  have hBP : B * P = P * diagonal d := by
    ext a j
    have h := congrFun (hb' j) a
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
    rw [Matrix.mul_diagonal]
    simp only [P, Matrix.mul_apply, Module.Basis.toMatrix_apply, Pi.basisFun_repr]
    rw [h, mul_comm]
  have hdp : ∀ i, d i ^ p = 1 := by
    intro i
    have hpow : ∀ m : ℕ, (B ^ m).mulVec (b' i) = d i ^ m • b' i := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ, ← Matrix.mulVec_mulVec, hb', Matrix.mulVec_smul, ih, smul_smul, pow_succ]
        ring_nf
    have h3 := hpow p
    rw [hB, Matrix.one_mulVec] at h3
    have hne : b' i ≠ 0 := b'.ne_zero i
    have h4 : (1 - d i ^ p) • b' i = 0 := by
      rw [sub_smul, one_smul, ← h3, sub_self]
    rcases smul_eq_zero.mp h4 with h5 | h5
    · exact (sub_eq_zero.mp h5).symm
    · exact absurd h5 hne
  let Pu : GL ι E' := unitOfInvertible P
  refine ⟨Pu⁻¹, d, ?_, hdp⟩
  have h1 : ((Pu⁻¹ : GL ι E') : Matrix ι ι E') = ⅟P := rfl
  have h2 : (((Pu⁻¹)⁻¹ : GL ι E') : Matrix ι ι E') = P := by simp [Pu]
  rw [h1, h2, Matrix.mul_assoc, hBP, ← Matrix.mul_assoc, invOf_mul_self, Matrix.one_mul]

end Escape

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitz2
