module

public import CFSG.ClassicalInvolution.Q3.TA3SOLDefs
public import CFSG.ClassicalInvolution.Q3.TA3SOLL4U4Shape
public import CFSG.ClassicalInvolution.Q3.TA3SOLSp4Cent
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Classify

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.ClassicalInvolution CFSG.Assembly.LowTwoRank CFSG.ComponentClassification
open CFSG.ComponentClassification.CatFactsSp4

section Model

variable {K : Type} [Field K]

theorem Sp4.twoSL2Shape_u1 (h2 : (2 : K) ≠ 0) :
    TwoSL2Shape (StatedProj (StatedSp 2 K)) (u1 K) K :=
  ⟨E1 K, E2 K, (E1_le_X0 h2).trans X0_le_centralizer, (E2_le_X0 h2).trans X0_le_centralizer,
    fun _ ha _ hb => commute_E1_E2 ha hb, ⟨(E1Equiv h2).symm⟩, ⟨(E2Equiv h2).symm⟩⟩

theorem Sp4.normalSimpleShape_u2 [Finite K] (h2 : (2 : K) ≠ 0) (h4 : 4 ≤ Nat.card K) :
    NormalSimpleShape (StatedProj (StatedSp 2 K)) (u2 K) :=
  ⟨Lsub K, Lsub_le_centralizer, Sp4.centralizer_u2_le_normalizer_Lsub h2 h4,
    isSimpleGroup_Lsub h4, Sp4.isPerfect_Lsub h4,
    fun _ ha _ hb => Sp4.commute_of_mem_centralizer_Lsub h2 ha hb⟩

end Model

theorem noDatumSp4_holds : NoDatumSp4 := by
  intro X _ _ _ p f hp hp2 h5 hm hF ⟨R, S, t, hD⟩
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hm
  have hodd : Odd (Nat.card K) := by rw [hK]; exact (hp.odd_of_ne_two hp2).pow
  have h4 : 4 ≤ Nat.card K := by rw [hK]; omega
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_card hodd
  have ht : orderOf (e t) = 2 := by rw [MulEquiv.orderOf_eq]; exact hD.order
  obtain ⟨g, hg⟩ := CatFactsSp4.exists_conj_of_orderOf_eq_two hodd ht
  let e' : X ≃* StatedProj (StatedSp 2 K) := e.trans (MulAut.conj g⁻¹)
  have hte : e' t = g⁻¹ * e t * g := by
    simp only [e', MulEquiv.trans_apply, MulAut.conj_apply, inv_inv]
  rcases hg with hg | hg
  · have h1 : TwoSL2Shape (StatedProj (StatedSp 2 K)) (e' t) K := by
      rw [hte, hg]
      exact Sp4.twoSL2Shape_u1 h2
    exact not_fourGenerated_of_twoSL2Shape hD hodd h4 (TwoSL2Shape.of_mulEquiv e' h1) hF
  · have h1 : NormalSimpleShape (StatedProj (StatedSp 2 K)) (e' t) := by
      rw [hte, hg]
      exact Sp4.normalSimpleShape_u2 h2 h4
    exact false_of_normalSimpleShape hD (NormalSimpleShape.of_mulEquiv e' h1)

end CFSG.ClassicalInvolution.Q3.TA3
