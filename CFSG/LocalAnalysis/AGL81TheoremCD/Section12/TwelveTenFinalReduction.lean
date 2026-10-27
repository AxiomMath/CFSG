module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.CGT6.Emb5NinePair
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixToNineStmt
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltCenter
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.H13.L32NSp4Over
public import CFSG.Quasithin.Vol2.Ch11SecOE5B
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

@[expose] def centralizerInJ (M H B : Subgroup G) : Subgroup G :=
  Subgroup.centralizer (B : Set G) ⊓ jSub M H

@[expose] def TwelveTenFinalA (M H Q : Subgroup G) (p : ℕ) : Prop :=
  ∃ E D : Subgroup G,
    E ≤ Q ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
      rankThreeGamma 1 p E ≤ M ∧
      IsThreeOnePlusTwo ↥D ∧ D ≤ Q ∧ E ≤ D

theorem seven_dvd_card_of_isL3TwoPow_one {X : Type} [Group X] [Finite X]
    (h : IsL3TwoPow 1 X) : 7 ∣ Nat.card X := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  rw [CFSG.OrderReductions.LinearOrders.card_projectiveSpecialLinear (GaloisField 2 1) 3
    (by norm_num)]
  rw [GaloisField.card 2 1 (by norm_num)]
  rw [show Finset.Icc 2 3 = ({2, 3} : Finset ℕ) by decide, Finset.prod_pair (by norm_num)]
  norm_num

theorem seven_dvd_card_of_quotient_isL3TwoPow_one {Y : Type} [Group Y] [Finite Y]
    (N : Subgroup Y) [N.Normal] (h : IsL3TwoPow 1 (Y ⧸ N)) : 7 ∣ Nat.card Y :=
  (seven_dvd_card_of_isL3TwoPow_one h).trans (Subgroup.card_quotient_dvd_card N)

theorem dvd_card_inf_map_conj_of_dvd_centralizer
    {M J E : Subgroup G} {x : G} (hJM : J ≤ M)
    (hN : Subgroup.normalizer (E : Set G) ≤ M)
    (h7 : 7 ∣ Nat.card (Subgroup.centralizer
      ((E.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) ⊓ J : Subgroup G)) :
    7 ∣ Nat.card (M ⊓ M.map (MulAut.conj x).toMonoidHom : Subgroup G) := by
  let C : Subgroup G :=
    Subgroup.centralizer ((E.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) ⊓ J
  have hCM : C ≤ M := fun y hy => hJM hy.2
  have hCnorm : C ≤ Subgroup.normalizer
      ((E.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) :=
    fun y hy => Subgroup.centralizer_le_normalizer _ hy.1
  have hNx : Subgroup.normalizer
      ((E.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) ≤
        M.map (MulAut.conj x).toMonoidHom := by
    rw [← Subgroup.map_equiv_normalizer_eq E (MulAut.conj x)]
    exact Subgroup.map_mono hN
  have hCinf : C ≤ M ⊓ M.map (MulAut.conj x).toMonoidHom :=
    le_inf hCM (hCnorm.trans hNx)
  exact h7.trans (Subgroup.card_dvd_of_le hCinf)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
