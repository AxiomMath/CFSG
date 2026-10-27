module

public import CFSG.Assembly.E6FourNeighbourFacts
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.Assembly

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Holds


theorem e6FourMark_exists_adjointGroup {J : Type} [Group J] (hJ : E6FourMark J)
    (hZ : center J = ⊥) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ 2 ∧
      Nonempty (↥(adjointGroup Tag.E6 K) ≃* J) := by
  have hM := CFSG.StandardType.Canonical.largeEvenMarking_markedModel (L := J) hJ
  obtain ⟨-, lab', -, R, _, I, F, θ, -, -, hP, hMM⟩ :=
    CFSG.StandardType.Canonical.largeEvenMarking_exists hM
  obtain ⟨tag, rank, n⟩ := lab'
  obtain ⟨htag, hn⟩ := hP
  simp only at htag hn
  subst htag
  subst hn
  have hC : CFSG.Blueprint.ChevalleyExceptionalModel R .E6 2 2 := by
    unfold CFSG.StandardType.MarkedModel at hMM
    simp only [CFSG.StandardType.markTag, CFSG.StandardType.markRank, CFSG.StandardType.markChar,
      CFSG.StandardType.markDeg] at hMM
    rcases hMM with ⟨h, -⟩ | ⟨-, -, hE6⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
    · exact absurd h (by decide)
    · exact hE6
    · exact absurd h (by decide)
    · exact absurd h (by simp)
  obtain ⟨-, K, iF, iFin, hK, ⟨e⟩⟩ := hC
  haveI : CharP K 2 := CFSG.StandardType.charP_two_of_card (m := 2) hK
  let eZ : AdjointQuotient Tag.E6 K ≃* ↥(adjointGroup Tag.E6 K) :=
    (QuotientGroup.quotientMulEquivOfEq (center_adjointGroup_eq_bot (τ := Tag.E6) (K := K))).trans
      QuotientGroup.quotientBot
  let eJ : J ≃* R :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans θ
  exact ⟨K, iF, iFin, inferInstance, hK, ⟨(eZ.symm.trans e.symm).trans eJ.symm⟩⟩

end Holds

end CFSG.Assembly

end
