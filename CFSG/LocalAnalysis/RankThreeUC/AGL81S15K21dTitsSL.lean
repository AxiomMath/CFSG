module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21dTitsBase
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSL

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K21dTitsProof

open CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.AGLEmbedding.ParabHub

theorem solvOver_of_typeA3 {S : Type} [Group S] [Finite S] {Q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A 3 Q).Valid) (hQ : Q.p = 2)
    (e : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.A 3 Q, hv⟩) {U : Subgroup S}
    (hU : IsSylowTwoOf U ⊤) : NQCat.SolvOver S U := by
  have : Fact Q.p.Prime := ⟨Q.prime_p⟩
  have : CharP (GaloisField Q.p Q.exponent) 2 := CharP.congr Q.p hQ
  have hK : Nat.card (GaloisField Q.p Q.exponent) = Q.card := by
    rw [TauCeti.PrimePower.card_def, GaloisField.card Q.p Q.exponent Q.exponent_pos.ne']
  have hF4 : 4 ≤ Nat.card (GaloisField Q.p Q.exponent) := by
    rw [hK]
    exact four_le_card_of_p_two hQ (card_ne_two_of_valid_A3 hv)
  exact solvOver_of_borelQuotient
    (borelQuotient_sl ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 3 Q hv).symm.trans
      e.symm))
    (fun i => rankOne_not_solvable_of_hasSL2Node hF4 (hasSL2Node_sl i)) hU

end K21dTitsProof

end CFSG.LocalAnalysis.RankThreeUC.S15
