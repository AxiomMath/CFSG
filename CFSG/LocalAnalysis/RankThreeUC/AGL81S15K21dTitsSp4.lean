module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21dTitsBase
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522D42Ident
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2Carrier

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K21dTitsProof

open CFSG.Quasithin.H13 CFSG.QuasithinUnique

theorem solvOver_of_typeB2 {S : Type} [Group S] [Finite S] {Q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.B 2 Q).Valid) (hQ : Q.p = 2)
    (e : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.B 2 Q, hv⟩) {U : Subgroup S}
    (hU : IsSylowTwoOf U ⊤) : NQCat.SolvOver S U := by
  have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 Q hv e
  rw [hQ] at hm
  exact D42.solvOver_of_isPSp4 (two_le_exponent_of_p_two hQ (card_ne_two_of_valid_B2 hv)) hm hU

end K21dTitsProof

end CFSG.LocalAnalysis.RankThreeUC.S15
