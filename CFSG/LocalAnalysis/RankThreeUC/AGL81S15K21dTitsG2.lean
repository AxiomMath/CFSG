module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21dTitsBase
import CFSG.Adapters.TauCetiExceptional.EvenBridgeG2

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K21dTitsProof

open CFSG.Quasithin.H13 CFSG.QuasithinUnique

section G2


theorem solvOver_of_typeG2 {S : Type} [Group S] [Finite S] {Q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.G2 Q).Valid) (hQ : Q.p = 2)
    (e : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.G2 Q, hv⟩) {U : Subgroup S}
    (hU : IsSylowTwoOf U ⊤) : NQCat.SolvOver S U := by
  have hk := two_le_exponent_of_p_two hQ (card_ne_two_of_valid_G2 hv)
  have hq3 : 3 ≤ Q.card :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  obtain ⟨p, f, hp, hf⟩ := Q
  dsimp only at hQ hk
  subst hQ
  haveI : Fact (Nat.Prime 2) := ⟨hp⟩
  let F := GaloisField 2 f
  have hF : Nat.card F = (⟨2, f, hp, hf⟩ : TauCeti.PrimePower).card := by
    rw [GaloisField.card _ _ hf.ne', TauCeti.PrimePower.card_def]
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2
    (⟨2, f, hp, hf⟩ : TauCeti.PrimePower) hv rfl F hF
  have hmod : CFSG.Blueprint.ChevalleyExceptionalModel S .G2 2 f :=
    ⟨⟨hp, hf, rfl, by simpa [TauCeti.PrimePower.card_def] using hq3⟩, F, inferInstance,
      inferInstance, by simpa [TauCeti.PrimePower.card_def] using hF, ⟨e.trans b.symm⟩⟩
  exact NQCat.BN.solvOver_of_isG2 hk hmod hU

end G2

end K21dTitsProof

end CFSG.LocalAnalysis.RankThreeUC.S15
