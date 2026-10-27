module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivialSporadicD2
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointExoticSigMcL

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivial

open CFSG.Blueprint CFSG.LocalAnalysis.RankFourTheoremC CFSG.AGLEmbeddingD2

theorem center_eq_bot_of_mulEquiv_mcl {K : Type} [Group K]
    (e : K ≃* NativeSporadic.McL) : Subgroup.center K = ⊥ := by
  have hs : IsSimpleGroup K :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.McL.isSimpleGroup_McL e
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h | h
  · exact h
  · exfalso
    have hc : IsMulCommutative K := Subgroup.center_eq_top_iff.mp h
    have hp : (Nat.card K).Prime := Group.is_simple_iff_prime_card.mp hs
    rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.McL.card_McL] at hp
    exact absurd hp (by norm_num)


theorem signalizerTrivialMcL_holds : SignalizerTrivialMcL := by
  intro K _ _ hK
  obtain ⟨e⟩ := hK
  obtain ⟨eC⟩ := CFSG.Sporadic.Bridge.McL.nonempty_mulEquiv
  have e' : K ≃* NativeSporadic.McL := e.trans eC.symm
  exact signalizerTrivialOn_of_d2Heis Nat.prime_five d2HeisLocalAt_mcl (signalizerAutAt_mcl rfl)
    ⟨e⟩ (center_eq_bot_of_mulEquiv_mcl e')

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivial
