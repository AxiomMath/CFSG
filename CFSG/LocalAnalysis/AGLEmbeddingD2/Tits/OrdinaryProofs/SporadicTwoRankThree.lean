module

public import CFSG.LocalAnalysis.SectionRank.SimpleList
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.AltThreeRank

public section

namespace CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs

open CFSG.Open

theorem two_le_pRank_three_sporadic {s : TauCeti.SporadicName}
    (hE : ∃ E : Subgroup (CFSG.Blueprint.NativeSporadic.Carrier s),
      CFSG.Open.IsElemAbelian 3 E ∧ ∃ k : ℕ, 3 ≤ k ∧ Nat.card E = 3 ^ k)
    (hbr : Nonempty (CFSG.Blueprint.NativeSporadic.Carrier s ≃*
      (TauCeti.CFSGIndex.sporadic s).Group))
    {S : Type} [Group S] [Finite S]
    (hS : Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic s).Group)) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) := by
  obtain ⟨b⟩ := hbr
  obtain ⟨e⟩ := hS
  have e' : S ≃* CFSG.Blueprint.NativeSporadic.Carrier s := e.trans b.symm
  obtain ⟨E, hEa, k, hk, hc⟩ := hE
  have : Finite (CFSG.Blueprint.NativeSporadic.Carrier s) := Finite.of_equiv S e'.toEquiv
  have hlift : k ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (CFSG.Blueprint.NativeSporadic.Carrier s)) :=
    le_pRank_of_elemAbelian_card (by norm_num) le_top hEa hc
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e']
  exact le_trans (by omega) (le_trans hk hlift)

theorem two_le_pRank_three_sporadic_all
    (hW : CFSG.SectionRank.SporadicThreeRankWitnesses) {s : TauCeti.SporadicName}
    (hs : s ∉ CFSG.SectionRank.sqtkSporadicNames) (hM : s ≠ .M)
    (hbr : Nonempty (CFSG.Blueprint.NativeSporadic.Carrier s ≃*
      (TauCeti.CFSGIndex.sporadic s).Group))
    {S : Type} [Group S] [Finite S]
    (hS : Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic s).Group)) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) :=
  two_le_pRank_three_sporadic (hW s hs hM) hbr hS

end CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs

end
