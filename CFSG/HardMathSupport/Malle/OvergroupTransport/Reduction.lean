module

public import CFSG.LocalAnalysis.AGLEmbedding.ReeF4Defs
public import CFSG.HardMathSupport.Malle.OvergroupTransport.Maximal

public section

namespace CFSG.HardMathSupport.Malle.OvergroupTransport

open CFSG.AGLEmbedding CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def ReeF4NormalizerStructure : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y) (d : TauCeti.ValidLieTypeIndex),
    IsReeFFourFiveIndex d → K.Normal → Nonempty (K ≃* CatGroup d) →
    Subgroup.centralizer (K : Set Y) = ⊥ → ∀ T : Sylow 5 Y,
      3 ≤ Open.pRank 5 (T : Subgroup Y) →
      ReeF4InSitu (T : Subgroup Y) (Subgroup.normalizer ((T : Subgroup Y) : Set Y)) ∧
        centerOf (T : Subgroup Y) ≤ K

@[expose] def ReeF4NormalizerMaximal : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y) (d : TauCeti.ValidLieTypeIndex),
    IsReeFFourFiveIndex d → K.Normal → Nonempty (K ≃* CatGroup d) →
    Subgroup.centralizer (K : Set Y) = ⊥ → ∀ T : Sylow 5 Y,
      3 ≤ Open.pRank 5 (T : Subgroup Y) →
      ∀ H : Subgroup Y, Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ H →
        H = Subgroup.normalizer ((T : Subgroup Y) : Set Y) ∨ H = ⊤

theorem kFactReeF4Local_of_structure_of_maximal (hS : ReeF4NormalizerStructure)
    (hM : ReeF4NormalizerMaximal) : KFactReeF4Local := by
  intro Y _ _ K d hd hKn hiso hC T Y₀ h3 hY₀ hne
  obtain ⟨hstruct, hZK⟩ := hS Y K d hd hKn hiso hC T h3
  have h2 : 2 ≤ CFSG.Open.pRank 5
      ((T : Subgroup Y) ⊓ Subgroup.centralizer ((T : Subgroup Y) : Set Y)) :=
    le_pRank_of_elemAbelian (by norm_num) le_rfl hstruct.center_elem hstruct.center_card
  have hN : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ Y₀ :=
    normalizer_le_of_weakCore_le h2 h3 hY₀
  rcases hM Y K d hd hKn hiso hC T h3 Y₀ hN with h | h
  · rw [h]
    exact ⟨hstruct, hZK⟩
  · exact absurd h hne

end CFSG.HardMathSupport.Malle.OvergroupTransport
