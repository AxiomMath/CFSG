module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4StrongAssembly
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4Fix11
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4CentralizerH11

public noncomputable section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


theorem card_centralizer_qx_le : Nat.card (Subgroup.centralizer ({qx} : Set J)) ≤ 242 := by
  obtain ⟨h, hh, hord, hcard⟩ := card_centralizer_qx
  rw [hcard]
  have := card_centralizer_H_eleven_le h hh hord
  omega

theorem centralizer_qz_le_normalizer_J4 :
    Subgroup.centralizer ({qz} : Set J) ≤ Subgroup.normalizer (Q11 : Set J) :=
  centralizer_qz_le_normalizer card_centralizer_qx_le

theorem normalizer_zpowers_qz_eq_J4 :
    Subgroup.normalizer ((Subgroup.zpowers qz : Subgroup J) : Set J) =
      Subgroup.normalizer (Q11 : Set J) :=
  normalizer_zpowers_qz_eq card_centralizer_qx_le

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
