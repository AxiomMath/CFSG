module

import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.OmegaMinusCentThree
import CFSG.LocalAnalysis.RankThreeTheoremC.ChevTwoInnerRankUnitary
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Sp62RankDefs
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding CFSG.ClassicalGroups.Orthogonal

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem four_le_pRank_of_uSixTwo {X : Type} [Group X] [Finite X] {A : Subgroup X}
    {d : TauCeti.ValidLieTypeIndex} (hd : IsUSixTwoIndex d) (e : Nonempty (↥A ≃* CatGroup d)) :
    4 ≤ Open.pRank 3 A := by
  obtain ⟨q, hq2, hq1, hdq⟩ := hd
  obtain ⟨e⟩ := e
  obtain ⟨c, hv⟩ := d
  simp only at hdq
  subst hdq
  obtain ⟨U, hU, hcard⟩ := ChevTwoInnerRank.centralCoverFour_twistedA5Two q hv hq2 hq1
    ↥A e.toMonoidHom e.surjective (by
      intro y hy
      have : y = 1 := e.injective (by simpa using hy)
      simp [this])
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
  exact CFSG.SectionRank.le_pRank Nat.prime_three.one_lt le_top hU hcard

theorem five_le_pRank_of_omegaMinus {X : Type} [Group X] [Finite X] {A : Subgroup X} {m : ℕ}
    (hm : 5 ≤ m) {d : TauCeti.ValidLieTypeIndex} (hd : IsOmegaMinusTwoIndex m d)
    (e : Nonempty (↥A ≃* CatGroup d)) : 5 ≤ Open.pRank 3 A := by
  obtain ⟨eL⟩ := OmegaMinusCent.omegaMinusModel hd e
  obtain ⟨P, P', hPP'⟩ := OmegaMinusCent.exists_orth_hypPair (m := m) (by omega)
  obtain ⟨Y, hYE, -, hY3, hYcomm, hYcard⟩ := OmegaMinusCent.exists_three_groups
    (OmegaMinusCent.nondegenerate_minusForm m) hm
    (OmegaMinusCent.finrank_minusSpace (by omega))
    (fun T hT => OmegaMinusCent.finrank_le_minusForm hT) hPP' (x := 1) (Subgroup.one_mem _)
    (one_pow 3) 5 le_rfl
  obtain ⟨Y', hmem, hcard'⟩ := OmegaMinusCent.exists_pullback_subgroup eL hYE
  have hinj : ∀ a b : ↥A, ((eL a : elementaryGroup (OmegaMinusCent.minusForm m)) :
      OmegaMinusCent.MinusSpace m ≃ₗ[ZMod 2] OmegaMinusCent.MinusSpace m) = (eL b : _) →
      a = b := fun a b h => eL.injective (Subtype.ext h)
  have hel : Open.IsElemAbelian 3 Y' := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun g hg => ?_⟩
    · apply hinj
      simpa using hYcomm _ ((hmem a).1 a.2) _ ((hmem b).1 b.2)
    · apply hinj
      simpa using hY3 _ ((hmem g).1 hg)
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
  exact CFSG.SectionRank.le_pRank Nat.prime_three.one_lt le_top hel (hcard'.trans hYcard)

theorem four_le_pRank_top_of_uSixTwo {Y : Type} [Group Y] [Finite Y]
    {d : TauCeti.ValidLieTypeIndex} (hd : IsUSixTwoIndex d) (e : Nonempty (Y ≃* CatGroup d)) :
    4 ≤ Open.pRank 3 (⊤ : Subgroup Y) := by
  obtain ⟨e⟩ := e
  exact four_le_pRank_of_uSixTwo (A := ⊤) hd ⟨Subgroup.topEquiv.trans e⟩

theorem five_le_pRank_top_of_omegaMinus {Y : Type} [Group Y] [Finite Y] {m : ℕ} (hm : 5 ≤ m)
    {d : TauCeti.ValidLieTypeIndex} (hd : IsOmegaMinusTwoIndex m d)
    (e : Nonempty (Y ≃* CatGroup d)) : 5 ≤ Open.pRank 3 (⊤ : Subgroup Y) := by
  obtain ⟨e⟩ := e
  exact five_le_pRank_of_omegaMinus (A := ⊤) hm hd ⟨Subgroup.topEquiv.trans e⟩

theorem kFactU62ThreeRank : KFactU62ThreeRank :=
  fun _ _ _ _ hd e => four_le_pRank_top_of_uSixTwo hd e

theorem kFactOmegaMinusThreeRank : KFactOmegaMinusThreeRank := fun _ _ _ m _ hm hd e =>
  (by norm_num : 4 ≤ 5).trans (five_le_pRank_top_of_omegaMinus hm hd e)

end CFSG.LocalAnalysis.RankThreeTheoremC
