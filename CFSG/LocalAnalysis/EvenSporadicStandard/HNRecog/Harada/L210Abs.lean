module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L210CA
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L210NoSplit
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L210Strong
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L210Normal
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L210AbsA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.Open

variable {X : Type} [Group X] [Finite X] {A : Subgroup X} {w : X}
  {ψ : ↥(normalizer (A : Set X)) →* A5WrTwo}

theorem Abs210.toL210Hyp (h : Abs210 A w ψ) : L210Hyp A where
  elemAb := h.elemAb
  card := h.card
  centralizer_le := fun i hi hiA hi2 => L210_card_centralizer_le h hi hiA hi2
  noE16 := fun D hD hDe hDA => L210_card_le_eight h hD hDe hDA

theorem Abs210.normal (hGold : GoldschmidtTheoremA) (h : Abs210 A w ψ) : A.Normal := by
  obtain ⟨T, hTN, hAT, hclosed⟩ := L210_strongly_closed h.toL210Hyp
  exact L210_normal_of_theoremA hGold T hAT hTN h.elemAb hclosed (Abs210.hirr h) h.faithful
    (Abs210.hO2 h) (Abs210.hinv h) h.odd

end CFSG.EvenSporadicStandard.HNRecog.Harada
