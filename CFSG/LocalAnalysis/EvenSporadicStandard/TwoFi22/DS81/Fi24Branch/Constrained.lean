module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi24Abstract
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.ConsCore
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.ConsR
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.ConsJ
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.ConsK
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.ConsCat
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.O2C

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup

variable {G : Type} [Group G] [Finite G] {L E : Subgroup G} {t z : G}

theorem isCharacteristicP_Cz (hs : StdHyp G L) (c : Core4 E t z)
    (hSch : CatalogOuterSolvable) (hB : DS81Lemma210Strong) :
    CFSG.IsCharacteristicP 2 ↥(Cz z) := by
  rcases O2In_Cz_eq_or c with h | h
  · exfalso
    have c1 : Core1 E t z := c.toCore3.toCore2.toCore1
    have c0 : Core0 E t z := c1.toCore0
    obtain ⟨Y, hK⟩ := kDataC c1
    obtain ⟨Y0, hY0⟩ := y0Data c0
    exact false_of_two_eq (cCore hs c0 h) (rData c) (jData c1) hK hY0 c0.u42 hSch hB
      (catSections hs c.klein.z_ne)
  · exact isCharacteristicP_of_O2C_eq c h

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
