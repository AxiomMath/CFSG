module

public import CFSG.LargeExtraspecial.S13EightF
public import CFSG.LargeExtraspecial.S10EightV
public import CFSG.LargeExtraspecial.S9RCMain
public import CFSG.LargeExtraspecial.S14Claims
public import CFSG.LargeExtraspecial.S13EntryD

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S13

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S10

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem timmesfeld_13_9
    (hCE : CentralExtInput.{u}) {t : S.O} (X : Hyp10 S g t) (hNo : S11.NoA2All S)
    (hirr : ¬ S.IsReducible) (h7 : 7 ≤ S.width) : Bridge.TimmesfeldAlt3 S.width S.Mbar := by
  obtain ⟨P, hPM, hP1, hP3, hPn⟩ := timmesfeld_10_8_o3 hCE (noPGL25 S g) hNo X h7
  have Y := hyp13_of hPM hP1 hP3 hPn X h7 hirr hCE hNo (noPGL25 S g)
  rcases timmesfeld_13_4 hCE Y with h | hii
  · exact h
  · exact (Hyp13.timmesfeld_13_8 hCE Y hii).elim

theorem s13_9Stmt_of
    (hCE : CentralExtInput.{0}) : S14.S13_9Stmt := by
  intro G _ _ _ S g t X hNo hirr h7
  exact timmesfeld_13_9 hCE X hNo hirr h7

end CFSG.LargeExtraspecial.S13
