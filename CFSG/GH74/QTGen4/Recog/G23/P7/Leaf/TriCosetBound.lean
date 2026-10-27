module

public import Certificates.Certificate320013
public import CFSG.GH74.QTGen4.Recog.G23.P7.OpenLeaves

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Recog.G23.P7

open CFSG.CosetTable

section Certificate


theorem tri_check_cosets :
    (genSub {r : FreeGroup (Fin 6) | r ∈ triWords.map FreeGroup.mk}
        (subsetOf 6 [0, 1, 2, 3])).FiniteIndex ∧
      (genSub {r : FreeGroup (Fin 6) | r ∈ triWords.map FreeGroup.mk}
        (subsetOf 6 [0, 1, 2, 3])).index ≤ 14742 :=
  Certificates.certificate320013.1

theorem tri_check_triv :
    Finite (PG (subsetOf 6 [0, 1, 2, 3]).length (restrictWords (subsetOf 6 [0, 1, 2, 3]) triWords)) ∧
      Nat.card (PG (subsetOf 6 [0, 1, 2, 3]).length
        (restrictWords (subsetOf 6 [0, 1, 2, 3]) triWords)) ≤ 288 :=
  Certificates.certificate320013.2.1

end Certificate

theorem leafTriCosetBound : LeafTriCosetBound := by
  obtain ⟨hf, hc⟩ := CFSG.KC.MiscCoset.card_le_of_index_restrict triWords (subsetOf 6 [0, 1, 2, 3])
    tri_check_cosets tri_check_triv
  exact ⟨hf, hc.trans (by norm_num)⟩

end CFSG.GH74.QTGen4.Recog.G23.P7
