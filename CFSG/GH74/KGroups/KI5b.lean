module

public import CFSG.GH74.KGroups.KI5
public import CFSG.GH74.Uniqueness.SU.KInputsR3

public section

namespace CFSG.GH74.KGroups.KI5

theorem ki5b :
    CFSG.GH74.Uniqueness.SU.K.KI5b := by
  intro K _ _ hq hZp hZne he
  obtain ⟨e⟩ := he
  obtain ⟨-, -, -, h5, h6⟩ := ki5_parts K hq hZp hZne e
  exact ⟨h5, h6⟩

end CFSG.GH74.KGroups.KI5
