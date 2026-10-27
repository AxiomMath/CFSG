module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenB
public import Certificates.Certificate17104

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven

theorem c0Seven_of_certificate :
    C0Seven := by
  have h := Certificates.certificate17104
  exact ⟨h.1, h.2⟩

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven
