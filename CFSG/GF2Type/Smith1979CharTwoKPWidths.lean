module

public import CFSG.GF2Type.Smith1979CharTwoWidths
public import CFSG.GF2Type.Smith1979W3.KProper
public import CFSG.GF2Type.Smith1979CharTwoKP

public section

namespace CFSG.GF2Type

open CFSG CFSG.Blueprint CFSG.Open

section Certs


theorem smith1979CharTwoKP_of_widthsKP
    (h3 : CFSG.GF2Type.Smith1979W3.Smith1979WidthThreeCharTwoKP)
    (h46 : Smith1979WidthsFourSixCharTwoKP) : Smith1979StatementCharTwoKP := by
  intro G _ _ _ hnonab hchar hKP z hz hext w hcard
  exact ⟨h3 G hnonab hchar hKP z hz hext w hcard, (h46 G hnonab hchar hKP z hz hext w hcard).1,
    (h46 G hnonab hchar hKP z hz hext w hcard).2,
    smith1979_widths_eleven_twelve_charTwo hchar hz hext hcard⟩

end Certs

end CFSG.GF2Type
