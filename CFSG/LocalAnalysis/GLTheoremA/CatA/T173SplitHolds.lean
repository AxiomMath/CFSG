module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173XDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.T173SplitVanish

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.T173S

open CFSG.LocalAnalysis.GLTheoremA.T173X

theorem modelFactSplit : ModelFactSplit := by
  intro F _ _ _ V _ _ _ Q l p hQ hdim hl hp hp2 hpq A d hA hd
  rintro ⟨T, hT0, hT2, hT⟩
  exact hT0 (eq_bot_of_closureIn_le_normalizer hQ hdim hl hp hp2 hpq hA hd.1 hd.2.2.2.1 hd.2.2.2.2
    hT2 (le_sup_left.trans hT))

end CFSG.LocalAnalysis.GLTheoremA.T173S

end
