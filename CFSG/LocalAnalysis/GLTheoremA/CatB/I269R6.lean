module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I269T
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I269R5

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

section Certs


theorem i269Residual3_holds : I269Residual3 := by
  intro S _ hcat
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  rcases hi with h1 | h1
  · exact e9Solv_d4two S ⟨i, h1, ⟨e⟩⟩
  · exact e9Solv_u3eight S ⟨i, h1, ⟨e⟩⟩

end Certs

end CFSG.LocalAnalysis.GLTheoremA

end
