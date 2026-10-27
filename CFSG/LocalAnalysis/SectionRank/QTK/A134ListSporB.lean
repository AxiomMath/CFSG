module

public import CFSG.LocalAnalysis.SectionRank.QTK.A134List0
public import CFSG.Blueprint.NativeSporadic
import CFSG.LocalAnalysis.SectionRank.QTK.A134ListSporC
import CFSG.LocalAnalysis.SectionRank.Sporadic.HSLocal
import CFSG.LocalAnalysis.SectionRank.Sporadic.HeLocal
import CFSG.LocalAnalysis.SectionRank.Sporadic.J2Local
import CFSG.LocalAnalysis.SectionRank.Sporadic.J4Local
import CFSG.LocalAnalysis.SectionRank.Sporadic.RuLocal

public section

namespace CFSG.SectionRank.QTK

open CFSG.Blueprint


theorem oddLocalWitness_matrixSporadic {s : TauCeti.SporadicName}
    (hs : s = .J2 ∨ s = .J4 ∨ s = .HS ∨ s = .He ∨ s = .Ru)
    [hfin : Finite (NativeSporadic.Carrier s)] : OddLocalWitness (NativeSporadic.Carrier s) := by
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · have : Finite NativeSporadic.J2 := hfin
    obtain ⟨x, y, h, hx, hy, hxy, hc, h1, h2⟩ := CFSG.SectionRank.J2_sylow5_square_witness
    exact oddLocalWitness_of_square_J2 hx hy hxy hc h1 h2
  · have : Finite NativeSporadic.J4 := hfin
    obtain ⟨x, y, h, hx, -, hz, hzx, hzy, -, h1, -, h3⟩ := CFSG.SectionRank.J4_sylow3_cubic_witness
    exact oddLocalWitness_of_cubic_J4 hx hz hzx hzy h1 h3
  · have : Finite NativeSporadic.HS := hfin
    obtain ⟨x, y, h, hx, hy, hxy, hc, h1, h2⟩ := CFSG.SectionRank.HS_sylow3_square_witness
    exact oddLocalWitness_of_square_HS hx hy hxy hc h1 h2
  · have : Finite NativeSporadic.He := hfin
    obtain ⟨x, y, h, hx, hy, hz, hzx, hzy, -, h1, h2, h3⟩ :=
      CFSG.SectionRank.He_sylow3_cubic_witness
    exact oddLocalWitness_of_cubic_He hx hy hz hzx hzy h1 h2 h3
  · have : Finite NativeSporadic.Ru := hfin
    obtain ⟨x, y, h, hx, -, hz, hzx, hzy, -, h1, -, h3⟩ := CFSG.SectionRank.Ru_sylow5_cubic_witness
    exact oddLocalWitness_of_cubic_Ru hx hz hzx hzy h1 h3

end CFSG.SectionRank.QTK
