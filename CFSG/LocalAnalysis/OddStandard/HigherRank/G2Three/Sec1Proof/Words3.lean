module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FactsS
public import CFSG.RankThree.PartTwo.Census.Carrier.G2ThreeCodes

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec1Proof

open CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.RankThree.PartTwo.Census.Carrier.G2Three

variable {G : Type} [Group G] [Finite G]

@[expose] def sGen (fr : Frame G) (s : ℕ) : G :=
  if h : s < 6 then fr.gens11 ⟨s, h⟩ else 1

theorem sGen_zero (fr : Frame G) : sGen fr 0 = fr.a₁ := by
  simp [sGen, Frame.gens11]

theorem sGen_one (fr : Frame G) : sGen fr 1 = fr.b₁ := by
  simp [sGen, Frame.gens11]

theorem sGen_two (fr : Frame G) : sGen fr 2 = fr.a₂ := by
  simp [sGen, Frame.gens11]

theorem sGen_three (fr : Frame G) : sGen fr 3 = fr.b₂ := by
  simp [sGen, Frame.gens11]

theorem sGen_four (fr : Frame G) : sGen fr 4 = fr.h₀ := by
  simp [sGen, Frame.gens11]

theorem sGen_five (fr : Frame G) : sGen fr 5 = fr.σ := by
  simp [sGen, Frame.gens11]

end CFSG.OddStandard.HigherRank.G2Three.Sec1Proof
