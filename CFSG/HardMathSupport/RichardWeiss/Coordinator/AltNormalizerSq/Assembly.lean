module

public import CFSG.HardMathSupport.RichardWeiss.Coordinator.AltNormalizerSq.Final
public import CFSG.HardMathSupport.RichardWeiss.Coordinator.AltNormalizerSq.SmallDegreeFinal

public section

namespace CFSG.HardMathSupport.RichardWeiss.Coordinator

open CFSG.AGLEmbedding

theorem citedBlockAltNormalizerSq_of_eightTen
    (h810 : CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Asc81bEightTen) :
    CitedBlockAltNormalizerSq := by
  intro G _ _ M S L p hK hA hL hX1 _ h678 hp hp2 hJ U hUK hUL hUp
  rcases altNormalizerSq_small_or_degree hA hL h678 hp hp2 hJ hUK hUL hUp with
    h | ⟨m, hm, hdeg⟩
  · obtain ⟨U₁, U₂, a, b, c, d, f, g⟩ := sq_of_relIndex_le h
    exact ⟨U₁, U₂, a, b, c, d, f, fun y hy hyL hyU => g y hy.1 hyL hyU⟩
  · exact altNormalizerSq_of_eightTen_large h810 hK hA hL hX1 hp hp2 hJ hm hdeg hUK hUL hUp

end CFSG.HardMathSupport.RichardWeiss.Coordinator
