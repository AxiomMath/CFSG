module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterD48Letters
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterD48SylowData

public section

namespace CFSG.AGLEmbedding.ChevOuterD48

@[expose] def sylowA : GL (Fin 8) GF512 := wordGL sylowWordA

@[expose] def sylowB : GL (Fin 8) GF512 := wordGL sylowWordT ^ 19

@[expose] def sylowGroup : Subgroup (GL (Fin 8) GF512) := Subgroup.closure {sylowA, sylowB}

theorem sylowWordA_lt : ∀ l ∈ sylowWordA, l < 24 := by decide +kernel

theorem sylowWordT_lt : ∀ l ∈ sylowWordT, l < 24 := by decide +kernel

end CFSG.AGLEmbedding.ChevOuterD48
