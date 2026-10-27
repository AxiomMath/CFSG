module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizerData
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section
namespace CFSG.ComponentClassification.M12Cover

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native

open CFSG.ComponentClassification.OuterAutomorphisms

section General

variable {G H : Type*} [Group G] [Group H]

end General

section Chain

variable {n : ℕ}

end Chain

@[expose] def permG0 : Equiv.Perm (Fin 12) := evalCodes [m12gA, m12gB] g0Word

@[expose] def permG1 : Equiv.Perm (Fin 12) := evalCodes [m12gA, m12gB] g1Word

end CFSG.ComponentClassification.M12Cover
