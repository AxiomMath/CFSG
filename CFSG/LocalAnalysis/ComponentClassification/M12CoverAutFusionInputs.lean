module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAut

public section
namespace CFSG.ComponentClassification.M12Cover

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier

open CFSG.ComponentClassification.OuterAutomorphisms

section General

variable {G : Type*} [Group G]

end General

@[expose] def permH : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 3, 5, 7, 4] * List.formPerm [1, 6, 11, 9, 10]

end CFSG.ComponentClassification.M12Cover
