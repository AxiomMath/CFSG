module

public import CFSG.Blueprint.ChevalleyRootsInputs

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley

@[expose] def e7RootsP1_certVecs : List (Fin Tag.E7.rank → ℤ) :=
  (List.range e7Certificate.roots.length).map e7Certificate.root

theorem e7RootsP1_check : e7Certificate.check = true := by decide +kernel

theorem e7RootsP1_isRoot_iff (v : Fin Tag.E7.rank → ℤ) :
    IsRoot Tag.E7 v ↔ v ∈ e7RootsP1_certVecs := by
  rw [RootCertificate.isRoot_iff e7RootsP1_check]
  simp [e7RootsP1_certVecs, List.mem_map, List.mem_range]

end CFSG.StandardType

end
