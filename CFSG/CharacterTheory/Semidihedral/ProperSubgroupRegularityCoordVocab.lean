module

public import Certificates.Certificate8048

public section

namespace CFSG.Semidihedral.ProperSubgroupRegularity

open CFSG.Sporadic.Mathieu CFSG.Blueprint

theorem m11_centralizer_coordinates_commute :
    ∀ x, m11CentralizerCoordinates x * m11a = m11a * m11CentralizerCoordinates x :=
  Certificates.certificate8048

@[expose] def m11CentralizerCoordinate
    (x : (Fin 8 × Fin 2) × Fin 3) : Subgroup.centralizer ({m11a} : Set NativeSporadic.M11) :=
  ⟨m11CentralizerCoordinates x,
    Subgroup.mem_centralizer_singleton_iff.mpr (m11_centralizer_coordinates_commute x)⟩

@[expose] def m11LocalThreeC : Subgroup.centralizer ({m11a} : Set NativeSporadic.M11) :=
  m11CentralizerCoordinate ((0, 0), 1)

@[expose] def m11ReflectionC : Subgroup.centralizer ({m11a} : Set NativeSporadic.M11) :=
  m11CentralizerCoordinate ((0, 1), 0)

end CFSG.Semidihedral.ProperSubgroupRegularity
