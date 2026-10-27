module

public import CFSG.CharacterTheory.Semidihedral.Presentation

public section

namespace CFSG.Semidihedral

open CFSG.Open

@[expose] def z (n : ℕ) : SemidihedralGroup n := r n ^ half n

@[expose] def rotationSubgroup (n : ℕ) : Subgroup (SemidihedralGroup n) :=
  Subgroup.zpowers (r n)

@[expose] def dihedralSubgroup (n : ℕ) : Subgroup (SemidihedralGroup n) :=
  Subgroup.closure {r n ^ 2, s n}

@[expose] def quaternionSubgroup (n : ℕ) : Subgroup (SemidihedralGroup n) :=
  Subgroup.closure {r n ^ 2, r n * s n}

end CFSG.Semidihedral
