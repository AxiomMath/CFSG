module

public import CFSG.LieType.HighestRoot.CentSymp
public import CFSG.LieType.HighestRoot.CentUnitaryModel

public section

namespace CFSG.LieType.HighestRoot

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.ClassicalInvolution.ModelFacts

variable {n p e : ℕ}

theorem highestRootCZ_modelUniv_PSL
    [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .PSL n p e) :
    HighestRootCZ (modelUniv .PSL n p e hp.out).D (GaloisField p e) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hadm.2.2.1; omega⟩
  exact highestRootCZ_specialLinear (two_ne_zero_galoisField e hp2)
    (by have := hadm.2.2.1; omega)

theorem highestRootCZ_modelUniv_PSp
    [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .PSp n p e) :
    HighestRootCZ (modelUniv .PSp n p e hp.out).D (GaloisField p e) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hadm.2.2.1; omega⟩
  exact highestRootCZ_symplectic (two_ne_zero_galoisField e hp2) m

theorem highestRootCZ_modelUniv_PSU
    [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .PSU n p e) :
    HighestRootCZ (modelUniv .PSU n p e hp.out).D (GaloisField p e) := by
  have he : 1 ≤ e := hadm.2.1
  rw [modelUniv_PSU he]
  exact highestRootCZ_unitary (card_galoisField_two_mul p e he) hp2 (by have := hadm.2.2.1; omega)
    (GaloisField.card p e (by omega))

theorem highestRootCZ_genericModelUniv_PSL
    [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .PSL n p e) :
    HighestRootCZ (CFSG.ClassicalInvolution.Generic.modelUniv .PSL n p e hp.out).D
      (GaloisField p e) :=
  highestRootCZ_modelUniv_PSL hp2 hadm

theorem highestRootCZ_genericModelUniv_PSp
    [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .PSp n p e) :
    HighestRootCZ (CFSG.ClassicalInvolution.Generic.modelUniv .PSp n p e hp.out).D
      (GaloisField p e) :=
  highestRootCZ_modelUniv_PSp hp2 hadm

theorem highestRootCZ_genericModelUniv_PSU
    [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .PSU n p e) :
    HighestRootCZ (CFSG.ClassicalInvolution.Generic.modelUniv .PSU n p e hp.out).D
      (GaloisField p e) :=
  highestRootCZ_modelUniv_PSU hp2 hadm

end CFSG.LieType.HighestRoot
