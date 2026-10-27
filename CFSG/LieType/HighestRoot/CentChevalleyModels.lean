module

public import CFSG.LieType.HighestRoot.CentG2Main
public import CFSG.LieType.HighestRoot.CentChevalleyMain
public import CFSG.LieType.HighestRoot.CentIsogenyE6E7

public section

namespace CFSG.LieType.HighestRoot

open CFSG.ClassicalInvolution.Generic

theorem ringChar_galoisField_ne_two {p : ℕ} [Fact p.Prime] (e : ℕ) (hp : p ≠ 2) :
    ringChar (GaloisField p e) ≠ 2 := by
  rw [ringChar.eq (GaloisField p e) p]
  exact hp

theorem g2InvolutionData_modelUniv
    (p e : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    G2InvolutionData (modelUniv .G2 0 p e Fact.out).D (GaloisField p e) :=
  g2InvolutionData (ringChar_galoisField_ne_two e hp)

theorem highestRootCZ_modelUniv_F4
    (n p e : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    HighestRootCZ (modelUniv .F4 n p e Fact.out).D (GaloisField p e) :=
  highestRootCZ_F4 (ringChar_galoisField_ne_two e hp)

theorem highestRootCZ_modelUniv_E8
    (n p e : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    HighestRootCZ (modelUniv .E8 n p e Fact.out).D (GaloisField p e) :=
  highestRootCZ_E8 (ringChar_galoisField_ne_two e hp)

theorem highestRootCZ_modelUniv_E6
    (n p e : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    HighestRootCZ (modelUniv .E6 n p e Fact.out).D (GaloisField p e) :=
  highestRootCZ_E6 p e hp

theorem highestRootCZ_modelUniv_E7
    (n p e : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    HighestRootCZ (modelUniv .E7 n p e Fact.out).D (GaloisField p e) :=
  highestRootCZ_E7 p e hp

end CFSG.LieType.HighestRoot
