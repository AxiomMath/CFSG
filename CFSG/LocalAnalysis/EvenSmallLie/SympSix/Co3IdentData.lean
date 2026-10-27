module

public import CFSG.Sporadic.Schreier.Co3First
public meta import CFSG.Sporadic.Schreier.Co3CentralizerCheck
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentDataInputs
public import Certificates.Certificate3089

public section

namespace CFSG.EvenSmallLie.SympSix.Co3Ident

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Co3

theorem gen_check :
    (∀ i < 7, isInvA 276 (genArr i) (invCand 276 (genArr i)) = true) ∧
    (∀ i ∈ mLetters, siftA 276 co3MLevels co3MBaseArr 0 (genArr i) = true) ∧
    siftA 276 co3ChainLevels co3ChainBaseArr 0 (genArr 3) = true ∧
    eqA 276 (compA 276 (genArr 3) (genArr 3)) (idA 276) = true ∧
    eqA 276 (compA 276 (genArr 3) (compA 276 (genArr 4) (genArr 3))) (genArr 0) = true ∧
    eqA 276 (compA 276 (genArr 3) (compA 276 (genArr 0) (genArr 3))) (genArr 4) = true ∧
    eqA 276 (compA 276 (genArr 0) (genArr 2)) (compA 276 (genArr 2) (genArr 0)) = true :=
  Certificates.certificate3089

end CFSG.EvenSmallLie.SympSix.Co3Ident
