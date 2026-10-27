module

public import CFSG.Sporadic.Schreier.Co3SecondCheck
public import CFSG.GH74.M12.HypCore
public meta import CFSG.Sporadic.Schreier.Co3SecondCheck
public meta import CFSG.GH74.M12.HypCore
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.FendelDataInputs
public import Certificates.Certificate3097

public section

namespace CFSG.EvenSmallLie.SympSix

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier.Co3
  CFSG.Sporadic.Schreier.Co3.Native CFSG.GH74.M12.Hyp

theorem fendelWit_check :
    ∀ x : Fin 128 × Fin 4 × Fin 2, fendelWitOK x.1 x.2.1 x.2.2 = true :=
  Certificates.certificate3097.1

theorem fendel_check_Tsizes :
    (co3TLevels[0]!).pts.size = 128 ∧ (co3TLevels[1]!).pts.size = 4 ∧
    (co3TLevels[2]!).pts.size = 2 :=
  Certificates.certificate3097.2.1

theorem fendel_check_elts :
    ∀ x ∈ fendelMElts, isInvA 276 x (invCand 276 x) = true ∧
    siftA 276 co3MLevels co3MBaseArr 0 x = true :=
  Certificates.certificate3097.2.2.1

theorem fendel_check_a :
    eqA 276 (compA 276 fendelAArr fendelAArr) (idA 276) = true ∧
    eqA 276 fendelAArr (idA 276) = false ∧ eqA 276 co3TtArr co3ZArr = false :=
  Certificates.certificate3097.2.2.2.1

theorem fendel_check_c :
    eqA 276 (compA 276 fendelCArr co3TtArr) (compA 276 (compA 276 co3ZArr co3TtArr) fendelCArr)
      = true :=
  Certificates.certificate3097.2.2.2.2.1

theorem fendel_check_k : commutesA 276 fendelKArr co3TtArr = true ∧
    eqA 276 (compA 276 fendelKArr fendelKArr) co3ZArr = true :=
  Certificates.certificate3097.2.2.2.2.2.1

theorem fendel_check_w : fendelKTbl co3ZArr = JT :=
  Certificates.certificate3097.2.2.2.2.2.2.1

theorem fendel_check_y : commutesA 276 fendelYArr co3TtArr = true ∧
    eqA 276 (compA 276 fendelYHArr fendelYArr) (compA 276 fendelAArr fendelYHArr) = true ∧
    fendelKTbl fendelYArr ∈ QT ∧ fendelKTbl fendelYArr ≠ JT :=
  Certificates.certificate3097.2.2.2.2.2.2.2.1

theorem fendel_check_y' : commutesA 276 fendelY'Arr co3TtArr = true ∧
    eqA 276 (compA 276 fendelY'HArr fendelY'Arr) (compA 276 fendelAArr fendelY'HArr) = true ∧
    eqA 276 (compA 276 fendelY'ZHArr (compA 276 co3ZArr fendelY'Arr))
      (compA 276 fendelAArr fendelY'ZHArr) = true :=
  Certificates.certificate3097.2.2.2.2.2.2.2.2.1

theorem fendel_check_g :
    ∀ i < 4, commutesA 276 (fendelGArr i) co3TtArr = true ∧
    eqA 276 (compA 276 (fendelGHArr i) (fendelGArr i)) (compA 276 fendelAArr (fendelGHArr i))
      = true :=
  Certificates.certificate3097.2.2.2.2.2.2.2.2.2.1

theorem fendel_check_words :
    fendelGWords.map fendelGWordTbl = gensT ∧
    ∀ u ∈ fendelGWords, ∀ i ∈ u, 1 ≤ i ∧ i ≤ 4 :=
  Certificates.certificate3097.2.2.2.2.2.2.2.2.2.2.1

theorem fendel_check_comm :
    commutesA 276 fendelK2Arr co3TtArr = true ∧
    eqA 276 (compA 276 (compA 276 (compA 276 (fendelGArr 0) fendelK2Arr)
      (invCand 276 (fendelGArr 0))) (invCand 276 fendelK2Arr)) co3ZArr = true :=
  Certificates.certificate3097.2.2.2.2.2.2.2.2.2.2.2.1

theorem fendel_bfS_center :
    ∀ t ∈ BT, (∀ u ∈ BT, tmul t u = tmul u t) → t = tid ∨ t = JT :=
  Certificates.certificate3097.2.2.2.2.2.2.2.2.2.2.2.2

end CFSG.EvenSmallLie.SympSix
