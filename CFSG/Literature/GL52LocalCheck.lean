module

public import CFSG.Literature.GL52Isos
public import CFSG.Literature.GL52Pass
public meta import CFSG.Literature.GL52Isos
public meta import CFSG.Literature.GL52Pass
public import CFSG.Literature.GL52LocalCheckInputs
public import Certificates.Certificate2002

public section

namespace CFSG.Literature.GL52

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native

attribute [local instance high] fastGL3

theorem orders_check :
    ordTest 31 2 (tbl glT0) = true ∧ ordTest 31 2 (tbl glU0) = true ∧
    ordTest 31 3 (tbl glTau1) = true ∧ ordTest 31 3 (tbl glTau2) = true ∧
    ordTest 31 3 (tbl glTauB) = true ∧ ordTest 31 5 (tbl glF5) = true ∧
    ordTest 31 15 (tbl glC15) = true ∧ ordTest 31 7 (tbl glS7) = true ∧
    ordTest 31 3 (tbl glFr) = true ∧ ordTest 31 31 (tbl glA) = true ∧
    ordTest 31 5 (tbl glH5) = true :=
  Certificates.certificate2002.1

theorem fix_check :
    fpT (tbl glT0) = 15 ∧ fpT (tbl glU0) = 7 ∧ fpT (tbl glTau1) = 1 ∧ fpT (tbl glTau2) = 7 :=
  Certificates.certificate2002.2.1

theorem comm_check :
    (gensE ++ gensT1 ++ gensT2).all (fun g => cmtT (tbl g) (tbl glT0)) = true ∧
    gensK1.all (fun g => cmtT (tbl g) (tbl glTau1)) = true ∧
    gensK2.all (fun g => cmtT (tbl g) (tbl glTau2)) = true ∧
    gensX.all (fun g => gensY.all fun h => cmtT (tbl g) (tbl h)) = true ∧
    cmtT (tbl glC15) (tbl glF5) = true ∧ cmtT (tbl glTau2) (tbl glTauB) = true :=
  Certificates.certificate2002.2.2.1

theorem notMem_check :
    (∀ σ : alternatingGroup (Fin 5),
      tblEq 31 (lkTableT tbK1 tbiK1 keyA5 tblA5 σ) (tbl glTau1) = false) ∧
    (∀ M : GL (Fin 3) (ZMod 2),
      tblEq 31 (lkTableT tbK2 tbiK2 keyGL3 tblGL3 M) (tbl glTau2) = false) :=
  Certificates.certificate2002.2.2.2.2.1

end CFSG.Literature.GL52
