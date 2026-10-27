module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinM2Tab
public import CFSG.Sporadic.Mathieu.M23
public meta import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinM2Tab
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinM23Inputs
public import Certificates.Certificate4047
public import Certificates.Certificate13
public import Certificates.Certificate14
public import Certificates.Certificate15
public import Certificates.Certificate16
public import Certificates.Certificate17
public import Certificates.Certificate18
public import Certificates.Certificate19
public import Certificates.Certificate20
public import Certificates.Certificate21
public import Certificates.Certificate22
public import Certificates.Certificate23
public import Certificates.Certificate24
public import Certificates.Certificate25
public import Certificates.Certificate26
public import Certificates.Certificate27
public import Certificates.Certificate28
public import Certificates.Certificate29
public import Certificates.Certificate30
public import Certificates.Certificate31
public import Certificates.Certificate32
public import Certificates.Certificate33
public import Certificates.Certificate34
public import Certificates.Certificate35
public import Certificates.Certificate36
public import Certificates.Certificate37
public import Certificates.Certificate38
public import Certificates.Certificate39
public import Certificates.Certificate40
public import Certificates.Certificate41
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
public meta import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
public import CFSG.Sporadic.M23.M23Group
public meta import Certificates.Certificate113
public import Certificates.Certificate113

public section

namespace CFSG.QuasithinUnique.Unc25G2

namespace M2x

open CFSG.Sporadic.Mathieu CFSG.Blueprint

set_option synthInstance.maxSize 32768 in
set_option synthInstance.maxHeartbeats 400000 in
theorem check23 : Check 23 d23 :=
  Certificates.certificate4047

abbrev m23gA : Equiv.Perm (Fin 23) :=
  List.formPerm [0, 1] * List.formPerm [2, 3] * List.formPerm [6, 7] * List.formPerm [8, 9] *
    List.formPerm [12, 13] * List.formPerm [14, 15] * List.formPerm [18, 19] * List.formPerm [20, 21]

abbrev m23gB : Equiv.Perm (Fin 23) :=
  List.formPerm [0, 15, 10, 2] * List.formPerm [1, 8, 20, 11] * List.formPerm [3, 4, 7, 22] *
    List.formPerm [5, 21, 13, 17] * List.formPerm [12, 19] * List.formPerm [14, 16]

theorem m23_eq : NativeSporadic.M23 = Subgroup.closure {m23gA, m23gB} := rfl

theorem m23gA_mem : m23gA ∈ NativeSporadic.M23 := by
  rw [m23_eq]
  exact Subgroup.subset_closure (Set.mem_insert _ _)

theorem m23gB_mem : m23gB ∈ NativeSporadic.M23 := by
  rw [m23_eq]
  exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem card_native_M23 : Nat.card NativeSporadic.M23 = 10200960 := by
  rw [nativeM23_eq, Nat.card_eq_fintype_card]
  exact CFSG.M23.M23Group.card_M23

theorem twoE_M23 : TwoE NativeSporadic.M23 :=
  twoE_of_check NativeSporadic.M23 (a := m23gA) (b := m23gB) m23gA_mem m23gB_mem d23 (by decide)
    (by decide) card_native_M23 check23

end M2x

end CFSG.QuasithinUnique.Unc25G2
