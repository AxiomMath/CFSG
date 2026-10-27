module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.FusD2PermSound
public import Certificates.Certificate9582

public section

namespace CFSG.AGLEmbedding

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four Certificates.FusD2Perm
  CFSG.Blueprint CFSG.RankThree.PartOne.CTP.Fus

abbrev m23FusA : Equiv.Perm (Fin 23) :=
  List.formPerm [0, 1] * List.formPerm [2, 3] * List.formPerm [6, 7] * List.formPerm [8, 9] *
    List.formPerm [12, 13] * List.formPerm [14, 15] * List.formPerm [18, 19] *
    List.formPerm [20, 21]

abbrev m23FusB : Equiv.Perm (Fin 23) :=
  List.formPerm [0, 15, 10, 2] * List.formPerm [1, 8, 20, 11] * List.formPerm [3, 4, 7, 22] *
    List.formPerm [5, 21, 13, 17] * List.formPerm [12, 19] * List.formPerm [14, 16]

theorem m23_fus_tab_a : TabRep m23Data.aT m23FusA := ⟨rfl, by decide⟩

theorem m23_fus_tab_b : TabRep m23Data.bT m23FusB := ⟨rfl, by decide⟩

theorem m23_fus3_check : check m23Data = true :=
  Certificates.certificate9582

theorem fusionGenerationOf_M23_three :
    FusionGenerationOf (NativeSporadic.Carrier .M23) 3 :=
  FusD2.fusionGenerationOf_of_check (G := NativeSporadic.M23) (a := m23FusA) (b := m23FusB)
    rfl (D := m23Data) rfl Nat.prime_three m23_fus_tab_a m23_fus_tab_b m23_fus3_check

end CFSG.AGLEmbedding
