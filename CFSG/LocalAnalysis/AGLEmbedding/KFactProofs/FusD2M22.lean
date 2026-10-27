module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.FusD2PermSound
public import Certificates.Certificate9581

public section

namespace CFSG.AGLEmbedding

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four Certificates.FusD2Perm
  CFSG.Blueprint CFSG.RankThree.PartOne.CTP.Fus

abbrev m22FusA : Equiv.Perm (Fin 22) :=
  List.formPerm [0, 12] * List.formPerm [1, 7] * List.formPerm [2, 15] * List.formPerm [3, 11] *
    List.formPerm [5, 21] * List.formPerm [6, 16] * List.formPerm [8, 9] * List.formPerm [10, 13]

abbrev m22FusB : Equiv.Perm (Fin 22) :=
  List.formPerm [0, 21, 2, 20] * List.formPerm [1, 17, 3, 12] * List.formPerm [4, 11] *
    List.formPerm [5, 10, 6, 14] * List.formPerm [7, 13, 19, 9] * List.formPerm [16, 18]

theorem m22_fus_tab_a : TabRep m22Data.aT m22FusA := ⟨rfl, by decide⟩

theorem m22_fus_tab_b : TabRep m22Data.bT m22FusB := ⟨rfl, by decide⟩

theorem m22_fus3_check : check m22Data = true :=
  Certificates.certificate9581

theorem fusionGenerationOf_M22_three :
    FusionGenerationOf (NativeSporadic.Carrier .M22) 3 :=
  FusD2.fusionGenerationOf_of_check (G := NativeSporadic.M22) (a := m22FusA) (b := m22FusB)
    rfl (D := m22Data) rfl Nat.prime_three m22_fus_tab_a m22_fus_tab_b m22_fus3_check

end CFSG.AGLEmbedding
