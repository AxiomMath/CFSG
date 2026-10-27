module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3M23Data
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinM2Abs

public section

namespace CFSG.QuasithinUnique.A5.Kc3M23
open CFSG.Blueprint CFSG.QuasithinUnique.Vol2Native.A312L.PermLat CFSG.QuasithinUnique.Unc25K1.Six CFSG.QuasithinUnique.Unc25G2.M2x CFSG.QuasithinUnique.A5.Kc3Cert CFSG.QuasithinUnique.A5.Kc3M23Data

@[expose] def m23gA : Equiv.Perm (Fin 23) :=
  List.formPerm [0, 1] * List.formPerm [2, 3] * List.formPerm [6, 7] * List.formPerm [8, 9] *
    List.formPerm [12, 13] * List.formPerm [14, 15] * List.formPerm [18, 19] *
    List.formPerm [20, 21]

@[expose] def m23gB : Equiv.Perm (Fin 23) :=
  List.formPerm [0, 15, 10, 2] * List.formPerm [1, 8, 20, 11] * List.formPerm [3, 4, 7, 22] *
    List.formPerm [5, 21, 13, 17] * List.formPerm [12, 19] * List.formPerm [14, 16]

theorem m23_eq : NativeSporadic.M23 = Subgroup.closure {m23gA, m23gB} := rfl

@[expose] def m23a : ↥NativeSporadic.M23 :=
  ⟨m23gA, by rw [m23_eq]; exact Subgroup.subset_closure (Set.mem_insert _ _)⟩

@[expose] def m23b : ↥NativeSporadic.M23 :=
  ⟨m23gB, by rw [m23_eq]; exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

@[expose] def enc : ↥NativeSporadic.M23 → RN 23 := fun x => RN.enc (x : Equiv.Perm (Fin 23))

@[expose] def gR : List (RN 23) := [m23a, m23b, m23a⁻¹, m23b⁻¹].map enc

end CFSG.QuasithinUnique.A5.Kc3M23
