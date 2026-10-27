module

public import Certificates.Data.Schreier

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3.SporGen.ThreeHeis.Mathieu

open CFSG.M23

@[expose] def m24A : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 3] * List.formPerm [1, 6] * List.formPerm [2, 16] * List.formPerm [4, 12] *
    List.formPerm [5, 8] * List.formPerm [7, 14] * List.formPerm [9, 18] * List.formPerm [10, 17] *
    List.formPerm [11, 20] * List.formPerm [13, 15] * List.formPerm [19, 23] *
    List.formPerm [21, 22]

@[expose] def m24B : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 3, 5] * List.formPerm [1, 20, 13] * List.formPerm [2, 8, 14] *
    List.formPerm [4, 17, 9] * List.formPerm [12, 16, 15] * List.formPerm [18, 23, 22]

@[expose] def m24S : Fin 2 → Equiv.Perm (Fin 24) := ![m24A, m24B]

@[expose] def m24X : Equiv.Perm (Fin 24) :=
  List.formPerm [1, 21, 2] * List.formPerm [4, 8, 23] * List.formPerm [5, 12, 10] *
    List.formPerm [7, 17, 22] * List.formPerm [9, 13, 14] * List.formPerm [11, 16, 15]

@[expose] def m24XWord : List (Fin 2 × Bool) :=
  [(0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true),
   (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true),
   (0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true),
   (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false),
   (0, true), (1, true), (0, true), (1, false), (0, false), (1, false), (0, false), (1, false),
   (0, false), (1, false), (0, false), (1, false), (0, false), (1, true), (0, false), (1, true),
   (0, false), (1, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true),
   (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true),
   (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (1, true),
   (0, false), (1, true), (0, false), (1, true), (0, false), (1, false), (0, false), (1, false),
   (0, false), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false),
   (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true),
   (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true),
   (0, false), (1, true), (0, false), (1, true), (0, false), (1, true), (0, false), (1, true),
   (0, false), (1, true), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false),
   (0, false), (1, true), (0, false), (1, false), (0, false), (1, true), (0, false), (1, false),
   (0, false), (1, false), (0, false), (1, false), (0, false)]

@[expose] def m24Y : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 1, 8] * List.formPerm [2, 23, 18] * List.formPerm [3, 21, 4] *
    List.formPerm [6, 19, 20] * List.formPerm [9, 10, 16] * List.formPerm [11, 12, 14]

@[expose] def m24YWord : List (Fin 2 × Bool) :=
  [(1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true),
   (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true),
   (1, false), (0, true), (1, false), (0, true), (0, true), (1, true), (0, true), (1, false),
   (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true),
   (1, true), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false),
   (1, false), (0, false), (1, true), (0, false), (1, true), (0, false), (1, false), (0, false),
   (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1, true), (0, false),
   (1, true), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false),
   (1, false), (0, false), (1, false), (0, false), (0, false), (1, false), (0, false), (1, true),
   (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1, true),
   (0, false), (1, true), (0, false), (1, false), (0, false), (1, true), (0, false), (1, false),
   (0, false), (1, true), (0, true), (1, true), (1, true), (0, false), (1, false), (0, false),
   (1, false), (0, false), (1, true), (0, false), (1, true), (0, false), (1, true), (0, false),
   (1, true), (0, false), (1, false), (0, false), (1, false), (0, false), (1, true), (1, true),
   (0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false),
   (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true),
   (0, true), (1, true), (0, false), (1, false), (0, false), (1, true), (0, false), (1, true),
   (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1, true),
   (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true),
   (0, true), (1, false), (0, true), (1, true), (0, true), (1, true)]

@[expose] def m24Z : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 3, 18] * List.formPerm [1, 21, 2] * List.formPerm [4, 23, 8] *
    List.formPerm [5, 15, 13] * List.formPerm [9, 10, 16] * List.formPerm [11, 14, 12]

@[expose] def m24ZWord : List (Fin 2 × Bool) :=
  [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false),
   (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true),
   (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true),
   (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false),
   (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true),
   (0, true), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1, true),
   (0, false), (1, true), (0, false), (1, false), (0, false), (1, false), (0, false), (1, true),
   (0, false), (1, false), (0, false), (1, true), (0, false), (1, true), (0, true), (1, false),
   (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true),
   (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true),
   (0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false),
   (0, true), (1, true), (0, true), (1, true), (0, true), (0, true), (1, true), (0, true),
   (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true),
   (1, false), (0, true), (1, false), (1, false), (0, false), (1, true), (0, false), (1, true),
   (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false),
   (0, false), (1, true), (0, false), (1, false), (0, false), (1, false), (0, false), (1, true),
   (0, false), (1, true), (0, false), (1, false), (0, false), (1, false), (0, false), (1, true),
   (0, false), (1, true), (0, false), (1, true), (0, false), (1, true), (0, false), (1, false),
   (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false),
   (0, false), (1, true)]

@[expose] def m24G11 : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 21, 18, 2, 3, 1] * List.formPerm [5, 12, 9, 13, 11, 16] *
    List.formPerm [7, 17, 22] * List.formPerm [8, 23] * List.formPerm [10, 15, 14] *
    List.formPerm [19, 20]

@[expose] def m24G11Word : List (Fin 2 × Bool) :=
  [(1, false), (0, false), (1, true), (0, false), (1, true), (0, false), (1, true), (0, false),
   (1, true), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false),
   (1, false), (0, false), (1, false), (0, false), (1, true), (1, true), (0, false), (1, false),
   (0, false), (1, true), (0, false), (1, true), (0, false), (1, true), (0, false), (1, true),
   (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1, true),
   (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false),
   (0, false), (1, true), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false),
   (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1, true),
   (0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true),
   (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (0, true),
   (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true),
   (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true),
   (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true),
   (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true),
   (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true),
   (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true),
   (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true),
   (1, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1, true)]

@[expose] def m24G12 : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 8, 17] * List.formPerm [3, 23, 7] * List.formPerm [4, 22, 18] *
    List.formPerm [6, 19, 20] * List.formPerm [9, 15, 12] * List.formPerm [10, 11, 13]

@[expose] def m24G12Word : List (Fin 2 × Bool) :=
  [(1, false), (0, true), (1, true), (0, true), (1, true), (1, true), (0, false), (1, false),
   (0, false), (1, false), (0, false), (1, true), (0, false), (1, false), (0, false), (1, true),
   (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true),
   (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true),
   (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true),
   (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true),
   (1, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, false), (1, true),
   (0, false), (1, false), (0, false), (1, true), (0, false), (1, true), (0, false), (1, false),
   (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false),
   (0, false), (1, false), (0, false), (1, true), (0, false), (1, false), (0, false), (1, false),
   (0, false), (1, false), (0, false), (1, true), (0, false), (1, false), (0, false), (1, false),
   (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false),
   (0, true), (1, true), (0, true), (1, false), (1, false), (0, false), (1, false), (0, false),
   (1, true), (0, false), (1, false), (0, false), (1, true), (0, false), (1, false), (0, false),
   (1, false), (0, false), (1, false), (0, false), (1, true), (0, false), (1, true), (0, false),
   (1, true), (0, false), (1, true), (0, false), (1, true), (0, false), (1, false), (0, false),
   (1, true), (0, false), (1, true), (0, false), (1, false)]

@[expose] def m24G13 : Equiv.Perm (Fin 24) :=
  List.formPerm [4, 22, 14] * List.formPerm [5, 12, 10] * List.formPerm [7, 9, 8] *
    List.formPerm [11, 15, 16] * List.formPerm [13, 23, 17] * List.formPerm [18, 20, 19]

@[expose] def m24G13Word : List (Fin 2 × Bool) :=
  [(0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false),
   (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false),
   (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true),
   (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true),
   (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true),
   (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true),
   (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true),
   (1, false), (0, true), (1, false), (0, false), (1, false), (1, false), (0, true), (1, true),
   (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false),
   (0, true), (1, false), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false),
   (0, true), (1, false), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true),
   (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true),
   (1, true), (0, false), (1, true), (0, false), (1, false), (0, false), (1, true), (0, false),
   (1, false), (0, false), (1, true), (0, false), (1, false), (0, true), (1, false), (0, true),
   (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true),
   (1, false), (1, false), (0, false), (1, false), (0, false), (1, true), (0, false), (1, false),
   (0, false), (1, true), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false),
   (0, false), (1, true), (0, false), (1, true), (0, false), (1, true), (0, false), (1, true),
   (0, false), (1, true), (0, false), (1, false), (0, false), (1, true), (0, false), (1, true),
   (0, false), (1, false)]

@[expose] def m24G21 : Equiv.Perm (Fin 24) :=
  List.formPerm [1, 8] * List.formPerm [2, 23] * List.formPerm [4, 21] * List.formPerm [6, 20] *
    List.formPerm [7, 22] * List.formPerm [9, 14] * List.formPerm [10, 12] * List.formPerm [11, 16]

@[expose] def m24G21Word : List (Fin 2 × Bool) :=
  [(1, false), (0, false), (1, true), (0, false), (1, true), (0, false), (1, true), (0, false),
   (1, true), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false),
   (1, false), (0, false), (1, false), (0, false), (1, true), (1, true), (0, true), (1, false),
   (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true),
   (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true),
   (0, true), (1, false), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true),
   (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false),
   (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false),
   (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true),
   (0, true), (1, false), (1, false), (0, false), (1, true), (0, false), (1, true), (0, false),
   (1, false), (0, false), (1, true), (0, false), (1, true), (0, false), (1, true), (0, false),
   (1, true), (0, false), (1, true), (0, false), (1, false), (0, false), (1, false), (0, false),
   (1, true), (0, true), (1, true), (1, true), (0, false), (1, false), (0, false), (1, false),
   (0, false), (1, false), (0, false), (1, true), (1, true), (0, true), (1, true), (0, true),
   (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true),
   (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, false),
   (1, false), (0, false), (1, true), (0, false), (1, false), (0, false), (1, false), (0, false),
   (1, false), (0, false), (1, false), (0, false), (1, true), (0, false), (1, true), (0, false),
   (1, true), (0, false), (1, false), (0, false), (1, true), (1, true), (0, false), (1, false),
   (0, false), (1, false), (0, false), (1, true), (0, false), (1, false), (0, false), (1, true),
   (0, false), (1, false), (0, true), (1, true), (0, true), (1, true)]

@[expose] def m24G22 : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 5, 8, 11, 2, 10] * List.formPerm [1, 9, 3, 13, 4, 12] *
    List.formPerm [6, 22, 20, 7, 19, 17] * List.formPerm [14, 21, 16, 18, 15, 23]

@[expose] def m24G22Word : List (Fin 2 × Bool) :=
  [(1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true),
   (1, false), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false), (0, true),
   (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true),
   (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true),
   (1, true), (1, true), (0, false), (1, false), (0, false), (1, true), (0, false), (1, true),
   (0, false), (1, false), (0, false), (1, true), (0, false), (1, true), (0, true), (1, false),
   (0, true), (1, false), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false),
   (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false),
   (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true),
   (1, true), (0, false), (1, true), (0, false), (1, false), (1, false), (0, true), (1, false),
   (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true),
   (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, false), (1, true),
   (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true),
   (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true),
   (0, false), (1, false), (0, false), (1, true), (0, false), (1, true), (0, false), (1, true),
   (0, false), (1, true), (0, false), (1, false), (0, false), (0, false)]

@[expose] def m24G23 : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 1, 4, 10, 17, 6, 9, 21, 23, 3, 15, 22, 19, 5, 8, 18, 2, 11, 7, 20, 12] *
    List.formPerm [13, 14, 16]

@[expose] def m24G23Word : List (Fin 2 × Bool) :=
  [(1, true), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false),
   (1, false), (0, false), (1, true), (0, false), (1, true), (0, false), (1, false), (0, false),
   (1, true), (0, false), (1, true), (0, false), (1, true), (0, false), (1, false), (0, false),
   (1, false), (0, false), (1, false), (0, false), (1, true), (0, false), (1, true), (0, false),
   (1, true), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false),
   (1, true), (0, false), (1, false), (0, false), (1, false), (0, false), (1, true), (0, false),
   (1, false), (0, false), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true),
   (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false),
   (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true),
   (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true),
   (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true),
   (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true),
   (0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true),
   (0, true), (1, true), (0, true), (1, true), (0, false), (1, false), (0, true), (1, false),
   (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true),
   (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true),
   (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false),
   (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, false)]

@[expose] def m24W2 : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 5] * List.formPerm [1, 10, 8, 12] * List.formPerm [2, 9, 23, 14] *
    List.formPerm [3, 15] * List.formPerm [4, 11, 21, 16] * List.formPerm [6, 22, 20, 7] *
    List.formPerm [13, 18] * List.formPerm [17, 19]

@[expose] def m24W2Word : List (Fin 2 × Bool) :=
  [(1, false), (0, false), (1, true), (0, false), (1, true), (0, false), (1, true), (0, false),
   (1, true), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false),
   (1, false), (0, false), (1, false), (0, false), (1, true), (0, true), (1, true), (0, true),
   (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true),
   (1, false), (0, true), (1, false), (1, false), (0, false), (1, true), (0, false), (1, true),
   (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false),
   (0, false), (1, true), (0, false), (1, false), (0, false), (1, false), (0, false), (1, true),
   (0, false), (1, true), (0, false), (1, false), (1, false), (0, true), (1, false), (0, true),
   (1, false), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false), (0, true),
   (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true),
   (1, false), (0, true), (1, true), (0, true), (1, true), (1, true), (0, false), (1, true),
   (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (0, false),
   (1, false), (0, false), (1, false), (0, false), (1, true), (0, false), (1, false), (0, false),
   (1, false), (0, false), (1, true), (0, false), (1, true), (0, false), (1, false), (0, false),
   (1, true), (0, false), (1, false), (0, false), (1, true), (0, false), (1, false), (0, false),
   (1, false), (0, false), (1, true), (0, false), (1, false), (0, false), (1, true), (0, false),
   (1, false), (0, false), (1, true), (1, true), (0, false), (1, false), (0, false), (1, false),
   (0, false), (1, true), (0, false), (1, false), (0, false), (1, true), (0, false), (1, false),
   (0, false), (1, false), (0, false), (1, true), (0, false)]

@[expose] def m24W4 : Equiv.Perm (Fin 24) :=
  List.formPerm [1, 21] * List.formPerm [3, 18] * List.formPerm [5, 12] * List.formPerm [8, 23] *
    List.formPerm [9, 16] * List.formPerm [11, 13] * List.formPerm [14, 15] * List.formPerm [17, 22]

@[expose] def m24W4Word : List (Fin 2 × Bool) :=
  [(1, false), (0, false), (1, true), (0, false), (1, false), (0, false), (1, true), (0, false),
   (1, true), (0, false), (1, true), (0, false), (1, false), (0, false), (1, false), (0, false),
   (1, true), (0, false), (1, true), (0, false), (1, true), (0, false), (1, true), (0, true),
   (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false),
   (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (1, false), (0, true),
   (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true),
   (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true),
   (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true),
   (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true),
   (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false), (1, false),
   (0, false), (1, false), (0, false), (1, true), (0, false), (1, false), (0, false), (1, false),
   (0, false), (1, true), (0, false), (1, false), (0, false), (1, true), (0, false), (1, true),
   (0, false), (1, false), (0, false), (1, false), (0, false), (1, true), (0, true), (1, true),
   (0, true), (1, true), (0, true), (1, true), (0, false), (1, false), (0, false), (1, true),
   (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false),
   (0, false), (1, true), (0, false), (1, true), (0, false), (1, true), (0, false), (1, true),
   (0, false), (1, true), (0, false), (1, true), (0, false), (1, false), (0, true), (1, false),
   (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true),
   (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true),
   (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false),
   (0, false), (1, false), (0, false), (1, false), (0, false), (1, true)]

@[expose] def m24GS1 : Fin 3 → Equiv.Perm (Fin 24) :=
  ![m24G11, m24G12, m24G13]

@[expose] def m24SeedA1 : List (Fin 3 × Bool) :=
  [(2, true), (0, false), (1, true), (2, false), (0, false), (0, false), (1, true), (2, false),
   (0, false), (0, false), (0, false), (2, false), (0, false), (2, false), (0, false), (1, true),
   (0, true), (0, true), (1, true), (2, true), (1, false), (0, false), (2, false), (0, false),
   (1, false), (2, true), (0, false), (2, true), (1, false), (0, true), (2, false), (0, true),
   (2, false), (0, true), (0, true), (2, false), (1, false), (2, true), (0, false), (1, true),
   (0, false), (1, true), (2, true), (0, true), (0, true), (0, true)]

@[expose] def m24SeedB1 : List (Fin 3 × Bool) :=
  [(0, false), (0, false), (0, false), (2, true), (0, false), (2, true), (0, true), (1, true),
   (2, false), (0, false), (2, false), (1, true), (0, false), (0, false), (1, false), (0, true),
   (1, true), (0, true), (1, false), (2, true), (1, false), (0, false), (1, true), (0, true),
   (1, false), (2, false), (0, true), (2, false)]

@[expose] def m24GS2 : Fin 3 → Equiv.Perm (Fin 24) :=
  ![m24G21, m24G22, m24G23]

@[expose] def m24SeedA2 : List (Fin 3 × Bool) :=
  [(0, false), (1, false), (0, false), (2, false), (1, false), (2, false), (0, true), (1, true),
   (0, true), (1, true), (0, false), (1, false), (2, false), (0, false), (1, true), (1, true),
   (0, true), (2, true), (1, true), (2, true), (0, true), (2, false), (1, false), (2, true),
   (1, true), (0, false), (2, false), (0, false), (1, false), (2, true), (0, true), (1, false),
   (2, true), (1, false), (0, false), (1, false), (2, true), (2, true), (1, true), (1, true),
   (2, true), (1, false), (2, true)]

@[expose] def m24SeedB2 : List (Fin 3 × Bool) :=
  [(2, true), (1, false), (1, false), (2, true), (2, true), (1, false), (1, false), (0, true),
   (2, true), (1, false), (2, false), (1, false), (0, false), (1, true), (2, true), (1, false),
   (2, false), (0, false), (1, false), (2, true), (1, true), (0, true), (1, false), (1, false),
   (2, true), (0, true), (2, false), (0, true), (1, false), (0, true), (2, false), (0, false),
   (1, false), (0, false), (1, true)]

abbrev M24Facts : Prop :=
  (evalGroupWord m24S m24XWord = m24X) ∧
  (evalGroupWord m24S m24YWord = m24Y) ∧
  (evalGroupWord m24S m24ZWord = m24Z) ∧
  (evalGroupWord m24S m24G11Word = m24G11) ∧
  (evalGroupWord m24S m24G12Word = m24G12) ∧
  (evalGroupWord m24S m24G13Word = m24G13) ∧
  (evalGroupWord m24S m24G21Word = m24G21) ∧
  (evalGroupWord m24S m24G22Word = m24G22) ∧
  (evalGroupWord m24S m24G23Word = m24G23) ∧
  (evalGroupWord m24S m24W2Word = m24W2) ∧
  (evalGroupWord m24S m24W4Word = m24W4) ∧
  (m24X ^ 3 = 1) ∧
  (m24Y ^ 3 = 1) ∧
  (m24Z ^ 3 = 1) ∧
  (m24Z ≠ 1) ∧
  (m24X * m24Y = m24Y * m24Z * m24X) ∧
  (m24Z * m24X = m24X * m24Z) ∧
  (m24Z * m24Y = m24Y * m24Z) ∧
  (m24G11 * m24Z = m24Z ^ 2 * m24X ^ 0 * m24G11) ∧
  (m24G11 * m24X = m24Z ^ 2 * m24X ^ 1 * m24G11) ∧
  (m24G12 * m24Z = m24Z ^ 0 * m24X ^ 1 * m24G12) ∧
  (m24G12 * m24X = m24Z ^ 2 * m24X ^ 2 * m24G12) ∧
  (m24G13 * m24X = m24X * m24G13) ∧
  (m24G21 * m24Z = m24Z ^ 1 * (m24X * m24Y ^ 1) ^ 0 * m24G21) ∧
  (m24G21 * (m24X * m24Y ^ 1) = m24Z ^ 1 * (m24X * m24Y ^ 1) ^ 2 * m24G21) ∧
  (m24G22 * m24Z = m24Z ^ 2 * (m24X * m24Y ^ 1) ^ 0 * m24G22) ∧
  (m24G22 * (m24X * m24Y ^ 1) = m24Z ^ 2 * (m24X * m24Y ^ 1) ^ 2 * m24G22) ∧
  (m24G23 * (m24X * m24Y ^ 1) = (m24X * m24Y ^ 1) * m24G23) ∧
  (m24W2 * m24X = m24X ^ 0 * m24Y ^ 1 * m24Z ^ 0 * m24W2) ∧
  (m24W2 * m24Z = m24Z ^ 1 * m24W2) ∧
  (m24W4 * (m24X * m24Y ^ 1) = m24X ^ 2 * m24Y ^ 1 * m24Z ^ 1 * m24W4) ∧
  (m24W4 * m24Z = m24Z ^ 2 * m24W4) ∧
  (evalGroupWord m24GS1 m24SeedA1 = m24A⁻¹) ∧
  (evalGroupWord m24GS1 m24SeedB1 = m24B⁻¹) ∧
  (evalGroupWord m24GS2 m24SeedA2 = m24A⁻¹) ∧
  (evalGroupWord m24GS2 m24SeedB2 = m24B⁻¹)

@[expose] def m22A : Equiv.Perm (Fin 22) :=
  List.formPerm [0, 12] * List.formPerm [1, 7] * List.formPerm [2, 15] * List.formPerm [3, 11] *
    List.formPerm [5, 21] * List.formPerm [6, 16] * List.formPerm [8, 9] * List.formPerm [10, 13]

@[expose] def m22B : Equiv.Perm (Fin 22) :=
  List.formPerm [0, 21, 2, 20] * List.formPerm [1, 17, 3, 12] * List.formPerm [4, 11] *
    List.formPerm [5, 10, 6, 14] * List.formPerm [7, 13, 19, 9] * List.formPerm [16, 18]

@[expose] def m22S : Fin 2 → Equiv.Perm (Fin 22) := ![m22A, m22B]

@[expose] def m22U : Equiv.Perm (Fin 22) :=
  List.formPerm [1, 3, 6] * List.formPerm [2, 12, 19] * List.formPerm [4, 9, 7] *
    List.formPerm [5, 11, 18] * List.formPerm [8, 10, 21] * List.formPerm [13, 16, 17]

@[expose] def m22UWord : List (Fin 2 × Bool) :=
  [(0, true), (1, false), (0, true), (1, false), (1, false), (0, false), (1, true), (0, false),
   (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1, true), (0, false),
   (1, false), (0, false), (1, true), (0, false), (1, false), (1, false), (0, false), (1, false),
   (0, false), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true),
   (0, true), (1, true), (1, true), (0, true), (1, false), (0, false), (1, false), (1, false),
   (0, false)]

@[expose] def m22V : Equiv.Perm (Fin 22) :=
  List.formPerm [1, 16, 7] * List.formPerm [2, 19, 12] * List.formPerm [3, 17, 4] *
    List.formPerm [5, 11, 18] * List.formPerm [6, 13, 9] * List.formPerm [14, 20, 15]

@[expose] def m22VWord : List (Fin 2 × Bool) :=
  [(0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false),
   (0, false), (1, false), (0, false), (1, false), (1, false), (0, false), (1, true), (0, false),
   (1, false), (0, false), (1, false), (0, false), (1, false), (1, false), (0, true), (1, true),
   (0, true), (1, false), (1, false), (1, false), (0, false), (1, true), (0, false), (1, true),
   (0, false), (1, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false),
   (1, false), (1, false), (1, false), (0, false), (1, false), (1, false), (0, false), (1, true),
   (0, false), (1, true), (0, false), (1, true), (0, false)]

@[expose] def m22C1 : Equiv.Perm (Fin 22) :=
  List.formPerm [0, 20] * List.formPerm [1, 16] * List.formPerm [3, 17] * List.formPerm [4, 21] *
    List.formPerm [6, 13] * List.formPerm [7, 10] * List.formPerm [8, 9] * List.formPerm [14, 15]

@[expose] def m22C1Word : List (Fin 2 × Bool) :=
  [(1, true), (0, true), (1, false), (0, true), (1, true), (1, true), (0, true), (1, true),
   (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true),
   (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true),
   (0, true), (1, false), (0, true), (1, true), (1, true), (0, true), (1, false), (0, true),
   (1, true), (0, true), (1, true), (1, true), (0, false), (1, false), (1, false), (0, false),
   (1, false), (0, true), (1, false)]

@[expose] def m22C2 : Equiv.Perm (Fin 22) :=
  List.formPerm [0, 10] * List.formPerm [1, 15] * List.formPerm [3, 6] * List.formPerm [4, 9] *
    List.formPerm [7, 20] * List.formPerm [8, 21] * List.formPerm [13, 17] * List.formPerm [14, 16]

@[expose] def m22C2Word : List (Fin 2 × Bool) :=
  [(1, false), (0, false), (1, false), (0, false), (1, true), (0, false), (1, true), (0, false),
   (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1, true), (0, false),
   (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1, true), (1, true),
   (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false),
   (0, true), (1, true), (0, false), (1, false), (1, false), (0, false), (1, false), (0, false),
   (1, false), (1, false), (0, false), (1, false), (0, false), (1, false), (1, false), (0, false),
   (1, false), (0, false), (1, false)]

@[expose] def m22C3 : Equiv.Perm (Fin 22) :=
  List.formPerm [0, 19] * List.formPerm [1, 4] * List.formPerm [2, 12] * List.formPerm [3, 18] *
    List.formPerm [5, 7] * List.formPerm [6, 17] * List.formPerm [9, 16] * List.formPerm [11, 13]

@[expose] def m22C3Word : List (Fin 2 × Bool) :=
  [(0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false),
   (0, false), (1, false), (0, false), (1, true), (0, true), (1, false), (0, true), (1, true),
   (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true),
   (0, true)]

@[expose] def m22GS : Fin 5 → Equiv.Perm (Fin 22) :=
  ![m22U, m22V, m22C1, m22C2, m22C3]

@[expose] def m22SeedA : List (Fin 5 × Bool) :=
  [(0, false), (1, false), (4, true), (2, true), (4, true), (2, true), (0, true), (4, false),
   (2, false), (0, false), (4, false), (2, false), (1, true)]

@[expose] def m22SeedB : List (Fin 5 × Bool) :=
  [(0, false), (1, false), (3, true), (4, true), (2, true), (4, true), (0, true), (4, false),
   (2, false), (3, false), (0, false), (4, false), (2, false)]

abbrev M22Facts : Prop :=
  (evalGroupWord m22S m22UWord = m22U) ∧
  (evalGroupWord m22S m22VWord = m22V) ∧
  (evalGroupWord m22S m22C1Word = m22C1) ∧
  (evalGroupWord m22S m22C2Word = m22C2) ∧
  (evalGroupWord m22S m22C3Word = m22C3) ∧
  (m22U ≠ 1) ∧
  (m22U ^ 3 = 1) ∧
  (m22V ^ 3 = 1) ∧
  (m22U * m22V = m22V * m22U) ∧
  (m22V ≠ 1) ∧
  (m22V ≠ m22U) ∧
  (m22V ≠ m22U ^ 2) ∧
  (m22C1 * m22U = m22U * m22C1) ∧
  (m22C1 ^ 2 = 1) ∧
  (m22C2 * m22V = m22V * m22C2) ∧
  (m22C2 ^ 2 = 1) ∧
  (m22C3 * (m22U * m22V) = (m22U * m22V) * m22C3) ∧
  (m22C3 ^ 2 = 1) ∧
  (evalGroupWord m22GS m22SeedA = m22A⁻¹) ∧
  (evalGroupWord m22GS m22SeedB = m22B⁻¹)

end CFSG.LocalAnalysis.AGL81I.Section3.SporGen.ThreeHeis.Mathieu
