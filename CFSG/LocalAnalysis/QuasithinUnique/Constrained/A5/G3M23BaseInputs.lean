module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermEnc

public section

namespace CFSG.QuasithinUnique.A5.G3.M23
open Equiv CFSG.QuasithinUnique.Vol2Native.A312L.PermLat

@[expose] def natA : Perm (Fin 23) :=
  List.formPerm [0, 1] * List.formPerm [2, 3] * List.formPerm [6, 7] * List.formPerm [8, 9] *
    List.formPerm [12, 13] * List.formPerm [14, 15] * List.formPerm [18, 19] * List.formPerm [20, 21]

@[expose] def natB : Perm (Fin 23) :=
  List.formPerm [0, 15, 10, 2] * List.formPerm [1, 8, 20, 11] * List.formPerm [3, 4, 7, 22] *
    List.formPerm [5, 21, 13, 17] * List.formPerm [12, 19] * List.formPerm [14, 16]

@[expose] def natGens : List (Perm (Fin 23)) := [natA, natB]

@[expose] def tGens : List (Perm (Fin 23)) :=
  [permOf 23 [[1,3],[4,10],[5,14],[8,9],[11,15],[12,22],[13,17],[19,20]], permOf 23 [[1,4],[2,16],[5,18],[6,12],[7,14],[8,9],[13,15],[21,22]], permOf 23 [[1,17],[2,16],[3,13],[4,11],[7,18],[10,15],[12,22],[19,20]], permOf 23 [[1,8,11,12],[2,10,6,4],[3,22,15,9],[5,14],[13,16,17,21],[19,20]]]

@[expose] def mGens1 : List (Perm (Fin 23)) :=
  [permOf 23 [[1,12,21,5,17],[2,14,7,4,15],[3,9,16,11,6],[10,20,18,13,19]], permOf 23 [[1,15,22,11],[2,8,13,3],[5,10,7,21],[9,19,12,18],[14,16],[17,20]]]

@[expose] def mGens2 : List (Perm (Fin 23)) :=
  [permOf 23 [[1,5],[3,11],[4,7],[9,16],[12,21],[13,18],[14,15],[19,20]], permOf 23 [[0,8,15,22,2,6,9,10,18,5,13,4,7,21],[1,17,11,12,16,14,3],[19,20]]]

end CFSG.QuasithinUnique.A5.G3.M23
