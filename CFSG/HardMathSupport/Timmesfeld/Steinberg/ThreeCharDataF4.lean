module

public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeChar
public meta import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeChar
public meta import CFSG.Blueprint.ChevalleyRootsInputs
public meta import CFSG.Blueprint.Chevalley

public section

namespace CFSG.HardMathSupport.Timmesfeld.Steinberg

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley KTree

set_option maxRecDepth 100000

@[expose] def f4ThreeReps : List (List ℕ) :=
  [[0, 0, 0, 0], [1, 0, 0, 0], [0, 1, 0, 0], [1, 0, 1, 0]]

@[expose] def f4ThreeOrbit : List ℕ :=
  [0, 1, 231006005901009, 2, 48314385, 9, 1116738, 25667333989001, 5368265, 740782250, 3, 154,
   1124462971, 48297617, 11, 89, 18, 434678553, 740893562, 1114874, 13882275, 2851925998777, 596473,
   124082, 91, 124940331, 5366401, 7379, 1547579, 66249, 9147402, 13762, 171955, 35208962945, 7361,
   1530, 19043, 1016314, 9145538, 235, 12546, 9145474, 19107, 1016378, 112906, 10120166739,
   434678569, 99, 817, 170, 3912106993, 82309138, 27, 1394, 91081500659, 3912107145, 899, 7377,
   1546, 35208962961, 9145458, 251, 12562, 819, 13882259, 596265, 82321506, 123874, 1542475,
   316880666529, 66273, 13786, 2115, 112922, 82309274, 2123, 112930, 1016162, 171387, 9146834,
   1016170]

@[expose] def f4ThreeStab0 : StabCert3 where
  vec := [0, 0, 0, 0]
  simple := [0, 1, 2, 3]
  keys :=
    [50462976]

@[expose] def f4ThreeStab1 : StabCert3 where
  vec := [1, 0, 0, 0]
  simple := [1, 2, 3]
  keys :=
    [33756458, 33756462, 34668573, 34668590, 50462976, 50463018, 50464004, 50464046, 50855948,
     50855982, 134417702, 134417710, 134874402, 134874414, 168296468, 168296494, 268633894,
     268633898, 269091106, 269091114, 285345052, 285345070, 402784540, 402784554]

@[expose] def f4ThreeStab2 : StabCert3 where
  vec := [0, 1, 0, 0]
  simple := [0, 2, 3, 39]
  keys :=
    [33756967, 34674454, 35134735, 35924495, 50462976, 50857477, 51383297, 52963841, 134420259,
     134879006, 135799311, 136259087, 168300045, 168825863, 170142215, 268639523, 269098270,
     269558294, 270083606, 285347349, 286268423, 287254023, 402789397, 403184653, 404301325,
     420486145, 421011969, 520625157, 521216517, 604115968, 604642560, 671292672]

@[expose] def f4ThreeStab3 : StabCert3 where
  vec := [1, 0, 1, 0]
  simple := [1, 3, 13]
  keys :=
    [34668573, 34803456, 34805252, 35720981, 35979303, 35984917, 50462976, 50464004, 50855948,
     52101411, 52428839, 52430115, 135991045, 136384269, 168296468, 168363776, 168365316, 169936670,
     170197031, 170200350, 286394117, 287377174, 420610317, 421200150]

@[expose] def f4ThreeCheck (_ : Unit := ()) : Bool :=
  orbitCheck3 .F4 f4ThreeReps f4ThreeOrbit &&
    [f4ThreeStab0, f4ThreeStab1, f4ThreeStab2, f4ThreeStab3].all fun S =>
      S.check f4Certificate && decide ((S.passing f4Certificate).length ≤ 1)

end CFSG.HardMathSupport.Timmesfeld.Steinberg
