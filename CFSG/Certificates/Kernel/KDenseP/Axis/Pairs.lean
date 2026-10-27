module

public import CFSG.Monster.AxisCount.BabyIdent
public import CFSG.Monster.AxisCount.HSIdentBase
public import CFSG.Monster.AxisCount.HSIdentRec0Inputs
public import CFSG.Monster.AxisCount.HSIdentRec1Inputs
public import CFSG.Monster.AxisCount.HSIdentRec2Inputs
public import CFSG.Monster.AxisCount.HSIdentRec3Inputs
public import CFSG.Monster.AxisCount.HSIdentRec4Inputs
public import CFSG.Monster.AxisCount.HSIdentRec5Inputs
public import CFSG.Monster.AxisCount.HSIdentRec6Inputs
public import CFSG.Monster.AxisCount.HSIdentRec7Inputs

public section

namespace CFSG.KC.KDenseP.Axis

open CFSG.Monster.AxisCount

@[expose] noncomputable def babyPairs (j : Nat) : List (List Native.Gen × List Native.Gen) :=
  (Baby.bo j).U.map (fun w => (Baby.gW j ++ w, Baby.gW j)) ++
    (List.range (Baby.nrec j)).flatMap (fun r => [true, false].map fun ε =>
      (Baby.gW j ++ Baby.xW j r ε, Baby.gW (Baby.tgt j r ε))) ++
    (Baby.jWords j).map (fun w => (w, [])) ++
    (Baby.bo j).gamma.flatMap (fun sg => Baby.Seg.rec (motive := fun _ => List (List Native.Gen × List Native.Gen))
      (fun w => [(w, [])]) (fun _ => []) sg)

@[expose] noncomputable def p6002 : List (List Native.Gen × List Native.Gen) := babyPairs 4 ++ babyPairs 5
@[expose] noncomputable def p6003 : List (List Native.Gen × List Native.Gen) := babyPairs 3 ++ babyPairs 6 ++ babyPairs 8
@[expose] noncomputable def p6004 : List (List Native.Gen × List Native.Gen) :=
  babyPairs 0 ++ babyPairs 1 ++ babyPairs 2 ++ babyPairs 7 ++ babyPairs 9

@[expose] noncomputable def p6009 : List (List Native.Gen × List Native.Gen) :=
  (List.range 10).flatMap fun j => (HS.babyBlocks[j]!).map fun b => (b, [])

@[expose] noncomputable def recPairs (l : List (Fin 12 × Nat × Nat)) : List (List Native.Gen × List Native.Gen) :=
  l.flatMap fun s => (List.range' s.2.1 (s.2.2 - s.2.1)).flatMap fun r => [true, false].flatMap fun ε =>
    [(Cert.gammaW s.1 ++ HS.xW s.1 r ε, Cert.gammaW (Cert.tFin s.1 r ε)),
     (Cert.gammaW s.1 ++ HS.xW s.1 r ε,
       HS.babyW (HS.bbL s.1 r ε) ++ HS.hppL s.1 r ε ++ Cert.gammaW (Cert.tFin s.1 r ε)),
     (HS.hppL s.1 r ε, [])]

@[expose] noncomputable def p6010 : List (List Native.Gen × List Native.Gen) := recPairs HS.recShard_0
@[expose] noncomputable def p6011 : List (List Native.Gen × List Native.Gen) := recPairs HS.recShard_1
@[expose] noncomputable def p6012 : List (List Native.Gen × List Native.Gen) := recPairs HS.recShard_2
@[expose] noncomputable def p6013 : List (List Native.Gen × List Native.Gen) := recPairs HS.recShard_3
@[expose] noncomputable def p6014 : List (List Native.Gen × List Native.Gen) := recPairs HS.recShard_4
@[expose] noncomputable def p6015 : List (List Native.Gen × List Native.Gen) := recPairs HS.recShard_5
@[expose] noncomputable def p6016 : List (List Native.Gen × List Native.Gen) := recPairs HS.recShard_6
@[expose] noncomputable def p6017 : List (List Native.Gen × List Native.Gen) := recPairs HS.recShard_7

@[expose] noncomputable def p6018 : List (List Native.Gen × List Native.Gen) :=
  (List.finRange 12).flatMap fun i => (List.range 2).flatMap fun k =>
    [(Cert.gammaW i ++ HS.uW i k, Cert.gammaW i),
     (Cert.gammaW i ++ HS.uW i k, HS.babyW (HS.bbU i k) ++ HS.hppU i k ++ Cert.gammaW i),
     (HS.hppU i k, [])]

@[expose] noncomputable def p6005v : List (List Native.Gen × List Native.Gen) :=
  (List.range 10).map fun j => (Baby.gW j, Baby.gW j)

@[expose] noncomputable def p6018v : List (List Native.Gen × List Native.Gen) :=
  (List.finRange 12).map fun i => (Cert.gammaW i, Cert.gammaW i)

end CFSG.KC.KDenseP.Axis

end
