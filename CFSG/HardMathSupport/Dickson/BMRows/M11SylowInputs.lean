module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.AgreeTasks
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterElevenInputs

public section

namespace CFSG.HardMathSupport.Dickson.BMRows.M11

open CFSG.Monster.AxisCount CFSG.YGroups.Y443 CFSG.YGroups.Y443Native CFSG.AGLEmbedding.Norton
  CFSG.AGLEmbedding.Norton.MON5_7 CFSG.AGLEmbedding.Norton.Gen11
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterEleven

@[expose] def m11aW : List Native.Gen :=
  [.tau, .tau, .rho (false, 2590, 3624), .tau, .rho (true, 3931, 1956), .rho (false, 0, 3394),
    .rho (false, 0, 24),
    .perm #[11, 0, 9, 22, 18, 8, 14, 4, 17, 7, 15, 10, 5, 1, 6, 20, 12, 13, 21, 3, 16, 2, 23, 19],
    .xi, .xi, .rho (false, 0, 62),
    .perm #[0, 5, 8, 9, 1, 4, 12, 13, 2, 6, 19, 18, 7, 3, 23, 22, 20, 17, 14, 10, 21, 16, 11, 15],
    .xi, .xi, .rho (false, 0, 44),
    .perm #[10, 11, 12, 19, 13, 20, 21, 18, 1, 16, 2, 14, 8, 5, 22, 0, 3, 9, 7, 23, 17, 6, 15, 4],
    .xi, .xi, .rho (false, 0, 60),
    .perm #[1, 2, 3, 5, 0, 4, 7, 6, 8, 18, 13, 23, 21, 15, 16, 10, 12, 22, 9, 19, 17, 11, 20, 14]]

@[expose] def m11bW : List Native.Gen := e0W ++ m11aW ++ e0W

@[expose] def m11uW : List Native.Gen :=
  [.rho (false, 1557, 3617), .rho (false, 0, 3079)]

@[expose] def m11cW : List Native.Gen :=
  [.rho (true, 2030, 2897), .rho (false, 0, 1247)]

@[expose] def m11Pairs : List (List Native.Gen × List Native.Gen) :=
  [(m11aW ++ m11aW, wW),
    (m11aW ++ m11bW, m11cW),
    (m11bW ++ m11aW, m11cW),
    (m11aW ++ m11uW ++ m11aW, m11uW),
    (m11aW ++ gen11W0, gen11W0 ++ m11aW),
    (m11uW ++ gen11W0, gen11W0 ++ m11uW)]

@[expose] def m11Check (_ : Unit := ()) : Bool := agreeAll m11Pairs

theorem m11Check_eq_agreeTasks :
    m11Check () = agreeTasks (Native.mkCtx ()) (aV ()) (bV ()) (wV ()) m11Pairs := by
  rw [m11Check, agreeAll_eq_agreeTasks]

end CFSG.HardMathSupport.Dickson.BMRows.M11
