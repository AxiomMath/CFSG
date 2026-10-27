module

public import CFSG.LocalAnalysis.GLTheoremA.S8.YS06Cat10
public import CFSG.LocalAnalysis.GLTheoremA.CatA.BMKChainYS06
public import CFSG.LocalAnalysis.GLTheoremA.CatA.BMKNineK

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Dickson.BMRows (I1416QSporSK i1416At_of_sporK)

section Ys06Cat11


structure YS06SporTables2NoNine : Prop where
  base : YS06SporTablesNoNine
  cfgI : CfgIRes

theorem ys06_of_cat11_inputs
    (hS : YS06SporTables2NoNine) (hI : Timm.UnitaryPoint.UnitaryPointIdentification)
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → ∀ p ∈ Mu G m, S8Cat10Inputs G p) : YS06 :=
  ys06_of_cat9K i1415NineSporSK_holds hS.base hI fun G _ _ m hctx p hp =>
    (hin G m hctx p hp).toS8Cat8Inputs hS.cfgI

end Ys06Cat11

end CFSG.LocalAnalysis.GLTheoremA
