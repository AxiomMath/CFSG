module

public import CFSG.GH74.GLS.LU.Local.FiveDef
public import CFSG.GH74.GLS.Stage2.Final.ModelOneClass

public section

namespace CFSG.GH74.GLS.LU.Local

open CFSG.Blueprint CFSG.GH74.GLS

theorem fiveModelFusion
    : FiveModelFusion := by
  intro Gs _ hL x y hx hy
  haveI : Finite Gs := (CFSG.LieType.Catalog.lieModel_finite_simple Gs _ 4 5 1 hL).1
  exact CFSG.GH74.GLS.Stage2.Final.modelOneClass Gs 5 1 Nat.prime_five (by norm_num)
    (Or.inl ⟨by norm_num, hL⟩) x y hx hy

end CFSG.GH74.GLS.LU.Local
