module

public import CFSG.LargeExtraspecial.S14SMKTransCode
public import CFSG.Fischer.Polar.Lines
public import CFSG.Sporadic.Th.Max3.Data
public import CFSG.LargeExtraspecial.S10FourG
public import CFSG.LargeExtraspecial.S14C12Lit
public import CFSG.LargeExtraspecial.S14SMHDefs
public import CFSG.LargeExtraspecial.S14SMIDefs
public import CFSG.LargeExtraspecial.S14SMKDivMain
public import CFSG.LargeExtraspecial.S14SMKTransBase
public import CFSG.LargeExtraspecial.S14SMKTransOuter
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.Sporadic.Th.KernelOrder
public import CFSG.Sporadic.Th.KernelOrderBase
public import CFSG.Sporadic.ThSchreier.LocalData
public import CFSG.Sporadic.ThSchreier.Max3Aut
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14.SMK

open Subgroup Module QuadraticMap CFSG.Open CFSG.Fischer CFSG.SmithE
  CFSG.LargeExtraspecial.SMod20 CFSG.RankThree.OrthogonalInvolutions CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Fischer.Native

@[expose] def IsTab (ct : Array ℕ) (π : Equiv.Perm (Fin 693)) : Prop :=
  ∀ x : Fin 693, ct[x.val]! = (π x).val

theorem sub_eq_add_V (x y : SMod20.V) : x - y = x + y := by
  funext m
  simp only [Pi.sub_apply, Pi.add_apply]
  generalize x m = a
  generalize y m = b
  revert a b
  decide

end CFSG.LargeExtraspecial.S14.SMK
