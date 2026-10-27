module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTL2Res
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTFinDefs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.ABGLocalTools

structure Inputs55B : Prop where
  sp4 : CellV FSp4
  l4 : CellV FL4
  u4 : CellV FU4
  a7 : ∀ (Y : Type) [Group Y], Nonempty (Y ≃* alternatingGroup (Fin 7)) → FinCellA Y
  alt : ∀ (n : ℕ), 8 ≤ n → n ≤ 11 → ∀ (Y : Type) [Group Y],
    Nonempty (Y ≃* alternatingGroup (Fin n)) → FinCellB Y
  m12 : ∀ (Y : Type) [Group Y], NativeSporadic.IsSporadic Y .M12 → FinCellB Y
  m22 : ∀ (Y : Type) [Group Y], NativeSporadic.IsSporadic Y .M22 → FinCellB Y
  m23 : ∀ (Y : Type) [Group Y], NativeSporadic.IsSporadic Y .M23 → FinCellB Y
  j2 : ∀ (Y : Type) [Group Y], NativeSporadic.IsSporadic Y .J2 → FinCellB Y
  j3 : ∀ (Y : Type) [Group Y], NativeSporadic.IsSporadic Y .J3 → FinCellB Y
  l216 : ∀ (Y : Type) [Group Y], LieModel Y .PSL 2 2 4 → FinCellB Y
  l34 : ∀ (Y : Type) [Group Y], LieModel Y .PSL 3 2 2 → FinCellB Y
  u34 : ∀ (Y : Type) [Group Y], LieModel Y .PSU 3 2 2 → FinCellB Y
  res : ResB

theorem fl2Res_of_resB (h : ResB) : FL2Res :=
  fun G _ _ z k S T Tstar p H P g X Y hc t q I Q₁ hd J hB _ hI =>
    h G z k S T Tstar p H P g X Y hc t q I Q₁ hd J hB hI

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
