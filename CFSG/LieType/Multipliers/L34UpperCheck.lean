module

public import CFSG.LieType.Multipliers.L34UpperData
public import CFSG.LieType.Multipliers.ProductKernel
public meta import CFSG.LieType.Multipliers.L34UpperData
public meta import CFSG.LieType.Multipliers.ProductKernel
public meta import CFSG.Certificates.CosetTableOrders
public import Certificates.Certificate3007
public meta import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.CosetTableShort
public import CFSG.GroupTheory.LocalCores.Fitting
public meta import CFSG.GroupTheory.LocalCores.Fitting
public meta import CFSG.Open.Defs
public import CFSG.Open.Defs

public section

namespace CFSG.LieType.Multipliers.L34Upper

open CFSG.Fischer CFSG.CosetTable CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34

theorem relations_check :
    ∀ u ∈ extraWs,
      PresentedGroup.mk {r : FreeGroup (Fin 2) | r ∈ hopfWs.map FreeGroup.mk} (FreeGroup.mk u) = 1 :=
  Certificates.certificate3007.1

theorem dMat_mul : dMat.mul dInvMat = Mat3.one ∧ dInvMat.mul dMat = Mat3.one := ⟨rfl, rfl⟩

theorem words_check :
    wordMat uA = dMat.mul (aMat.mul dInvMat) ∧ wordMat uB = dMat.mul (bMat.mul dInvMat) ∧
      bFive = List.replicate 5 (1, true) :=
  Certificates.certificate3007.2.1

theorem bMat_ne_one : bMat ≠ Mat3.one := fun h =>
  absurd (congrArg (fun x : Mat3 => x.e01.code.val) h) (by decide)

theorem delta_check :
    ∀ p ∈ deltaWalks,
      PresentedGroup.mk {r : FreeGroup (Fin 2) | r ∈ coverWs.map FreeGroup.mk} (FreeGroup.mk p.1) ∈
        genSub {r : FreeGroup (Fin 2) | r ∈ coverWs.map FreeGroup.mk} (subsetOf 2 [1]) :=
  Certificates.certificate3007.2.2

end CFSG.LieType.Multipliers.L34Upper
