module

public import CFSG.LieType.Multipliers.L34Data
public import CFSG.Certificates.CosetTableOrders
public import Certificates.Certificate10005
public meta import CFSG.LieType.Multipliers.L34Data
public meta import CFSG.Certificates.CosetTableOrders
public meta import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.CosetTableShort
public import CFSG.GroupTheory.LocalCores.Fitting
public meta import CFSG.GroupTheory.LocalCores.Fitting
public meta import CFSG.Open.Defs
public import CFSG.Open.Defs

public section

namespace CFSG.LieType.Multipliers.L34

open CFSG.Fischer CFSG.CosetTable

theorem det_gens :
    aMat.det = 1 ∧ aInvMat.det = 1 ∧ bMat.det = 1 ∧ bInvMat.det = 1 :=
  Certificates.certificate10005.1

theorem trans_entry : ∀ i j k l : Fin 3, ∀ c : F4, i ≠ j →
    (if k = l then 1 else if k = i ∧ l = j then c else 0) =
      (if k = l then (1 : F4) else 0) + (if i = k ∧ j = l then c else 0) :=
  Certificates.certificate10005.2.1

theorem rels_isScalar :
    rels.all (fun r => (wordMat r).isScalar) = true :=
  Certificates.certificate10005.2.2.1

theorem coverWs_eq_one :
    coverWs.all (fun r => decide (wordMat r = Mat3.one)) = true :=
  Certificates.certificate10005.2.2.2.1

theorem zOne_eq_one : wordMat zOne = Mat3.one :=
  Certificates.certificate10005.2.2.2.2.1

theorem zTwo_eq_one : wordMat zTwo = Mat3.one :=
  Certificates.certificate10005.2.2.2.2.2.1

theorem zThree_isScalar : (wordMat zThree).isScalar = true :=
  Certificates.certificate10005.2.2.2.2.2.2.1

theorem transCheck :
    ∀ i j : Fin 3, ∀ c : F4, i ≠ j → wordMat (transWord i j c) = transMat i j c :=
  Certificates.certificate10005.2.2.2.2.2.2.2.1

theorem diagCheck : ∀ d₀ d₁ d₂ : F4, d₀ * d₁ * d₂ = 1 →
    wordMat (diagWord d₀ d₁) = diagMat d₀ d₁ d₂ :=
  Certificates.certificate10005.2.2.2.2.2.2.2.2.1

theorem cyclic_card_le :
    Finite (PG 2 rels) ∧ Nat.card (PG 2 rels) ≤ 20160 :=
  Certificates.certificate10005.2.2.2.2.2.2.2.2.2.1

theorem restrict_card_le :
    Finite (PG (subsetOf 2 [1]).length (restrictWords (subsetOf 2 [1]) coverWs)) ∧
      Nat.card (PG (subsetOf 2 [1]).length (restrictWords (subsetOf 2 [1]) coverWs)) ≤ 5 :=
  Certificates.certificate10005.2.2.2.2.2.2.2.2.2.2.1

theorem cover_index_walks :
    (genSub {r : FreeGroup (Fin 2) | r ∈ coverWs.map FreeGroup.mk} (subsetOf 2 [1])).FiniteIndex ∧
      (genSub {r : FreeGroup (Fin 2) | r ∈ coverWs.map FreeGroup.mk}
        (subsetOf 2 [1])).index ≤ 193536 ∧
      ∀ p ∈ walkWords, p.2 ∣ orderOf (PresentedGroup.mk
        {r : FreeGroup (Fin 2) | r ∈ coverWs.map FreeGroup.mk} (FreeGroup.mk p.1)) :=
  Certificates.certificate10005.2.2.2.2.2.2.2.2.2.2.2

end CFSG.LieType.Multipliers.L34
