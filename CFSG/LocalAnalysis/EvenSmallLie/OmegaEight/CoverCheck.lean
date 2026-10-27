module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.CoverData
public import CFSG.Certificates.CosetTableCompactColumns
public meta import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.CoverData
public meta import CFSG.Certificates.CosetTableCompactColumns
public import Certificates.Certificate3006
public meta import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.CosetTableShort
public meta import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.GroupTheory.LocalCores.Fitting
public meta import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public meta import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public meta import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public meta import CFSG.Sporadic.SmallOddCore.CheckSpec

public section

namespace CFSG.EvenSmallLie.OmegaEight.Cover

open CFSG.LieType.Multipliers CFSG.CosetTable

theorem gen_check :
    ((List.finRange 8).all fun j => (List.finRange 360).all fun x =>
    (genArrs[(j : ℕ)]!)[(x : ℕ)]! == ((cycPerm 360 (genCycles j) x : Fin 360) : ℕ)) = true :=
  Certificates.certificate3006.1

theorem model_check :
    ((rels.all fun r => decide (word r = 1)) &&
      ((List.finRange 4).all fun i => decide (word (commWords (pairs i)) = gens i)) &&
      ((List.finRange 8).all fun j => decide (word (genWords j) = cycPerm 360 (genCycles j))) &&
      decide (word uWord * word uWord = 1) &&
      decide (word tuWord = rhoT * word uWord * rhoT⁻¹)) = true :=
  Certificates.certificate3006.2.1

theorem pres_check :
    (genSub {r | r ∈ rels.map FreeGroup.mk} (subsetOf 4 [0, 1, 2])).FiniteIndex ∧
      (genSub {r | r ∈ rels.map FreeGroup.mk} (subsetOf 4 [0, 1, 2])).index ≤ 120 :=
  Certificates.certificate3006.2.2.1

theorem cover_check :
    (genSub {r | r ∈ coverWs.map FreeGroup.mk} (subsetOf 4 [0, 1, 2])).FiniteIndex ∧
      (genSub {r | r ∈ coverWs.map FreeGroup.mk} (subsetOf 4 [0, 1, 2])).index ≤ 240 :=
  Certificates.certificate3006.2.2.2.1

theorem rho_check :
    ((coverWs.all fun r => decide (rhoWord r = 1)) &&
      decide (rhoWord uWord * rhoWord uWord = 1) &&
      !decide (rhoWord tuWord * rhoWord tuWord = 1)) = true :=
  Certificates.certificate3006.2.2.2.2

end CFSG.EvenSmallLie.OmegaEight.Cover
