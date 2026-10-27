module

public import CFSG.Certificates.CosetTablePresented
public import CFSG.LieType.Multipliers.CoverWords
public import CFSG.Sporadic.Schreier.TitsArrays
public import CFSG.Sporadic.Schreier.TitsBasic
public import CFSG.LieType.Multipliers.TitsCheckInputs
public import Certificates.Certificate10009
public meta import CFSG.Certificates.CosetTablePresented
public meta import CFSG.LieType.Multipliers.CoverWords
public meta import CFSG.Sporadic.Schreier.TitsData
public meta import CFSG.Sporadic.Schreier.TitsArrays
public meta import CFSG.Sporadic.Schreier.TitsBasic
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.CosetTableShort
public meta import CFSG.Certificates.NativeSchreierCard
public import CFSG.Certificates.NativeSchreierCard
public meta import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.GroupTheory.LocalCores.Fitting
public meta import CFSG.Open.Defs
public import CFSG.Open.Defs

public section

namespace CFSG.LieType.Multipliers.Tits

open CFSG.CosetTable CFSG.Sporadic.Schreier.Tits CFSG.Certificates.Native CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native

theorem tits_check_rels :
    Finite (PG 3 titsRels) ∧ Nat.card (PG 3 titsRels) ≤ 17971200 :=
  Certificates.certificate10009.1

theorem tits_check_cover :
    Finite (PG 3 titsCoverWords) ∧ Nat.card (PG 3 titsCoverWords) ≤ 17971200 :=
  Certificates.certificate10009.2.1

theorem tits_check_perms :
    (∀ w ∈ titsOneWords, FreeGroup.lift (fun i : Fin 3 => wordIn 2
      (fun j => permOfArr 1755 titsDerivedArrs[j]!) (abcWords.getD i.val [])) (FreeGroup.mk w) = 1)
    ∧ ∀ j < 2, permOfArr 1755 titsDerivedArrs[j]! = wordIn 3
      (fun i => wordIn 2 (fun j => permOfArr 1755 titsDerivedArrs[j]!) (abcWords.getD i []))
      (titsDWords.getD j []) :=
  Certificates.certificate10009.2.2

end CFSG.LieType.Multipliers.Tits
