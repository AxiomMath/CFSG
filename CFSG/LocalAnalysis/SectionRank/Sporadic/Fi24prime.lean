module

public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import Certificates.Data.CFSGNative.SectionRank.Fi24prime
public meta import Certificates.Data.CFSGNative.SectionRank.Fi24prime
import all CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate8016
public import CFSG.Open.Defs

public section

namespace CFSG.SectionRank

open CFSG.Open CFSG.SectionRank.Native

theorem fi24prime_check : (ops3 781).check fi24primeData = true :=
  Certificates.certificate8016

theorem Fi24prime_elementary_three_rank_four :
    ∃ E : Subgroup CFSG.Blueprint.NativeSporadic.Fi24prime,
      IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 :=
  (spec3 781).exists_of_check fi24primeData fi24prime_check

end CFSG.SectionRank
