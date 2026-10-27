module

public import Certificates.Data.CFSGNative.Chevalley.C2E6CertLie
public import Certificates.Certificate17105

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven

open CFSG.Monster.Existence.StdOdd CFSG.Monster.Existence.StdOdd.Cert CFSG.Monster.Existence.StdOdd.CertNative CFSG.LieType.Chevalley.C2E6Std.MatrixModel

section Rgrp

theorem exists_card_inf_centralizer_rep7B :
    ∃ z ∈ Subgroup.centralizer ({rep7B} : Set Rgrp),
      Nat.card ↥(Subgroup.centralizer ({rep7B} : Set Rgrp) ⊓
        Subgroup.centralizer ({z} : Set Rgrp)) = 49 :=
  Certificates.certificate17105

end Rgrp

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven
