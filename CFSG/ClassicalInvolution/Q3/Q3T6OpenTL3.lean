module

public import CFSG.ClassicalInvolution.Q3.Q3T6MainSylow
public import CFSG.ClassicalInvolution.Q3.TL3S8BData

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}

theorem TightStd3.toTL3 (ht : TightStd3 K z) : Q3.TightMemStd K z where
  isUniqueInvolution := ht.isUniqueInvolution
  le_centralizer := ht.le_centralizer
  hypGen := hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) ht.hyp
  normEq := ht.normEq
  edgeless := ht.edgeless
  natCard_rSet := fun hR => ht.natCard_rSet hR

theorem Sec19Data3.toTL3 {S : Sylow 2 G} {W : Subgroup G} (hd : Sec19Data3 K z S W) :
    Q3.TightSylowData K z S W where
  tight := hd.tight.toTL3
  mu := hd.mu
  sylow := hd.sylow
  hSz := hd.hSz
  hW := hd.hW
  hWS := hd.hWS

theorem Sec19DataT3.toTL3 {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}
    (hd : Sec19DataT3 K z S W L t V) : Q3.TightSylowDataT K z S W L t V where
  toTightSylowData := hd.toSec19Data3.toTL3
  memL := hd.memL
  invL := hd.invL
  ne := hd.ne
  memV := hd.memV
  leW := hd.leW
  memT := hd.memT

end CFSG.ClassicalInvolution.Q3.Q3T6
