module

public import CFSG.ClassicalInvolution.Q3.Q3T6OpenCore
public import CFSG.ClassicalInvolution.Q3.Q3T6OpenMuSym
public import CFSG.ClassicalInvolution.Q3.Q3T6FusL3Main
public import CFSG.ClassicalInvolution.Q3.Q3T6OpenEEtaY

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.Open (classicalInvolutionOddCore fusionStronglyClosed)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

section L3


variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}
  {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

namespace Sec19DataT3

variable (hd : Sec19DataT3 K z S W L t V)
include hd

theorem fl3Facts : FL3Facts hd where
  UKW := hd.toSec19Data3.inf_mem_USet
  invol_eq_or := fun {_} {_} hη hinv hWη {_} hA {_} hJ hAJ {_} hu =>
    hd.invol_eq_or hη hinv hWη hA hJ hAJ hu
  invol_mem_W := fun h e2 e1 => hd.invol_mem_W h e2 e1
  exists_mul := hd.exists_conj_eq_mul
  SW := hd.le_normalizer_W
  CK := fun hxS hxR => hd.mem_centralizerModOdd_K hxS hxR
  starSymm := fun hK hJ h => Mu.omegaStarNbr_symm hd.tight.hypGen hK hJ h
  Bconj := fun hx hdz hdS => hd.conj_mem_sec19BPrime hx hdz hdS

end Sec19DataT3

theorem residualL3Stmt : ResidualL3Stmt := by
  intro G _ _ _ K z S W L t V hd x hx _
  exact residual_of_FL3 hd (fun _ hd' => hd'.fl3Facts) hx

end L3

end CFSG.ClassicalInvolution.Q3.Q3T6
