module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicRep
public meta import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBaseNative
public import CFSG.Sporadic.J2.Simple
public meta import Certificates.Data.CFSGNative.J2.Certificate
public import CFSG.Sporadic.Bridge.J2
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicJ2Inputs
public import Certificates.Certificate4142
public import Certificates.Certificate3139
public import CFSG.Foundations
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.QuasithinUnique.K1.Interface
public import CFSG.Sporadic.Th.F2Spec
public import Certificates.Certificate113

public section

namespace CFSG.QuasithinUnique.K1.SporadicPerm

open CFSG.Sporadic.J2 CFSG.Sporadic.Th.Native CFSG.Blueprint.NativeSporadic

theorem j2_tab_a : tab 315 (a : J) = j2ta := tab_eq_of_rep _ _ rep_alpha

theorem j2_tab_b : tab 315 (b : J) = j2tb := tab_eq_of_rep _ _ rep_beta

theorem j2_valid : slpValidAux j2Prog 2 = true :=
  Certificates.certificate4142.1

theorem j2_cert :
    BaseCertS 315 (List.range 315) j2SLP j2Qp 143 181 185 183 187
      j2Enum.1 j2Enum.2.1 j2Enum.2.2 7 :=
  Certificates.certificate4142.2

theorem j2_group_noStronglyClosedElemAbelian : NoStronglyClosedElemAbelian J := by
  refine noStronglyClosedElemAbelian_of_baseCertS (n := 315) (List.range 315)
    (fun b hb => List.mem_range.mp hb) base_of_faithful (a : J) (b : J) j2Prog j2_valid j2Qp
    143 181 185 183 187 j2Enum.1 j2Enum.2.1 j2Enum.2.2 7 4725
    (by rw [card_J]; norm_num) (by decide) ?_
  rw [j2_tab_a, j2_tab_b]
  exact j2_cert

theorem j2_noStronglyClosedElemAbelian : NoStronglyClosedElemAbelian (Carrier .J2) := by
  have h : NoStronglyClosedElemAbelian CFSG.Blueprint.NativeSporadic.J2 :=
    NoStronglyClosedElemAbelian.of_mulEquiv (X := CFSG.Blueprint.NativeSporadic.J2) (Y := ↥J)
      CFSG.Sporadic.Bridge.J2.nativeEquiv j2_group_noStronglyClosedElemAbelian
  exact h

end CFSG.QuasithinUnique.K1.SporadicPerm
