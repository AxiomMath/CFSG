module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBaseVec
public meta import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBaseNative
public import CFSG.Sporadic.HS
public meta import Certificates.Data.CFSGNative.HS.Data
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHSInputs
public import Certificates.Certificate4140
public import Certificates.Certificate3167
public import CFSG.Foundations
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.QuasithinUnique.K1.Interface
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicRep
public import CFSG.Sporadic.Th.F2Spec
public import Certificates.Certificate113

public section

namespace CFSG.QuasithinUnique.K1.SporadicPerm

open CFSG.Sporadic.SmallF2
open CFSG.Sporadic.Th.Native (ap)
open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.Sporadic.HS.Native (hsData)

theorem hs_valid : slpValidAux hsProg 2 = true :=
  Certificates.certificate4140.1

theorem hs_cert :
    BaseCertS hsData.n hsB hsSLP hsQp 164 202 206 204 208
      hsEnum.1 hsEnum.2.1 hsEnum.2.2 9 :=
  Certificates.certificate4140.2

theorem hs_group_noStronglyClosedElemAbelian : NoStronglyClosedElemAbelian (J hsData) := by
  have hF : Facts hsData 3 := CFSG.Sporadic.HS.hsFacts
  have ha : tab hsData.n (a hsData) = hsTa.toList := by
    rw [tab_eq_of_rep (n := hsData.n) _ (a hsData) (rep_a hF.toBaseFacts)]
    simp [hsTa]
  have hb : tab hsData.n (b hsData) = hsTb.toList := by
    rw [tab_eq_of_rep (n := hsData.n) _ (b hsData) (rep_b hF.toBaseFacts)]
    simp [hsTb]
  have hcard0 : Nat.card (J hsData) = 44352000 :=
    (Nat.card_congr (seedEquiv hF.toBaseFacts).toEquiv).symm.trans CFSG.Sporadic.HS.card_HS
  have hcard : Nat.card (J hsData) = 2 ^ 9 * 86625 := by
    rw [hcard0]; norm_num
  refine noStronglyClosedElemAbelian_of_baseCertS (n := hsData.n) hsB
    (base_lt hF) (base_property hF) (a hsData) (b hsData) hsProg hs_valid hsQp
    164 202 206 204 208 hsEnum.1 hsEnum.2.1 hsEnum.2.2 9 86625 hcard
    (by decide) ?_
  rw [ha, hb, Array.toArray_toList, Array.toArray_toList]
  exact hs_cert

theorem hs_noStronglyClosedElemAbelian : NoStronglyClosedElemAbelian (Carrier .HS) := by
  have hF : Facts hsData 3 := CFSG.Sporadic.HS.hsFacts
  have h : NoStronglyClosedElemAbelian CFSG.Blueprint.NativeSporadic.HS :=
    NoStronglyClosedElemAbelian.of_mulEquiv (X := CFSG.Blueprint.NativeSporadic.HS)
      (Y := ↥(J hsData)) (seedEquiv hF.toBaseFacts) hs_group_noStronglyClosedElemAbelian
  exact h

end CFSG.QuasithinUnique.K1.SporadicPerm
