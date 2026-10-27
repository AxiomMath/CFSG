module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBaseVec
public meta import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBaseNative
public import CFSG.Sporadic.Ru
public meta import Certificates.Data.CFSGNative.Ru.Data
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicRuInputs
public import Certificates.Certificate4143
public import Certificates.Certificate3172
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
open CFSG.Sporadic.Ru.Native (ruData)

theorem ru_valid : slpValidAux ruProg 2 = true :=
  Certificates.certificate4143.1

theorem ru_cert :
    BaseCertS ruData.n ruB ruSLP ruQp 154 187 191 189 193
      ruEnum.1 ruEnum.2.1 ruEnum.2.2 14 :=
  Certificates.certificate4143.2

theorem ru_group_noStronglyClosedElemAbelian : NoStronglyClosedElemAbelian (J ruData) := by
  have hF : Facts ruData 3 := CFSG.Sporadic.Ru.ruFacts
  have ha : tab ruData.n (a ruData) = ruTa.toList := by
    rw [tab_eq_of_rep (n := ruData.n) _ (a ruData) (rep_a hF.toBaseFacts)]
    simp [ruTa]
  have hb : tab ruData.n (b ruData) = ruTb.toList := by
    rw [tab_eq_of_rep (n := ruData.n) _ (b ruData) (rep_b hF.toBaseFacts)]
    simp [ruTb]
  have hcard0 : Nat.card (J ruData) = 145926144000 :=
    (Nat.card_congr (seedEquiv hF.toBaseFacts).toEquiv).symm.trans CFSG.Sporadic.Ru.card_Ru
  have hcard : Nat.card (J ruData) = 2 ^ 14 * 8906625 := by
    rw [hcard0]; norm_num
  refine noStronglyClosedElemAbelian_of_baseCertS (n := ruData.n) ruB
    (base_lt hF) (base_property hF) (a ruData) (b ruData) ruProg ru_valid ruQp
    154 187 191 189 193 ruEnum.1 ruEnum.2.1 ruEnum.2.2 14 8906625 hcard
    (by decide) ?_
  rw [ha, hb, Array.toArray_toList, Array.toArray_toList]
  exact ru_cert

theorem ru_noStronglyClosedElemAbelian : NoStronglyClosedElemAbelian (Carrier .Ru) := by
  have hF : Facts ruData 3 := CFSG.Sporadic.Ru.ruFacts
  have h : NoStronglyClosedElemAbelian CFSG.Blueprint.NativeSporadic.Ru :=
    NoStronglyClosedElemAbelian.of_mulEquiv (X := CFSG.Blueprint.NativeSporadic.Ru)
      (Y := ↥(J ruData)) (seedEquiv hF.toBaseFacts) ru_group_noStronglyClosedElemAbelian
  exact h

end CFSG.QuasithinUnique.K1.SporadicPerm
