module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBase
public meta import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBaseNative
public import CFSG.Sporadic.Mathieu.M11
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M22
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.Schreier.M23Gens
public import CFSG.Sporadic.Schreier.M23
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicMathieuInputs
public import Certificates.Certificate4075
public import Certificates.Certificate2197
public import Certificates.Certificate3017
public import Certificates.Certificate3029
public import Certificates.Certificate3086
public import Certificates.Certificate3120
public import CFSG.Foundations
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.QuasithinUnique.K1.Interface
public import CFSG.Sporadic.M23.M23Group
public import Certificates.Certificate113

public section

namespace CFSG.QuasithinUnique.K1.SporadicPerm

open CFSG.Sporadic.Mathieu (m11a m11b m12a m12b m22a m22b m24a m24b card_M11 card_M12 card_M22
  card_M24)
open CFSG.Sporadic.Schreier (m23GenA m23GenB m23_card)

theorem m11_tab_a : tab 11 m11a = m11ta := by decide +kernel

theorem m11_tab_b : tab 11 m11b = m11tb := by decide +kernel

theorem m11_valid : slpValidAux m11Prog 2 = true :=
  Certificates.certificate4075.1

theorem m11_cert :
    BaseCertS 11 (List.range 11) m11SLP m11Qp 159 189 193 191 195
      m11Enum.1 m11Enum.2.1 m11Enum.2.2 4 :=
  Certificates.certificate4075.2.1

theorem m11_noStronglyClosedElemAbelian :
    NoStronglyClosedElemAbelian ↥CFSG.Blueprint.NativeSporadic.M11 := by
  refine noStronglyClosedElemAbelian_of_baseCertS (n := 11) (List.range 11)
    (fun b hb => List.mem_range.mp hb) base_of_faithful m11a m11b m11Prog m11_valid m11Qp
    159 189 193 191 195 m11Enum.1 m11Enum.2.1 m11Enum.2.2 4 495
    (by rw [card_M11]; norm_num) (by decide) ?_
  rw [m11_tab_a, m11_tab_b]
  exact m11_cert

theorem m12_tab_a : tab 12 m12a = m12ta := by decide +kernel

theorem m12_tab_b : tab 12 m12b = m12tb := by decide +kernel

theorem m12_valid : slpValidAux m12Prog 2 = true :=
  Certificates.certificate4075.2.2.1

theorem m12_cert :
    BaseCertS 12 (List.range 12) m12SLP m12Qp 153 204 208 206 210
      m12Enum.1 m12Enum.2.1 m12Enum.2.2 6 :=
  Certificates.certificate4075.2.2.2.1

theorem m12_noStronglyClosedElemAbelian :
    NoStronglyClosedElemAbelian ↥CFSG.Blueprint.NativeSporadic.M12 := by
  refine noStronglyClosedElemAbelian_of_baseCertS (n := 12) (List.range 12)
    (fun b hb => List.mem_range.mp hb) base_of_faithful m12a m12b m12Prog m12_valid m12Qp
    153 204 208 206 210 m12Enum.1 m12Enum.2.1 m12Enum.2.2 6 1485
    (by rw [card_M12]; norm_num) (by decide) ?_
  rw [m12_tab_a, m12_tab_b]
  exact m12_cert

theorem m22_tab_a : tab 22 m22a = m22ta := by decide +kernel

theorem m22_tab_b : tab 22 m22b = m22tb := by decide +kernel

theorem m22_valid : slpValidAux m22Prog 2 = true :=
  Certificates.certificate4075.2.2.2.2.1

theorem m22_cert :
    BaseCertS 22 (List.range 22) m22SLP m22Qp 163 205 209 207 211
      m22Enum.1 m22Enum.2.1 m22Enum.2.2 7 :=
  Certificates.certificate4075.2.2.2.2.2.1

theorem m22_noStronglyClosedElemAbelian :
    NoStronglyClosedElemAbelian ↥CFSG.Blueprint.NativeSporadic.M22 := by
  refine noStronglyClosedElemAbelian_of_baseCertS (n := 22) (List.range 22)
    (fun b hb => List.mem_range.mp hb) base_of_faithful m22a m22b m22Prog m22_valid m22Qp
    163 205 209 207 211 m22Enum.1 m22Enum.2.1 m22Enum.2.2 7 3465
    (by rw [card_M22]; norm_num) (by decide) ?_
  rw [m22_tab_a, m22_tab_b]
  exact m22_cert

theorem m23_tab_a : tab 23 m23GenA = m23ta := by decide +kernel

theorem m23_tab_b : tab 23 m23GenB = m23tb := by decide +kernel

theorem m23_valid : slpValidAux m23Prog 2 = true :=
  Certificates.certificate4075.2.2.2.2.2.2.1

theorem m23_cert :
    BaseCertS 23 (List.range 23) m23SLP m23Qp 159 199 203 201 205
      m23Enum.1 m23Enum.2.1 m23Enum.2.2 7 :=
  Certificates.certificate4075.2.2.2.2.2.2.2.1

theorem m23_noStronglyClosedElemAbelian :
    NoStronglyClosedElemAbelian ↥CFSG.Blueprint.NativeSporadic.M23 := by
  refine noStronglyClosedElemAbelian_of_baseCertS (n := 23) (List.range 23)
    (fun b hb => List.mem_range.mp hb) base_of_faithful m23GenA m23GenB m23Prog m23_valid m23Qp
    159 199 203 201 205 m23Enum.1 m23Enum.2.1 m23Enum.2.2 7 79695
    (by rw [m23_card]; norm_num) (by decide) ?_
  rw [m23_tab_a, m23_tab_b]
  exact m23_cert

theorem m24_tab_a : tab 24 m24a = m24ta := by decide +kernel

theorem m24_tab_b : tab 24 m24b = m24tb := by decide +kernel

theorem m24_valid : slpValidAux m24Prog 2 = true :=
  Certificates.certificate4075.2.2.2.2.2.2.2.2.1

theorem m24_cert :
    BaseCertS 24 (List.range 24) m24SLP m24Qp 162 213 216 214 217
      m24Enum.1 m24Enum.2.1 m24Enum.2.2 10 :=
  Certificates.certificate4075.2.2.2.2.2.2.2.2.2

theorem m24_noStronglyClosedElemAbelian :
    NoStronglyClosedElemAbelian ↥CFSG.Blueprint.NativeSporadic.M24 := by
  refine noStronglyClosedElemAbelian_of_baseCertS (n := 24) (List.range 24)
    (fun b hb => List.mem_range.mp hb) base_of_faithful m24a m24b m24Prog m24_valid m24Qp
    162 213 216 214 217 m24Enum.1 m24Enum.2.1 m24Enum.2.2 10 239085
    (by rw [card_M24]; norm_num) (by decide) ?_
  rw [m24_tab_a, m24_tab_b]
  exact m24_cert

end CFSG.QuasithinUnique.K1.SporadicPerm
