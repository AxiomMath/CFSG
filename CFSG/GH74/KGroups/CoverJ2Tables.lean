module

public import Mathlib
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModelsNative
public meta import CFSG.LocalAnalysis.ComponentClassification.J2CoverModelsNative
public import CFSG.GH74.KGroups.CoverJ2TablesInputs
public meta import CFSG.GH74.KGroups.CoverJ2TablesInputs
public import Certificates.Certificate5110

public section

namespace CFSG.GH74.KGroups.J2

open CFSG.ComponentClassification.J2Cover.Models

theorem uList_lt :
    ∀ p ∈ uList, p.1 < 2 ∧ p.2 < 128 :=
  Certificates.certificate5110.1

theorem uList_nodup : uList.Nodup :=
  Certificates.certificate5110.2.1

theorem uList_length : uList.length = 64 :=
  Certificates.certificate5110.2.2.1

theorem uList_one : ((0, 0) : ℕ × ℕ) ∈ uList :=
  Certificates.certificate5110.2.2.2.1

theorem uList_mul :
    ∀ p ∈ uList, ∀ q ∈ uList, mulM p q ∈ uList :=
  Certificates.certificate5110.2.2.2.2.1

theorem uList_inv :
    ∀ p ∈ uList, ∃ q ∈ uList, mulM p q = (0, 0) :=
  Certificates.certificate5110.2.2.2.2.2.1

theorem nElt_mem : nElt ∈ uList :=
  Certificates.certificate5110.2.2.2.2.2.2.1

theorem nElt_sq : mulM nElt nElt = (0, 0) :=
  Certificates.certificate5110.2.2.2.2.2.2.2.1

theorem nElt_ne : nElt ≠ (0, 0) :=
  Certificates.certificate5110.2.2.2.2.2.2.2.2.1

theorem nElt_central :
    ∀ p ∈ uList, mulM nElt p = mulM p nElt :=
  Certificates.certificate5110.2.2.2.2.2.2.2.2.2.1

theorem u_sq :
    ∀ p ∈ uList, mulM p p = (0, 0) ∨ mulM p p = nElt :=
  Certificates.certificate5110.2.2.2.2.2.2.2.2.2.2.1

theorem u_comm : ∀ p ∈ uList, ∀ q ∈ uList,
    mulM p q = mulM (0, 0) (mulM q p) ∨ mulM p q = mulM nElt (mulM q p) :=
  Certificates.certificate5110.2.2.2.2.2.2.2.2.2.2.2

end CFSG.GH74.KGroups.J2
