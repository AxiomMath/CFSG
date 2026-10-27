module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8MAFacts

public section

namespace CFSG.ComponentClassification.HSFLit

open Sec8

namespace KD8ab

@[expose] def dImgs (gy c₁ c₂ : MA) : List MA :=
  [1, MA.y * MA.u * gy, MA.w₁ * c₁, MA.v * MA.w₁ * c₂, MA.z, gy, MA.t, MA.z * MA.k]

@[expose] def dAct (gy c₁ c₂ a : MA) : MA := nfProd (dImgs gy c₁ c₂) (MA.nfBits a)

@[expose] def gens7 : List MA := [MA.u, MA.w₁, MA.v, MA.z, MA.y, MA.t, MA.k]

@[expose] def cOne (e : Bool) : MA := if e then MA.k else 1

@[expose] def tE (e : Bool) : MA := if e then MA.t else 1

@[expose] def dc (e : Bool) (c₂ a : MA) : MA := dAct MA.u (cOne e) c₂ a

@[expose] def dci (e : Bool) (c₂ a : MA) : MA := tE e * dc e c₂ a * tE e

@[expose] def pAct (e : Bool) (c₂ a : MA) : MA := dc e c₂ (MA.w₂ * dci e c₂ a * MA.w₂⁻¹)

@[expose] def SqOK (e : Bool) (gy c₁ c₂ : MA) : Bool :=
  gens7.all fun g => dAct gy c₁ c₂ (dAct gy c₁ c₂ g) = tE e * g * tE e

@[expose] def CanonOK (e : Bool) (gy c₁ c₂ r c₂' : MA) : Bool :=
  (gens7.all fun g => dAct gy c₁ c₂ (r * g * r⁻¹) = dc e c₂' g) &&
    (dAct gy c₁ c₂ r * tE e * r = tE e)

theorem nfBits_T1 : ∀ a : MA, MA.inT1 a = true → MA.nfBits a = false :: (MA.nfBits a).tail := by
  decide +kernel

theorem dAct_T1 : ∀ gy ∈ [MA.u, MA.z * MA.u], ∀ c₁ ∈ MA.ZList, ∀ c₂ ∈ MA.ZList, ∀ a : MA,
    MA.inT1 (dAct gy c₁ c₂ a) = true := by decide +kernel

theorem dAct_gens (gy c₁ c₂ : MA) :
    dAct gy c₁ c₂ MA.u = MA.y * MA.u * gy ∧ dAct gy c₁ c₂ MA.w₁ = MA.w₁ * c₁ ∧
      dAct gy c₁ c₂ MA.v = MA.v * MA.w₁ * c₂ ∧ dAct gy c₁ c₂ MA.z = MA.z ∧
      dAct gy c₁ c₂ MA.y = gy ∧ dAct gy c₁ c₂ MA.t = MA.t ∧
      dAct gy c₁ c₂ MA.k = MA.z * MA.k := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [dAct, dImgs, show MA.nfBits MA.u = [false, true, false, false, false, false, false,
      false] by decide +kernel, show MA.nfBits MA.w₁ = [false, false, true, false, false, false,
      false, false] by decide +kernel, show MA.nfBits MA.v = [false, false, false, true, false,
      false, false, false] by decide +kernel, show MA.nfBits MA.z = [false, false, false, false,
      true, false, false, false] by decide +kernel, show MA.nfBits MA.y = [false, false, false,
      false, false, true, false, false] by decide +kernel, show MA.nfBits MA.t = [false, false,
      false, false, false, false, true, false] by decide +kernel, show MA.nfBits MA.k = [false,
      false, false, false, false, false, false, true] by decide +kernel, nfProd]

theorem canon_exists : ∀ e : Bool, ∀ gy ∈ [MA.u, MA.z * MA.u], ∀ c₁ ∈ MA.ZList,
    ∀ c₂ ∈ MA.ZList, SqOK e gy c₁ c₂ = true →
    ∃ r ∈ [1, MA.t, MA.u * MA.y, MA.u * MA.y * MA.t], ∃ c₂' ∈ [1, MA.z],
      CanonOK e gy c₁ c₂ r c₂' = true := by
  decide +kernel

theorem actsW_pAct : ∀ e : Bool, ∀ c₂ ∈ [1, MA.z],
    pAct e c₂ MA.t = MA.t * MA.u ∧ pAct e c₂ MA.u = MA.u ∧
    pAct e c₂ MA.y = MA.y * MA.w₁ * cOne e ∧ pAct e c₂ MA.z = MA.z ∧ pAct e c₂ MA.k = MA.k ∧
    pAct e c₂ MA.w₁ = MA.w₁ ∧ pAct e c₂ MA.v = MA.v := by decide +kernel

theorem cOne_mem (e : Bool) : cOne e ∈ MA.ZList := by
  cases e <;> simp [cOne, MA.ZList]

end KD8ab

end CFSG.ComponentClassification.HSFLit
