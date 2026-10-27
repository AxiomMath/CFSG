module

public import CFSG.ClassicalInvolution.Q3.Q3E8Facts
public import CFSG.ClassicalInvolution.Q3.Q3TCCp
public import CFSG.ClassicalInvolution.Q3.Q3TCP1
public import CFSG.ClassicalInvolution.Q3.Q3PStage

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.CurtisTits CFSG.Timmesfeld
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.LieType.Steinberg.Adjoint (iform)
open scoped MatrixGroups commutatorElement

set_option linter.unusedSectionVars false


theorem e8P1x3_of_productP1 (h : Q3TC.ProductP1Input3) : E8P1x3 := by
  intro G _ _ _ hnab K z hR W₁ W₂ w₁ w₂ hW₁ hW₂ hw₁ hw₂ hKW₁ hKW₂ hW₁₂ hcard
  have hz2 : z * z = 1 := mul_self_of_isClassicalMember3 hR.cls
  have hw₁2 : w₁ * w₁ = 1 := mul_self_of_isClassicalMember3 hw₁
  have hzw₁ : z * w₁ = w₁ * z := hKW₁ z hR.cls.mem w₁ hw₁.mem
  have hne : w₁ ≠ w₂ := by
    intro hw
    have hle := Q3.card_closure_pair_le_four hz2 hw₁2 hzw₁
    have hset : ({z, w₁, w₂} : Set G) = {z, w₁} := by
      subst hw
      ext y
      simp
    rw [hset] at hcard
    omega
  have hS₁ : RouteD3Setup W₁ w₁ := Q3TC.RouteD3Setup.of_mem_conjClass3 hR hW₁ hw₁
  have hcl : conjClass3 W₁ = conjClass3 K := Q3TC.conjClass3_eq_of_mem hW₁
  have hW₂' : W₂ ∈ conjClass3 W₁ := by
    rw [hcl]
    exact hW₂
  have := h G W₁ w₁ hS₁ W₂ hW₂' w₂ hw₂ hW₁₂ hne
  rwa [hcl] at this

end CFSG.ClassicalInvolution.Q3.Q3W
