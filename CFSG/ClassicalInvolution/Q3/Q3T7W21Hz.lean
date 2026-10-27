module

public import CFSG.ClassicalInvolution.Q3.Q3T7P24V01
public import CFSG.ClassicalInvolution.Q3.Q3T7M03
public import CFSG.ClassicalInvolution.Q3.Q3T7W21A01

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
open scoped commutatorElement Pointwise


theorem twinFrameHyp51z_proved : TwinFrameHyp51z := by
  intro G _ _ _ Ω K K' J z u t hs
  have hΩ : Q3T7M.HM Ω := hs.hyp
  have hd := hs.frame
  have hKΩ : K ∈ Ω := hd.mem
  have hK'Ω : K' ∈ Ω := hd.hK'.1
  have hzK : IsUniqueInvolution K z := hd.hz
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hd.hz hd.hK'
  have hc₁ : Q3T8.Generic.IsClassicalMember K z := isClassicalMember_of_twin hΩ hKΩ hzK
  have hc₂ : Q3T8.Generic.IsClassicalMember K' z := isClassicalMember_of_twin hΩ hK'Ω hzK'
  have hz1 : z ≠ 1 := hzK.ne_one
  have hKz : K ≤ Subgroup.centralizer ({z} : Set G) := isSubnormal_le hc₁.subnormal
  have hK'z : K' ≤ Subgroup.centralizer ({z} : Set G) := isSubnormal_le hc₂.subnormal
  have hB : IsElemAbelian 2 (Subgroup.closure ({z, u, t} : Set G)) :=
    twinFrame_isElemAbelian hΩ hd
  have hzB : z ∈ Subgroup.closure ({z, u, t} : Set G) := Subgroup.subset_closure (by simp)
  have huB : u ∈ Subgroup.closure ({z, u, t} : Set G) := Subgroup.subset_closure (by simp)
  have hKN : K ≤ Subgroup.normalizer (K' : Set G) :=
    hΩ.le_normalizer_of_twin hKΩ hK'Ω hd.hne.symm hzK hzK'
  have hmul : ((K ⊔ K' : Subgroup G) : Set G) = (K : Set G) * (K' : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right K K' hKN
  have hu' : u ∈ (K : Set G) * (K' : Set G) := by
    rw [← hmul]
    exact hd.hu
  obtain ⟨x, hxK, y, hyK', hxy⟩ := hu'
  have hx' : x ∈ Subgroup.centralizer ({z} : Set G) := hKz hxK
  have hy' : y ∈ Subgroup.centralizer ({z} : Set G) := hK'z hyK'
  have huC : u ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [← hxy]
    exact (Subgroup.centralizer ({z} : Set G)).mul_mem hx' hy'
  have hno : ∀ L : Subgroup (OddQuot z), CFSG.IsComponent L →
      MovedByAll (Subgroup.closure ({z, u, t} : Set G)) z L → False := by
    intro L hL hmov
    have hum : oddQuotMk z ⟨u, huC⟩ ∈ modOdd z (Subgroup.closure ({z, u, t} : Set G)) :=
      oddQuotMk_mem_modOdd huB huC
    have hnot := Lemma52Proof.oddQuotMk_not_mem_zpowers hB hzB hz1 huB hd.hu1 hd.huz huC
    obtain ⟨w, hw, hwne⟩ := hmov _ hum hnot
    apply hwne
    have hcx : ∀ v ∈ L, v * oddQuotMk z ⟨x, hx'⟩ = oddQuotMk z ⟨x, hx'⟩ * v := by
      intro v hv
      have h1 : ⁅v, oddQuotMk z ⟨x, hx'⟩⁆ ∈ ⁅L, modOdd z K⁆ :=
        Subgroup.commutator_mem_commutator hv (oddQuotMk_mem_modOdd hxK hx')
      rw [Q3T7P24.commutator_component_modOdd_of_member hc₁ hL, Subgroup.mem_bot,
        commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    have hcy : ∀ v ∈ L, v * oddQuotMk z ⟨y, hy'⟩ = oddQuotMk z ⟨y, hy'⟩ * v := by
      intro v hv
      have h1 : ⁅v, oddQuotMk z ⟨y, hy'⟩⁆ ∈ ⁅L, modOdd z K'⁆ :=
        Subgroup.commutator_mem_commutator hv (oddQuotMk_mem_modOdd hyK' hy')
      rw [Q3T7P24.commutator_component_modOdd_of_member hc₂ hL, Subgroup.mem_bot,
        commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    have e1 : oddQuotMk z ⟨u, huC⟩ = oddQuotMk z ⟨x, hx'⟩ * oddQuotMk z ⟨y, hy'⟩ := by
      rw [← map_mul]
      congr 1
      exact Subtype.ext hxy.symm
    rw [e1, mul_assoc, ← hcy w hw, ← mul_assoc, ← hcx w hw, mul_assoc]
  exact ⟨fun L₁ L₂ h1 _ m1 _ => (hno L₁ h1 m1).elim, fun L hL hm => (hno L hL hm).elim⟩

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
