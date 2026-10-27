module

public import CFSG.ClassicalInvolution.Q3.Q3T7P24V01
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf11H00

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q8P.P24

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q8P.Asc77
open scoped commutatorElement

section Vertex

variable {G : Type} [Group G] [Finite G]

theorem isSolvable_of_quot2 {M : Subgroup G}
    (h2 : IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M)) : Group.IsSolvable ↥M := by
  have h1 : Group.IsSolvable (↥M ⧸ classicalInvolutionOddCore ↥M) := by
    have := h2.isNilpotent
    infer_instance
  have h3 : Group.IsSolvable (classicalInvolutionOddCore ↥M) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (CFSG.ComponentClassification.OddCore.odd_card ↥M)
  exact Group.isSolvable_of_subgroup_quotient (classicalInvolutionOddCore ↥M)

theorem commutator_component_modOdd_of_quot2 {M : Subgroup G} {z : G}
    (hsub : IsSubnormal M (Subgroup.centralizer ({z} : Set G)))
    (h2 : IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M)) {L : Subgroup (OddQuot z)}
    (hL : CFSG.IsComponent L) : ⁅L, modOdd z M⁆ = ⊥ := by
  have hMC : M ≤ Subgroup.centralizer ({z} : Set G) := isSubnormal_le hsub
  exact (CFSG.LocalCores.component_solvable_centralizer
    (Q3.Q3T7P24.isSolvable_modOdd_of_solvable hMC (isSolvable_of_quot2 h2))
    (Q3.Q3T7P24.isSubnormal_modOdd_of_subnormal hsub)).1 L hL

end Vertex

theorem hyp51VertexP_proved : Hyp51VertexP := by
  intro G _ _ _ Ω K₀ hst h2 K K' z x y e₁ e₂ hKΩ hK'Ω hzK hzK' B hB hzB hxK hyK' hxyB hxy1 hxyz
    _ _ _ _ _ _ _ _
  have hsub₁ := hst.cls.isSubnormal_of_uniqueInvolution hKΩ hzK
  have hsub₂ := hst.cls.isSubnormal_of_uniqueInvolution hK'Ω hzK'
  have hz1 : z ≠ 1 := hzK.ne_one
  have hKz : K ≤ Subgroup.centralizer ({z} : Set G) := isSubnormal_le hsub₁
  have hK'z : K' ≤ Subgroup.centralizer ({z} : Set G) := isSubnormal_le hsub₂
  have hx' : x ∈ Subgroup.centralizer ({z} : Set G) := hKz hxK
  have hy' : y ∈ Subgroup.centralizer ({z} : Set G) := hK'z hyK'
  have hxC : x * y ∈ Subgroup.centralizer ({z} : Set G) :=
    (Subgroup.centralizer ({z} : Set G)).mul_mem hx' hy'
  have hno : ∀ L : Subgroup (OddQuot z), CFSG.IsComponent L → MovedByAll B z L → False := by
    intro L hL hmov
    have hxm : oddQuotMk z ⟨x * y, hxC⟩ ∈ modOdd z B := oddQuotMk_mem_modOdd hxyB hxC
    have hnot := Lemma52Proof.oddQuotMk_not_mem_zpowers hB hzB hz1 hxyB hxy1 hxyz hxC
    obtain ⟨w, hw, hwne⟩ := hmov _ hxm hnot
    apply hwne
    have hcx : ∀ v ∈ L, v * oddQuotMk z ⟨x, hx'⟩ = oddQuotMk z ⟨x, hx'⟩ * v := by
      intro v hv
      have h1 : ⁅v, oddQuotMk z ⟨x, hx'⟩⁆ ∈ ⁅L, modOdd z K⁆ :=
        Subgroup.commutator_mem_commutator hv (oddQuotMk_mem_modOdd hxK hx')
      rw [commutator_component_modOdd_of_quot2 hsub₁ (h2 K hKΩ) hL, Subgroup.mem_bot,
        commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    have hcy : ∀ v ∈ L, v * oddQuotMk z ⟨y, hy'⟩ = oddQuotMk z ⟨y, hy'⟩ * v := by
      intro v hv
      have h1 : ⁅v, oddQuotMk z ⟨y, hy'⟩⁆ ∈ ⁅L, modOdd z K'⁆ :=
        Subgroup.commutator_mem_commutator hv (oddQuotMk_mem_modOdd hyK' hy')
      rw [commutator_component_modOdd_of_quot2 hsub₂ (h2 K' hK'Ω) hL, Subgroup.mem_bot,
        commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    have e1 : oddQuotMk z ⟨x * y, hxC⟩ = oddQuotMk z ⟨x, hx'⟩ * oddQuotMk z ⟨y, hy'⟩ := by
      rw [← map_mul]
      rfl
    rw [e1, mul_assoc, ← hcy w hw, ← mul_assoc, ← hcx w hw, mul_assoc]
  exact ⟨fun L₁ L₂ h1 _ m1 _ => (hno L₁ h1 m1).elim, fun L hL hm => (hno L hL hm).elim⟩

end CFSG.ClassicalInvolution.Q8P.P24
