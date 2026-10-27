module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUAE5Cent
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameVertex
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpWz
public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.GoodLift

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement



open CFSG.ClassicalInvolution.Balance

section U10

theorem hyp51At_of_twin_product {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    (hΩ : HypOmegaGen Ω) (hsolv : ∀ M ∈ Ω, Group.IsSolvable ↥M) {B : Subgroup G}
    (hB : IsElemAbelian 2 B) {c x k k' : G} {J J' : Subgroup G} (hJ : J ∈ Ω) (hJ' : J' ∈ Ω)
    (hc : IsUniqueInvolution J c) (hc' : IsUniqueInvolution J' c) (hcB : c ∈ B) (hxB : x ∈ B)
    (hc1 : c ≠ 1) (hx1 : x ≠ 1) (hxc : x ≠ c) (hk : k ∈ J) (hk' : k' ∈ J') (hx : x = k * k') :
    Hyp51At B c := by
  have hKz : J ≤ Subgroup.centralizer ({c} : Set G) := le_centralizer_of_unique hc
  have hK'z : J' ≤ Subgroup.centralizer ({c} : Set G) := le_centralizer_of_unique hc'
  have hKsub := isSubnormal_of_hypOmegaGen hΩ hJ hc
  have hK'sub := isSubnormal_of_hypOmegaGen hΩ hJ' hc'
  have hx' : k ∈ Subgroup.centralizer ({c} : Set G) := hKz hk
  have hy' : k' ∈ Subgroup.centralizer ({c} : Set G) := hK'z hk'
  have huC : x ∈ Subgroup.centralizer ({c} : Set G) := hx ▸ Subgroup.mul_mem _ hx' hy'
  have hno : ∀ L : Subgroup (OddQuot c), CFSG.IsComponent L → MovedByAll B c L → False := by
    intro L hL hmov
    have hxm : oddQuotMk c ⟨x, huC⟩ ∈ modOdd c B := oddQuotMk_mem_modOdd hxB huC
    have hnot := Lemma52Proof.oddQuotMk_not_mem_zpowers hB hcB hc1 hxB hx1 hxc huC
    obtain ⟨w, hw, hwne⟩ := hmov _ hxm hnot
    apply hwne
    have hcx : ∀ v ∈ L, v * oddQuotMk c ⟨k, hx'⟩ = oddQuotMk c ⟨k, hx'⟩ * v := by
      intro v hv
      have h1 : ⁅v, oddQuotMk c ⟨k, hx'⟩⁆ ∈ ⁅L, modOdd c J⁆ :=
        Subgroup.commutator_mem_commutator hv (oddQuotMk_mem_modOdd hk hx')
      rw [TwinFrame.commutator_component_modOdd_of_solvable hKsub (hsolv J hJ) hL,
        Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    have hcy : ∀ v ∈ L, v * oddQuotMk c ⟨k', hy'⟩ = oddQuotMk c ⟨k', hy'⟩ * v := by
      intro v hv
      have h1 : ⁅v, oddQuotMk c ⟨k', hy'⟩⁆ ∈ ⁅L, modOdd c J'⁆ :=
        Subgroup.commutator_mem_commutator hv (oddQuotMk_mem_modOdd hk' hy')
      rw [TwinFrame.commutator_component_modOdd_of_solvable hK'sub (hsolv J' hJ') hL,
        Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    have e1 : oddQuotMk c ⟨x, huC⟩ = oddQuotMk c ⟨k, hx'⟩ * oddQuotMk c ⟨k', hy'⟩ := by
      subst hx
      rw [← map_mul]
      rfl
    rw [e1, mul_assoc, ← hcy w hw, ← mul_assoc, ← hcx w hw, mul_assoc]
  exact ⟨fun L₁ L₂ h1 _ m1 _ => (hno L₁ h1 m1).elim, fun L hL hm => (hno L hL hm).elim⟩

end U10

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
