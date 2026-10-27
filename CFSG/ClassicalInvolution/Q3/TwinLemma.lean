module

public import CFSG.ClassicalInvolution.Balance.Basic
public import CFSG.ClassicalInvolution.Q3.TwinLemmaCore
import CFSG.GroupTheory.SubnormalJoin
import CFSG.ClassicalInvolution.SubnormalClosure.Basic

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Balance
open CFSG.ComponentClassification
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem isSubnormal_subgroupOf_top {X K : Subgroup G} (h : IsSubnormal K X) :
    (K.subgroupOf X).IsSubnormal := by
  have := isSubnormal_subgroupOf h X
  rw [Subgroup.subgroupOf_self] at this
  exact Components.mathlib_subnormal_of_chain this Subgroup.IsSubnormal.top

theorem twinLemma3 {C J₁ J₂ : Subgroup G} {z : G} (hC : oddCoreIn C = ⊥)
    (h₁ : IsSubnormal J₁ C) (h₂ : IsSubnormal J₂ C)
    (e₁ : Nonempty (↥J₁ ≃* SL(2, ZMod 3))) (e₂ : Nonempty (↥J₂ ≃* SL(2, ZMod 3)))
    (hz : orderOf z = 2) (hz₁ : z ∈ J₁) (hz₂ : z ∈ J₂) : J₁ = J₂ ∨ ⁅J₁, J₂⁆ = ⊥ := by
  obtain ⟨e₁⟩ := e₁
  obtain ⟨e₂⟩ := e₂
  have hJ₁C : J₁ ≤ C := isSubnormal_le h₁
  have hJ₂C : J₂ ≤ C := isSubnormal_le h₂
  have hHC : J₁ ⊔ J₂ ≤ C := sup_le hJ₁C hJ₂C
  have hHsub : IsSubnormal (J₁ ⊔ J₂) C := by
    have a₁ := isSubnormal_subgroupOf_top h₁
    have a₂ := isSubnormal_subgroupOf_top h₂
    have hj := CFSG.GroupTheory.isSubnormal_sup a₁ a₂
    have := Components.chain_map C.subtype (Components.chain_of_mathlib_subnormal hj)
    rwa [Subgroup.map_top, Subgroup.range_subtype, Subgroup.map_sup,
      Subgroup.map_subgroupOf_eq_of_le hJ₁C, Subgroup.map_subgroupOf_eq_of_le hJ₂C] at this
  have hOH : oddCoreIn (J₁ ⊔ J₂) = ⊥ :=
    le_bot_iff.mp (hC ▸ oddCoreIn_le_of_isSubnormal hHsub)
  have hJ₁H : J₁ ≤ J₁ ⊔ J₂ := le_sup_left
  have hJ₂H : J₂ ≤ J₁ ⊔ J₂ := le_sup_right
  have hsub : ∀ J : Subgroup G, IsSubnormal J C → J ≤ J₁ ⊔ J₂ → IsSubnormal J (J₁ ⊔ J₂) := by
    intro J hJ hJH
    have := isSubnormal_inf hJ (J₁ ⊔ J₂)
    rwa [inf_eq_left.mpr hJH, inf_eq_right.mpr hHC] at this
  set H : Subgroup G := J₁ ⊔ J₂ with hH
  have hY : J₁.subgroupOf H ⊔ J₂.subgroupOf H = ⊤ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hJ₁H,
      Subgroup.map_subgroupOf_eq_of_le hJ₂H, Subgroup.map_top, Subgroup.range_subtype]
  have hO : ∀ N : Subgroup ↥H, N.Normal → Odd (Nat.card N) → N = ⊥ := by
    intro N hN hodd
    have hle : N.map H.subtype ≤ oddCoreIn H := by
      refine le_oddCoreIn_of_normalizes (Subgroup.map_subtype_le N) ?_ ?_
      · intro x hx
        rw [Subgroup.mem_normalizer_iff]
        intro y
        constructor
        · rintro ⟨n, hn, rfl⟩
          exact ⟨⟨x, hx⟩ * n * ⟨x, hx⟩⁻¹, hN.conj_mem n hn ⟨x, hx⟩, rfl⟩
        · rintro ⟨n, hn, hny⟩
          refine ⟨⟨x, hx⟩⁻¹ * n * ⟨x, hx⟩, by simpa using hN.conj_mem n hn ⟨x, hx⟩⁻¹, ?_⟩
          have h : (n : G) = x * y * x⁻¹ := hny
          have : y = x⁻¹ * (n : G) * x := by rw [h]; group
          simp [this]
      · rwa [Subgroup.card_map_of_injective H.subtype_injective]
    rw [hOH, le_bot_iff] at hle
    exact (Subgroup.map_eq_bot_iff_of_injective N H.subtype_injective).mp hle
  have hz' : orderOf (⟨z, hJ₁H hz₁⟩ : ↥H) = 2 := by
    rw [← hz]
    exact Subgroup.orderOf_mk z _
  rcases Twin.twinLemma3_core hY hO (isSubnormal_subgroupOf_top (hsub J₁ h₁ hJ₁H))
      (isSubnormal_subgroupOf_top (hsub J₂ h₂ hJ₂H))
      ((Subgroup.subgroupOfEquivOfLe hJ₁H).trans e₁) ((Subgroup.subgroupOfEquivOfLe hJ₂H).trans e₂)
      hz' (Subgroup.mem_subgroupOf.mpr hz₁) (Subgroup.mem_subgroupOf.mpr hz₂) with h | h
  · left
    have := congrArg (Subgroup.map H.subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hJ₁H, Subgroup.map_subgroupOf_eq_of_le hJ₂H] at this
  · right
    have := congrArg (Subgroup.map H.subtype) h
    rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hJ₁H,
      Subgroup.map_subgroupOf_eq_of_le hJ₂H, Subgroup.map_bot] at this

theorem eq_of_same_quaternion {C J₁ J₂ : Subgroup G} {z : G} (hC : oddCoreIn C = ⊥)
    (h₁ : IsSubnormal J₁ C) (h₂ : IsSubnormal J₂ C)
    (e₁ : Nonempty (↥J₁ ≃* SL(2, ZMod 3))) (e₂ : Nonempty (↥J₂ ≃* SL(2, ZMod 3)))
    (hz : orderOf z = 2) (hz₁ : z ∈ J₁) (hz₂ : z ∈ J₂)
    (hQ : ∃ Q : Subgroup G, IsPGroup 2 Q ∧ Nat.card Q = 8 ∧ Q ≤ J₁ ∧ Q ≤ J₂) : J₁ = J₂ := by
  rcases twinLemma3 hC h₁ h₂ e₁ e₂ hz hz₁ hz₂ with h | h
  · exact h
  · exfalso
    obtain ⟨Q, hQ2, hQ8, hQ₁, hQ₂⟩ := hQ
    obtain ⟨e⟩ := e₁
    have hQe : Q = Twin.quatIn e := Twin.eq_quatIn_of_card_eq e hQ₁ hQ2 hQ8
    obtain ⟨a, b, ha, hb, hab⟩ := Twin.exists_noncomm_quatIn e
    rw [← hQe] at ha hb
    have hac : a ∈ Subgroup.centralizer (J₂ : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp h (hQ₁ ha)
    exact hab (Subgroup.mem_centralizer_iff.mp hac b (hQ₂ hb)).symm

end CFSG.ClassicalInvolution.Q3
