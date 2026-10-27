module

public import Mathlib.GroupTheory.Transfer

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator

open Subgroup

theorem eq_one_of_mem_center_commutator_of_abelian_sylow {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) (hP : IsMulCommutative (P : Subgroup G)) {z : G}
    (hzP : z ∈ (P : Subgroup G)) (hzZ : z ∈ Subgroup.center G) (hzK : z ∈ commutator G) :
    z = 1 := by
  classical
  let _ : CommGroup (P : Subgroup G) :=
    { (inferInstance : Group (P : Subgroup G)) with
      mul_comm := fun a b => hP.is_comm.comm a b }
  have hker : commutator G ≤ (MonoidHom.transfer (MonoidHom.id (P : Subgroup G))).ker := by
    show ⁅(⊤ : Subgroup G), ⊤⁆ ≤ _
    refine commutator_le.mpr fun g₁ _ g₂ _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  have hz : MonoidHom.transfer (MonoidHom.id (P : Subgroup G)) z = 1 := hker hzK
  have key : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * z ^ k * g₀ ∈ (P : Subgroup G) →
      g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have hc := Subgroup.mem_center_iff.mp ((Subgroup.center G).pow_mem hzZ k) g₀
    calc g₀⁻¹ * z ^ k * g₀ = g₀⁻¹ * (z ^ k * g₀) := by rw [mul_assoc]
      _ = g₀⁻¹ * (g₀ * z ^ k) := by rw [hc]
      _ = z ^ k := by group
  have h1 := MonoidHom.transfer_eq_pow (MonoidHom.id (P : Subgroup G)) z key
  have h2 := h1.symm.trans hz
  have h3 : z ^ (P : Subgroup G).index = 1 := by
    simpa using congrArg Subtype.val h2
  set w : (P : Subgroup G) := ⟨z, hzP⟩ with hw
  have hwindex : w ^ (P : Subgroup G).index = 1 := Subtype.ext (by simpa using h3)
  have hord : orderOf w ∣ (P : Subgroup G).index := orderOf_dvd_of_pow_eq_one hwindex
  have hord2 : orderOf w ∣ Nat.card (P : Subgroup G) := orderOf_dvd_natCard w
  have hcop : Nat.Coprime (Nat.card (P : Subgroup G)) (P : Subgroup G).index :=
    Sylow.card_coprime_index P
  have hone : orderOf w = 1 := Nat.eq_one_of_dvd_coprimes hcop hord2 hord
  have hw1 : w = 1 := orderOf_eq_one_iff.mp hone
  exact congrArg Subtype.val hw1

end CFSG.HardMathSupport.Foote.Coordinator

end
