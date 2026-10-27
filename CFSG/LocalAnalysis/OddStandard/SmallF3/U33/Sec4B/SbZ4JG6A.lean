module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4NA

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

namespace Ctx4Z


variable (hz : Ctx4Z t L S x₁ x₂ lam rho tau)
include hz

theorem z4j_count17 {V'' : Subgroup G} (hV''S : V'' ≤ S)
    (hn : ∀ s ∈ S, ∀ v ∈ V'', s * v * s⁻¹ ∈ V'') (h4 : Nat.card V'' = 4)
    (he : ∀ a ∈ V'', ∀ b ∈ V'', a * b = b * a ∧ a * a = 1)
    (ht : ∀ g : G, ∀ v ∈ V'', g * t * g⁻¹ ≠ v) :
    17 ≤ {x : G | x ∈ S ⊓ centralizer (V'' : Set G) ∧ x * x = 1}.ncard := by
  have hEA : CFSG.Open.IsElemAbelian 2 V'' :=
    ⟨IsMulCommutative.of_comm fun a b => Subtype.ext (he a a.2 b b.2).1,
      fun x hx => by rw [pow_two]; exact (he x hx x hx).2⟩
  have hC : S ⊓ centralizer (V'' : Set G) = zpowers t ⊔ closure {x₁, x₂, tau} :=
    (hz.toCtx10.l45 V'' ⟨hV''S, hn⟩ hEA h4 ht).2.1
  have hsub_cl : ({x₁, x₂} : Set G) ⊆ ({x₁, x₂, tau} : Set G) := by
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg ⊢
    tauto
  let f : G → G := fun b => b * tau
  have hf_inj : Function.Injective f := fun a b h => mul_right_cancel h
  have hBcard : ((baseGrp x₁ x₂ : Subgroup G) : Set G).ncard = 16 := by
    rw [← Nat.card_coe_set_eq]
    exact hz.nGood.card_B
  have hnot1 : (1 : G) ∉ f '' ((baseGrp x₁ x₂ : Subgroup G) : Set G) := by
    rintro ⟨b, hb, hb1⟩
    change b * tau = 1 at hb1
    have hbQ : b ∈ ctxQ t tau x₁ x₂ rho := hz.base_le_Q hb
    have hb_eq : b = tau⁻¹ := eq_inv_of_mul_eq_one_left hb1
    have htauQ : tau⁻¹ ∈ ctxQ t tau x₁ x₂ rho := hb_eq ▸ hbQ
    exact hz.tau_not_mem_Q (by simpa using inv_mem htauQ)
  have hAcard : (insert (1 : G) (f '' ((baseGrp x₁ x₂ : Subgroup G) : Set G))).ncard = 17 := by
    rw [Set.ncard_insert_of_notMem hnot1, Set.ncard_image_of_injective _ hf_inj, hBcard]
  have hAsub : insert (1 : G) (f '' ((baseGrp x₁ x₂ : Subgroup G) : Set G)) ⊆
      {x : G | x ∈ S ⊓ centralizer (V'' : Set G) ∧ x * x = 1} := by
    intro y hy
    rcases hy with rfl | ⟨b, hb, rfl⟩
    · exact ⟨by rw [hC]; exact one_mem _, one_mul 1⟩
    · have hbQ : b ∈ ctxQ t tau x₁ x₂ rho := hz.base_le_Q hb
      have hbtau : b * tau ∈ zpowers t ⊔ closure ({x₁, x₂, tau} : Set G) :=
        Subgroup.mem_sup_right (Subgroup.mul_mem _
          (Subgroup.closure_mono hsub_cl hb)
          (Subgroup.mem_closure_of_mem (by simp)))
      refine ⟨by rw [hC]; exact hbtau, ?_⟩
      have htau2 : tau * tau = 1 := hz.tau_mul_self
      calc (b * tau) * (b * tau) = b * (tau * b * tau⁻¹) * (tau * tau) := by group
        _ = b * b⁻¹ * 1 := by rw [hz.tau_inv_Q b hbQ, htau2]
        _ = 1 := by simp
  rw [← hAcard]
  exact Set.ncard_le_ncard hAsub

end Ctx4Z

end CFSG.OddStandard.SmallF3.HarrisU33
