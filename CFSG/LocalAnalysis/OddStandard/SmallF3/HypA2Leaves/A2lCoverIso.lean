module

public import CFSG.LieType.Steinberg.CentralExt.PerfectCover

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup

theorem a2l_cover {K M : Type} [Group K] [Finite K] [Group.IsPerfect K] [Group M] [Finite M]
    (hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* M), Function.Surjective π →
      π.ker ≤ center E → IsPGroup 2 π.ker → ∃ σ : M →* E, ∀ x, π (σ x) = x)
    (h2 : IsPGroup 2 ↥(center K)) (N : Subgroup M) [N.Normal] (e : K ⧸ center K ≃* M ⧸ N) :
    ∃ α : M →* K, Function.Surjective α ∧ α.ker ≤ N ∧ center K = N.map α ∧
      ∀ s, e (QuotientGroup.mk (α s)) = QuotientGroup.mk s := by
  set β : M →* K ⧸ center K := e.symm.toMonoidHom.comp (QuotientGroup.mk' N) with hβdef
  set η : K →* K ⧸ center K := QuotientGroup.mk' (center K) with hηdef
  have hβ : Function.Surjective β := e.symm.surjective.comp (QuotientGroup.mk'_surjective N)
  have hη : Function.Surjective η := QuotientGroup.mk'_surjective _
  have hηker : η.ker = center K := QuotientGroup.ker_mk' _
  have hβker : β.ker = N := by
    ext x
    rw [MonoidHom.mem_ker, hβdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  obtain ⟨α, hα, hαs, hker⟩ := LieType.Steinberg.exists_surjective_of_isPerfect hsplit hβ hη
    hηker.le (by rw [hηker]; exact h2)
  refine ⟨α, hαs, ?_, ?_, fun s => ?_⟩
  · intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [← hβker, MonoidHom.mem_ker, ← hα, hx, map_one]
  · rw [← hηker, hker, hβker]
  · have h1 : η (α s) = e.symm (QuotientGroup.mk s) := by
      rw [hα s, hβdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply]
    rw [← MulEquiv.eq_symm_apply, ← h1]
    rfl

theorem a2l_card_map_mul_card_ker {K M : Type} [Group K] [Group M] [Finite M] (α : M →* K)
    (N : Subgroup M) (hle : α.ker ≤ N) :
    Nat.card (N.map α) * Nat.card α.ker = Nat.card N := by
  have h := Subgroup.card_ker_mul_card_range (α.domRestrict N)
  rw [MonoidHom.ker_domRestrict, MonoidHom.domRestrict_range,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at h
  rw [mul_comm]
  exact h

theorem a2l_ker_eq_bot {K M : Type} [Group K] [Group M] [Finite M] (α : M →* K) (N : Subgroup M)
    (hle : α.ker ≤ N) {m : ℕ} (hN : Nat.card N < 2 * m) (hZ : m ≤ Nat.card (N.map α)) :
    α.ker = ⊥ := by
  have h := a2l_card_map_mul_card_ker α N hle
  have hpos : 0 < Nat.card α.ker := Nat.card_pos
  have h1 : Nat.card α.ker = 1 := by
    by_contra hne
    have h2 : 2 ≤ Nat.card α.ker := by omega
    have h3 : m * 2 ≤ Nat.card (N.map α) * Nat.card α.ker := Nat.mul_le_mul hZ h2
    omega
  exact Subgroup.eq_bot_of_card_eq _ h1

end CFSG.OddStandard.SmallF3.HypA2Leaves
