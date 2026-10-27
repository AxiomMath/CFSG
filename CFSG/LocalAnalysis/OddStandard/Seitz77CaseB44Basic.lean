module

public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB43Main

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.OddStandard.Seitz77.CaseB45
  CFSG.LocalAnalysis.ComponentInitial.FieldFourCover
open scoped commutatorElement

theorem eq_cs_of_swap {G : Type*} [Group G] {H K : Subgroup G} {t : G} (ht : t * t = 1)
    (h₁ : ∀ x ∈ H, t * x * t⁻¹ ∈ K) (h₂ : ∀ x ∈ K, t * x * t⁻¹ ∈ H) : K = cs t H := by
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  refine le_antisymm (fun y hy => ?_) (fun y hy => ?_)
  · rw [mem_cs, ht']
    have := h₂ y hy
    rwa [ht'] at this
  · rw [mem_cs, ht'] at hy
    have := h₁ _ hy
    have e : t * (t * y * t) * t⁻¹ = y := by
      calc t * (t * y * t) * t⁻¹ = (t * t) * y * (t * t⁻¹) := by group
        _ = y := by rw [ht]; group
    rwa [e] at this

section CS

variable {G : Type} [Group G] [Finite G] {A V₁ V₂ : Subgroup G} {d : Datum A}
  {c₁ : CaseB A V₁ d.t} {c₂ : CaseB A V₂ d.t} {M₁ M₂ N₁ N₂ S A₁ B₁ : Subgroup G} {k : Type}
  [Field k] {e : ↥A₁ ≃* ↥(unipAll k)} (CS : CommonSylow c₁ c₂ M₁ M₂ N₁ N₂ S A₁ B₁ e)

include CS

theorem CommonSylow.swapPair : SwapPair A₁ B₁ d.t := CS.syl.swapPair

theorem CommonSylow.S_eq : S = A₁ ⊔ B₁ := CS.syl.prod

theorem CommonSylow.A₁_le_M₁ : A₁ ≤ M₁ := by
  rw [CS.syl.A₁_eq]; exact inf_le_right

theorem CommonSylow.B₁_le_M₂ : B₁ ≤ M₂ := by
  rw [CS.syl.B₁_eq]; exact inf_le_right

theorem CommonSylow.A₁_le_N₁ : A₁ ≤ N₁ := by
  rw [← CS.A_eq]; exact inf_le_right

theorem CommonSylow.B₁_le_N₂ : B₁ ≤ N₂ := by
  rw [← CS.B_eq]; exact inf_le_right

theorem CommonSylow.A₁_le_S : A₁ ≤ S := by rw [CS.S_eq]; exact le_sup_left

theorem CommonSylow.M₂_eq : M₂ = cs d.t M₁ :=
  eq_cs_of_swap c₁.t_mul_self CS.F₁.swap₁ CS.F₁.swap₂

theorem CommonSylow.N₂_eq : N₂ = cs d.t N₁ :=
  eq_cs_of_swap c₂.t_mul_self CS.F₂.swap₁ CS.F₂.swap₂

theorem CommonSylow.ninf₁ : c₁.Ninf = M₁ ⊔ M₂ := CS.F₁.ninf_eq

theorem CommonSylow.ninf₂ : c₂.Ninf = N₁ ⊔ N₂ := CS.F₂.ninf_eq

theorem CommonSylow.card_S : Nat.card S = 2 ^ 12 := by
  have P := CS.swapPair
  have e1 := supEquivProd A₁ B₁ P.comm (disjoint_iff.mpr P.inf_eq)
  have hA : Nat.card ↥A₁ = 64 := by
    rw [Nat.card_congr e.toEquiv, card_unipAll, CS.syl.card_k]; norm_num
  have hB : Nat.card ↥B₁ = 64 := by
    rw [P.B_eq, nat_card_cs, hA]
  rw [CS.S_eq, Nat.card_congr e1.toEquiv, Nat.card_prod, hA, hB]
  norm_num

theorem CommonSylow.W₁_le_S : c₁.W ≤ S := CS.syl.W_le

theorem CommonSylow.W₂_le_S : c₂.W ≤ S := by
  rw [CS.W₂_eq, CS.S_eq]
  exact sup_le_sup radIn_le (CS.swapPair.cs_le radIn_le)

theorem CommonSylow.W_sup : c₁.W ⊔ c₂.W = S := by
  rw [CS.W₁_eq, CS.W₂_eq, CS.syl.S_eq_sup]

end CS

end CFSG.OddStandard.Seitz77
