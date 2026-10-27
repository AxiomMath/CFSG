module

public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Combinatorics.SimpleGraph.Init
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.QuasithinUnique

open MulAction Equiv Equiv.Perm
open scoped Pointwise

namespace SteinbergCH

theorem coe_sup_eq_mul_of_mul_comm {G : Type*} [Group G] (H K : Subgroup G)
    (h : (H : Set G) * K = K * H) : ((H ⊔ K : Subgroup G) : Set G) = H * K := by
  let T : Subgroup G :=
    { carrier := (H : Set G) * K
      one_mem' := ⟨1, H.one_mem, 1, K.one_mem, one_mul 1⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨c, hc, d, hd, rfl⟩
        have hbc : b * c ∈ (K : Set G) * H := ⟨b, hb, c, hc, rfl⟩
        rw [← h] at hbc
        obtain ⟨c', hc', b', hb', hcb⟩ := hbc
        have hcb : c' * b' = b * c := hcb
        refine ⟨a * c', H.mul_mem ha hc', b' * d, K.mul_mem hb' hd, ?_⟩
        calc a * c' * (b' * d) = a * (c' * b') * d := by group
          _ = a * (b * c) * d := by rw [hcb]
          _ = a * b * (c * d) := by group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        have hba : b⁻¹ * a⁻¹ ∈ (K : Set G) * H := ⟨b⁻¹, K.inv_mem hb, a⁻¹, H.inv_mem ha, rfl⟩
        rw [← h] at hba
        rw [mul_inv_rev]
        exact hba }
  have hT : H ⊔ K = T := le_antisymm
    (sup_le (fun x hx => ⟨x, hx, 1, K.one_mem, mul_one x⟩)
      (fun x hx => ⟨1, H.one_mem, x, hx, one_mul x⟩))
    (fun x ⟨a, ha, b, hb, hab⟩ => hab ▸ Subgroup.mul_mem_sup ha hb)
  rw [hT]
  rfl

theorem no_index_five_of_simple {G : Type*} [Group G] [IsSimpleGroup G]
    (hG : Nat.card G = 360) (H : Subgroup G) (hH : Nat.card H = 72) : False := by
  have hidx : H.index = 5 := by
    have := H.card_mul_index
    rw [hH, hG] at this
    omega
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H.normalCore with h | h
  · have := H.index_normalCore_le_factorial_index
    rw [h, Subgroup.index_bot, hG, hidx] at this
    norm_num [Nat.factorial] at this
  · have hH' : H = ⊤ := top_le_iff.mp (h ▸ H.normalCore_le)
    rw [hH', Subgroup.index_top] at hidx
    omega

variable {S X : Type*} [Group S] [MulAction S X]

end SteinbergCH

open SteinbergCH

end CFSG.QuasithinUnique
