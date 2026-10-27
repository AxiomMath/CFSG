module

public import CFSG.HardMathSupport.Cooperstein.Proving.OddGen
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks
public import CFSG.HardMathSupport.Cooperstein.Proving.OddK1

public section

namespace CFSG.HardMathSupport.Cooperstein.Proving.OddShort

open Subgroup

variable {G : Type} [Group G]

theorem closure_odd_normal {B : Subgroup G} :
    ((Subgroup.closure {x : G | x ∈ B ∧ Odd (orderOf x)}).subgroupOf B).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  simpa using OddGen.odd_closure_conj g.2 hn

theorem pow_two_pow_mem_closure [Finite G] {B : Subgroup G} {b : G} (hb : b ∈ B) :
    ∃ k : ℕ, b ^ 2 ^ k ∈ Subgroup.closure {x : G | x ∈ B ∧ Odd (orderOf x)} := by
  have hpos : orderOf b ≠ 0 := (orderOf_pos b).ne'
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd hpos
  refine ⟨k, Subgroup.subset_closure ⟨B.pow_mem hb _, ?_⟩⟩
  have hc : (b ^ 2 ^ k) ^ m = 1 := by
    rw [← pow_mul, ← hkm, pow_orderOf_eq_one]
  exact Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one hc)

theorem closure_odd_eq_of_no_two_quotient [Finite G] {B : Subgroup G}
    (hsh : ∀ (N : Subgroup B) [N.Normal], IsPGroup 2 (B ⧸ N) → N = ⊤) :
    Subgroup.closure {x : G | x ∈ B ∧ Odd (orderOf x)} = B := by
  set H := Subgroup.closure {x : G | x ∈ B ∧ Odd (orderOf x)} with hH
  have hHB : H ≤ B := (Subgroup.closure_le B).2 fun x hx => hx.1
  have : (H.subgroupOf B).Normal := closure_odd_normal
  have hp : IsPGroup 2 (B ⧸ H.subgroupOf B) := by
    intro g
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨k, hk⟩ := pow_two_pow_mem_closure (B := B) b.2
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa using hk
  have htop : H.subgroupOf B = ⊤ := hsh (H.subgroupOf B) hp
  apply le_antisymm hHB
  intro b hb
  have hmem : (⟨b, hb⟩ : B) ∈ H.subgroupOf B := by
    rw [htop]
    exact Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.1 hmem

theorem closure_odd_eq_of_isShort2 [Finite G] {B : Subgroup G}
    (h : CFSG.QuasithinUnique.IsShort2 B) :
    Subgroup.closure {x : G | x ∈ B ∧ Odd (orderOf x)} = B :=
  closure_odd_eq_of_no_two_quotient h.1

theorem eq_bot_of_K1_short [Finite G] {X B Y : Subgroup G}
    (hX : CFSG.QuasithinUnique.CharTwo X) (hBX : B ≤ X)
    (hYX : Y ≤ X) (hBY : B ≤ Y) (hQY : CFSG.Open.pCoreOf 2 X ≤ Y)
    (hY : ∀ p ∈ Y, ∃ b ∈ B, ∃ q ∈ CFSG.Open.pCoreOf 2 X, p = b * q)
    (hBQ : B ⊓ CFSG.Open.pCoreOf 2 X = ⊥)
    (hsh : CFSG.QuasithinUnique.IsShort2 B)
    (hch : Relation.ReflTransGen (fun H K : Subgroup G => H ≤ K ∧ (H.subgroupOf K).Normal) B Y) :
    B = ⊥ :=
  K1.eq_bot_of_K1 hX hBX hYX hBY hQY hY hBQ (closure_odd_eq_of_isShort2 hsh) hch

end CFSG.HardMathSupport.Cooperstein.Proving.OddShort

end
