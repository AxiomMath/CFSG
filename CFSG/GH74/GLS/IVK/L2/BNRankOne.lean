module

public import CFSG.GH74.BNPair.Defs

public section

namespace CFSG.GH74.GLS.IVK.L2BN

open CFSG.GH74.BNPair
open scoped Pointwise

variable {X : Type*} [Group X]

theorem mk_eq_one_iff_mem (B N : Subgroup X) [(cartan B N).Normal] (n : N) :
    (n : WeylGroup B N) = 1 ↔ (n : X) ∈ B := by
  rw [QuotientGroup.eq_one_iff]
  simp [cartan, Subgroup.mem_subgroupOf]

theorem isTitsSystem_of_rankOne (B N : Subgroup X) [(cartan B N).Normal] (w : N)
    (hwB : (w : X) ∉ B) (hw2 : (w : X) ^ 2 ∈ B)
    (hcases : ∀ n : N, (n : X) ∈ B ∨ (n : X) * (w : X)⁻¹ ∈ B)
    (hbruhat : ∀ x : X, x ∈ B ∨ x ∈ (B : Set X) * {(w : X)} * (B : Set X))
    (hne : ∀ n : N, (n : X) ∉ B → ∃ b ∈ B, (n : X) * b * (n : X) ∉ B) :
    IsTitsSystem B N {(w : WeylGroup B N)} := by
  have hw1 : (w : WeylGroup B N) ≠ 1 := fun h => hwB ((mk_eq_one_iff_mem B N w).1 h)
  have hw2' : (w : WeylGroup B N) ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow, mk_eq_one_iff_mem]
    simpa using hw2
  have key : ∀ x : WeylGroup B N, x = 1 ∨ x = (w : WeylGroup B N) := by
    intro x
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective x
    rcases hcases n with h | h
    · exact Or.inl ((mk_eq_one_iff_mem B N n).2 h)
    · right
      have : ((n * w⁻¹ : N) : WeylGroup B N) = 1 :=
        (mk_eq_one_iff_mem B N _).2 (by simpa using h)
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, mul_inv_eq_one] at this
      exact this
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [eq_top_iff]
    intro x _
    rcases hbruhat x with h | ⟨_, ⟨b₁, hb₁, y, hy, rfl⟩, b₂, hb₂, rfl⟩
    · exact Subgroup.mem_sup_left h
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact mul_mem (mul_mem (Subgroup.mem_sup_left hb₁) (Subgroup.mem_sup_right w.2))
        (Subgroup.mem_sup_left hb₂)
  · intro s hs
    rw [Finset.mem_singleton] at hs
    subst hs
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime hw2' hw1
  · rw [eq_top_iff]
    intro x _
    rcases key x with rfl | rfl
    · exact one_mem _
    · exact Subgroup.subset_closure (by simp)
  · intro n m hn x hx
    rw [Finset.mem_singleton] at hn
    obtain ⟨_, ⟨_, rfl, b, hb, rfl⟩, _, rfl, rfl⟩ := hx
    rcases key (m : WeylGroup B N) with hm | hm
    · left
      refine ⟨n, by rw [hm, mul_one], ?_⟩
      have hmB : (m : X) ∈ B := (mk_eq_one_iff_mem B N m).1 hm
      exact ⟨(1 : X) * n, ⟨1, B.one_mem, n, rfl, rfl⟩, b * m, B.mul_mem hb hmB, by group⟩
    · rcases hbruhat ((n : X) * b * m) with h | ⟨_, ⟨b₁, hb₁, y, hy, rfl⟩, b₂, hb₂, h⟩
      · left
        refine ⟨1, ?_, ?_⟩
        · rw [hn, hm, ← pow_two, hw2']
          rfl
        · exact ⟨(n : X) * b * m * 1, ⟨(n : X) * b * m, h, 1, rfl, rfl⟩, 1, B.one_mem, by simp⟩
      · right
        refine ⟨w, hm.symm, ?_⟩
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact ⟨b₁ * w, ⟨b₁, hb₁, w, rfl, rfl⟩, b₂, hb₂, h⟩
  · intro n hn heq
    rw [Finset.mem_singleton] at hn
    have hnB : (n : X) ∉ B := fun h => hw1 (hn ▸ (mk_eq_one_iff_mem B N n).2 h)
    obtain ⟨b, hb, hnb⟩ := hne n hnB
    apply hnb
    rw [← SetLike.mem_coe, ← heq]
    exact ⟨_, ⟨n, rfl, b, hb, rfl⟩, n, rfl, rfl⟩

end CFSG.GH74.GLS.IVK.L2BN
