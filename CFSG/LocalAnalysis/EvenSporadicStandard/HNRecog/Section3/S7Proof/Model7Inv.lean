module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Shapes

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private lemma s7_inv_conj_cancel {G : Type*} [Group G] (g : G) {x y : G}
    (h : g * x * g⁻¹ = g * y * g⁻¹) : x = y :=
  mul_left_cancel (mul_right_cancel h)

private lemma s7_inv_conj_mul {G : Type*} [Group G] (g x y : G) :
    g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by
  group

theorem s7_sym7_cycleType_two :
    (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 2 3).cycleType = {2, 2} :=
  Equiv.Perm.cycleType_swap_mul_swap_of_nodup (by decide)

theorem s7_sym7_cycleType_three :
    (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 2 3 * Equiv.swap 4 5).cycleType = {2, 2, 2} := by
  have hd : Equiv.Perm.Disjoint (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 2 3)
      (Equiv.swap 4 5) :=
    (Equiv.Perm.disjoint_swap_swap (by decide : [(0 : Fin 7), 1, 4, 5].Nodup)).mul_left
      (Equiv.Perm.disjoint_swap_swap (by decide : [(2 : Fin 7), 3, 4, 5].Nodup))
  rw [Equiv.Perm.Disjoint.cycleType_mul hd, s7_sym7_cycleType_two,
    Equiv.Perm.isSwap_iff_cycleType.mp
      (Equiv.Perm.swap_isSwap_iff.mpr (by decide : (4 : Fin 7) ≠ 5))]
  decide

theorem s7_sym7_involution (σ : Sym 7) (h2 : σ ^ 2 = 1) (h1 : σ ≠ 1) :
    σ.cycleType = {2} ∨
    (σ.cycleType = {2, 2} ∧ ∃ τ₁ τ₂ : Sym 7, τ₁.IsSwap ∧ τ₂.IsSwap ∧ τ₁ ≠ τ₂ ∧
      τ₁ * τ₂ = τ₂ * τ₁ ∧ σ = τ₁ * τ₂) ∨
    (σ.cycleType = {2, 2, 2} ∧ ∃ τ₁ τ₂ τ₃ : Sym 7, τ₁.IsSwap ∧ τ₂.IsSwap ∧ τ₃.IsSwap ∧
      τ₁ ≠ τ₂ ∧ τ₃ ≠ τ₁ ∧ τ₃ ≠ τ₂ ∧ τ₃ ≠ τ₁ * τ₂ ∧ τ₁ * τ₂ = τ₂ * τ₁ ∧
      τ₁ * τ₃ = τ₃ * τ₁ ∧ τ₂ * τ₃ = τ₃ * τ₂ ∧ σ = τ₁ * τ₂ * τ₃) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hct : σ.cycleType = Multiset.replicate σ.cycleType.card 2 :=
    Equiv.Perm.cycleType_of_pow_prime_eq_one h2
  have hpos : 0 < σ.cycleType.card := Equiv.Perm.card_cycleType_pos.mpr h1
  have hle : σ.cycleType.card * 2 ≤ 7 := by
    have h := σ.sum_cycleType_le
    rw [hct, Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin] at h
    exact h
  have hcases : σ.cycleType.card = 1 ∨ σ.cycleType.card = 2 ∨ σ.cycleType.card = 3 := by omega
  rcases hcases with hk | hk | hk
  · left
    rw [hct, hk]
    decide
  · right; left
    have hσc : σ.cycleType = {2, 2} := by rw [hct, hk]; decide
    refine ⟨hσc, ?_⟩
    have hconj : IsConj (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 2 3) σ :=
      Equiv.Perm.isConj_iff_cycleType_eq.mpr (s7_sym7_cycleType_two.trans hσc.symm)
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    have hτ1 : Equiv.swap (g 0) (g 1) = g * Equiv.swap (0 : Fin 7) 1 * g⁻¹ :=
      Equiv.swap_apply_apply g 0 1
    have hτ2 : Equiv.swap (g 2) (g 3) = g * Equiv.swap 2 3 * g⁻¹ :=
      Equiv.swap_apply_apply g 2 3
    have hbase_ne : Equiv.swap (0 : Fin 7) 1 ≠ Equiv.swap 2 3 := by decide
    have hbase_comm : Equiv.swap (0 : Fin 7) 1 * Equiv.swap 2 3 =
        Equiv.swap 2 3 * Equiv.swap (0 : Fin 7) 1 := by decide
    refine ⟨Equiv.swap (g 0) (g 1), Equiv.swap (g 2) (g 3),
      Equiv.Perm.swap_isSwap_iff.mpr (g.injective.ne (by decide : (0 : Fin 7) ≠ 1)),
      Equiv.Perm.swap_isSwap_iff.mpr (g.injective.ne (by decide : (2 : Fin 7) ≠ 3)),
      ?_, ?_, ?_⟩
    · intro heq
      rw [hτ1, hτ2] at heq
      exact hbase_ne (s7_inv_conj_cancel g heq)
    · rw [hτ1, hτ2, ← s7_inv_conj_mul, ← s7_inv_conj_mul, hbase_comm]
    · rw [hτ1, hτ2]
      exact hg.symm.trans (s7_inv_conj_mul g (Equiv.swap (0 : Fin 7) 1) (Equiv.swap 2 3))
  · right; right
    have hσc : σ.cycleType = {2, 2, 2} := by rw [hct, hk]; decide
    refine ⟨hσc, ?_⟩
    have hconj : IsConj (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 2 3 * Equiv.swap 4 5) σ :=
      Equiv.Perm.isConj_iff_cycleType_eq.mpr (s7_sym7_cycleType_three.trans hσc.symm)
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    have hτ1 : Equiv.swap (g 0) (g 1) = g * Equiv.swap (0 : Fin 7) 1 * g⁻¹ :=
      Equiv.swap_apply_apply g 0 1
    have hτ2 : Equiv.swap (g 2) (g 3) = g * Equiv.swap 2 3 * g⁻¹ :=
      Equiv.swap_apply_apply g 2 3
    have hτ3 : Equiv.swap (g 4) (g 5) = g * Equiv.swap 4 5 * g⁻¹ :=
      Equiv.swap_apply_apply g 4 5
    have hb12 : Equiv.swap (0 : Fin 7) 1 ≠ Equiv.swap 2 3 := by decide
    have hb31 : Equiv.swap 4 5 ≠ Equiv.swap (0 : Fin 7) 1 := by decide
    have hb32 : Equiv.swap (4 : Fin 7) 5 ≠ Equiv.swap (2 : Fin 7) 3 := by decide
    have hb312 : Equiv.swap 4 5 ≠ Equiv.swap (0 : Fin 7) 1 * Equiv.swap 2 3 := by decide
    have hc12 : Equiv.swap (0 : Fin 7) 1 * Equiv.swap 2 3 =
        Equiv.swap 2 3 * Equiv.swap (0 : Fin 7) 1 := by decide
    have hc13 : Equiv.swap (0 : Fin 7) 1 * Equiv.swap 4 5 =
        Equiv.swap 4 5 * Equiv.swap (0 : Fin 7) 1 := by decide
    have hc23 : Equiv.swap (2 : Fin 7) 3 * Equiv.swap (4 : Fin 7) 5 =
        Equiv.swap (4 : Fin 7) 5 * Equiv.swap (2 : Fin 7) 3 := by decide
    refine ⟨Equiv.swap (g 0) (g 1), Equiv.swap (g 2) (g 3), Equiv.swap (g 4) (g 5),
      Equiv.Perm.swap_isSwap_iff.mpr (g.injective.ne (by decide : (0 : Fin 7) ≠ 1)),
      Equiv.Perm.swap_isSwap_iff.mpr (g.injective.ne (by decide : (2 : Fin 7) ≠ 3)),
      Equiv.Perm.swap_isSwap_iff.mpr (g.injective.ne (by decide : (4 : Fin 7) ≠ 5)),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro heq
      rw [hτ1, hτ2] at heq
      exact hb12 (s7_inv_conj_cancel g heq)
    · intro heq
      rw [hτ3, hτ1] at heq
      exact hb31 (s7_inv_conj_cancel g heq)
    · intro heq
      rw [hτ3, hτ2] at heq
      exact hb32 (s7_inv_conj_cancel g heq)
    · intro heq
      rw [hτ3, hτ1, hτ2, ← s7_inv_conj_mul] at heq
      exact hb312 (s7_inv_conj_cancel g heq)
    · rw [hτ1, hτ2, ← s7_inv_conj_mul, ← s7_inv_conj_mul, hc12]
    · rw [hτ1, hτ3, ← s7_inv_conj_mul, ← s7_inv_conj_mul, hc13]
    · rw [hτ2, hτ3, ← s7_inv_conj_mul, ← s7_inv_conj_mul, hc23]
    · rw [hτ1, hτ2, hτ3, ← s7_inv_conj_mul]
      exact hg.symm.trans
        (s7_inv_conj_mul g (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 2 3) (Equiv.swap 4 5))

theorem s7_sym7_swaps : ∃ τ₁ τ₂ τ₃ : Sym 7, τ₁.IsSwap ∧ τ₂.IsSwap ∧ τ₃.IsSwap ∧ τ₁ ≠ τ₂ ∧
    τ₃ ≠ τ₁ ∧ τ₃ ≠ τ₂ ∧ τ₃ ≠ τ₁ * τ₂ ∧ τ₁ * τ₂ = τ₂ * τ₁ ∧ τ₁ * τ₃ = τ₃ * τ₁ ∧
    τ₂ * τ₃ = τ₃ * τ₂ := by
  refine ⟨Equiv.swap (0 : Fin 7) 1, Equiv.swap 2 3, Equiv.swap 4 5,
    Equiv.Perm.swap_isSwap_iff.mpr (by decide : (0 : Fin 7) ≠ 1),
    Equiv.Perm.swap_isSwap_iff.mpr (by decide : (2 : Fin 7) ≠ 3),
    Equiv.Perm.swap_isSwap_iff.mpr (by decide : (4 : Fin 7) ≠ 5),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals decide

end CFSG.EvenSporadicStandard.HNRecog.Section3
