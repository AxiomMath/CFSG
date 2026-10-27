module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidM123
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidMinusFacts
public import CFSG.Timmesfeld.Orders.ClassicalOmega
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOPlusLevi

public section

namespace CFSG.ComponentClassification.RankTwoClassical.ORigid

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin CFSG.ABGLocalTools
open CFSG.Timmesfeld.ClassicalOrders
open CFSG.Quasithin (perfectCore)
open scoped MatrixGroups

section Form

variable {K : Type} [Field K]

theorem quadMinus_minusOe (j : ℕ) (b c : K) (v : Fin (j + 2) ⊕ Fin (j + 2) ⊕ Fin 2 → K) :
    quadMinus (j + 3) K b c v = quadMinus (j + 1) K b c (fun a => v (minusOe j (.inl a))) +
      StatedQuadPlus 2 K (fun b' => v (minusOe j (.inr b'))) := by
  rw [coe_quadMinus, coe_quadMinus]
  exact statedQuadMinus_minusOe j b c v

end Form

section Syl

variable (K : Type) [Field K] [Finite K] [CharP K 2] {b c : K}
  (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

@[expose] noncomputable def minusSyl : (m : ℕ) → Subgroup (GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K)
  | 0 => ⊥
  | 1 => ⊥
  | 2 => (exists_isPGroup_statedOmega_quadMinus_two hirr).choose
  | j + 3 => oSylStep (minusOe j) (quadMinus (j + 1) K b c) (minusSyl (j + 1))

variable {K}

theorem minusSyl_spec (hSL : commutator SL(2, K) = ⊤) {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    ∀ m, minusSyl K hirr m ≤ StatedOmega (StatedQuadMinus m K b c) ∧
      IsPGroup 2 (minusSyl K hirr m) ∧ Nat.card (minusSyl K hirr m) = Nat.card K ^ (m * (m - 1))
  | 0 => ⟨bot_le, IsPGroup.of_bot, by simp [minusSyl]⟩
  | 1 => ⟨bot_le, IsPGroup.of_bot, by simp [minusSyl]⟩
  | 2 => (exists_isPGroup_statedOmega_quadMinus_two hirr).choose_spec
  | j + 3 => by
    obtain ⟨h1, h2, h3⟩ := minusSyl_spec hSL ht0 ht1 (j + 1)
    have h1' : minusSyl K hirr (j + 1) ≤ StatedOmega ⇑(quadMinus (j + 1) K b c) := by
      rw [coe_quadMinus]
      exact h1
    have hS : minusSyl K hirr (j + 3) =
        oSylStep (minusOe j) (quadMinus (j + 1) K b c) (minusSyl K hirr (j + 1)) := rfl
    rw [hS]
    refine ⟨?_, isPGroup_oSylStep (quadMinus_minusOe j b c) h1' h2, ?_⟩
    · rw [← coe_quadMinus]
      exact (oSylStep_le_oXt h1').trans (oXt_le_statedOmega (quadMinus_minusOe j b c) hSL ht0 ht1)
    · refine (card_oSylStep (quadMinus_minusOe j b c) h1').trans ?_
      rw [h3, ← pow_add, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
      congr 1
      rw [show j + 3 - 1 = j + 2 by omega, show j + 1 - 1 = j by omega]
      ring

end Syl

section Main

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem orthMinus_m123 (h4 : 4 ≤ Nat.card K) {n : ℕ} (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {M : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K}
    (hMH : M ∈ StatedOmega (StatedQuadMinus n K b c)) (hM2 : orderOf M = 2)
    (hr : commRank M = 2)
    (hsing : ∀ v, StatedQuadMinus n K b c
      (((M : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K) -
        1) *ᵥ v) = 0) :
    OrthM123 (StatedQuadMinus n K b c) M hMH := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 3 := ⟨n - 3, by omega⟩
  have hSL : commutator SL(2, K) = ⊤ :=
    (CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K h4).commutator_eq_top
  obtain ⟨t, ht0, ht1⟩ := exists_ne_zero_ne_one h4
  obtain ⟨h1, h2, h3⟩ := minusSyl_spec hirr hSL ht0 ht1 (j + 1)
  have hperf : commutator (StatedOmega (StatedQuadMinus (j + 1) K b c)) = ⊤ :=
    commutator_statedOmega_quadMinus_eq_top (by omega) hirr
  have : Nonempty (Fin j ⊕ Fin j ⊕ Fin 2) := ⟨.inr (.inr 0)⟩
  have hq : Even (Nat.card K : ℤ) := by
    have := Fintype.ofFinite K
    obtain ⟨m, -, hm⟩ := FiniteField.card K 2
    rw [Nat.card_eq_fintype_card, hm]
    push_cast
    exact (even_two).pow_of_ne_zero m.ne_zero
  have hodd : ∀ i, i ≠ 0 → Odd ((Nat.card K : ℤ) ^ i - 1) := fun i hi =>
    (hq.pow_of_ne_zero hi).sub_odd odd_one
  have hodd' : Odd ((Nat.card K : ℤ) ^ (j + 3) + 1) :=
    (hq.pow_of_ne_zero (by omega)).add_odd odd_one
  have hexp : (j + 3) * (j + 3 - 1) = 2 * (j + j + 2) + 2 + (j + 1) * (j + 1 - 1) := by
    rw [show j + 3 - 1 = j + 2 by omega, show j + 1 - 1 = j by omega]
    ring
  have hR : Odd (((Nat.card K : ℤ) ^ (j + 3) + 1) *
      ∏ i ∈ Finset.Icc 1 (j + 3 - 1), ((Nat.card K : ℤ) ^ (2 * i) - 1)) :=
    hodd'.mul (Finset.prod_induction _ Odd (fun _ _ ha hb => ha.mul hb)
      odd_one fun i hi => hodd _ (by rw [Finset.mem_Icc] at hi; omega))
  have hcard : (Nat.card (StatedProj (StatedOmega (StatedQuadMinus (j + 3) K b c))) : ℤ) =
      (Nat.card K : ℤ) ^ (2 * Fintype.card (Fin j ⊕ Fin j ⊕ Fin 2) + 2) *
        Nat.card (minusSyl K hirr (j + 1)) *
        (((Nat.card K : ℤ) ^ (j + 3) + 1) *
          ∏ i ∈ Finset.Icc 1 (j + 3 - 1), ((Nat.card K : ℤ) ^ (2 * i) - 1)) := by
    rw [card_statedProj_statedOmega_quadMinus (by omega) hirr, h3, Fintype.card_sum,
      Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, hexp, pow_add]
    push_cast
    ring
  exact orthM123_of_singular (oe := minusOe j) (coe_quadMinus (j + 3) K b c)
    (coe_quadMinus (j + 1) K b c) (nondegenerate_polarBilin_quadMinus_of_finite (j + 3) K hirr)
    (nondegenerate_polarBilin_quadMinus_of_finite (j + 1) K hirr)
    (statedQuadMinus_minusOe j b c) hSL ht0 ht1 hperf (oProj_injective_minus (j + 3) b c) h1 h2
    hR hcard hMH hM2 hr hsing

end Main

end CFSG.ComponentClassification.RankTwoClassical.ORigid
