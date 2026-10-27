module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidM123
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOPlusLevi
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOFourPerf
public import CFSG.Timmesfeld.Orders.ClassicalOmega
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOCoords

public section

namespace CFSG.ComponentClassification.RankTwoClassical.ORigid

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin CFSG.ABGLocalTools
open CFSG.Timmesfeld.ClassicalOrders
open CFSG.Quasithin (perfectCore)
open scoped MatrixGroups

section Form

variable {K : Type} [Field K]

theorem quadPlus_plusOe (k : ℕ) (v : Fin (k + 2) ⊕ Fin (k + 2) → K) :
    quadPlus (k + 2) K v = quadPlus k K (fun a => v (plusOe k (.inl a))) +
      StatedQuadPlus 2 K (fun b => v (plusOe k (.inr b))) := by
  rw [coe_quadPlus, coe_quadPlus]
  exact statedQuadPlus_plusOe k v

end Form

section Syl

variable (K : Type) [Field K] [CharP K 2]

@[expose] noncomputable def plusSyl : (k : ℕ) → Subgroup (GL (Fin k ⊕ Fin k) K)
  | 0 => ⊥
  | 1 => ⊥
  | k + 2 => oSylStep (plusOe k) (quadPlus k K) (plusSyl k)

variable {K}

theorem plusSyl_spec (hSL : commutator SL(2, K) = ⊤) {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    ∀ k, plusSyl K k ≤ StatedOmega (StatedQuadPlus k K) ∧ IsPGroup 2 (plusSyl K k) ∧
      Nat.card (plusSyl K k) = Nat.card K ^ (k * (k - 1))
  | 0 => ⟨bot_le, IsPGroup.of_bot, by simp [plusSyl]⟩
  | 1 => ⟨bot_le, IsPGroup.of_bot, by simp [plusSyl]⟩
  | k + 2 => by
    obtain ⟨h1, h2, h3⟩ := plusSyl_spec hSL ht0 ht1 k
    have h1' : plusSyl K k ≤ StatedOmega ⇑(quadPlus k K) := by
      rw [coe_quadPlus]
      exact h1
    have hS : plusSyl K (k + 2) = oSylStep (plusOe k) (quadPlus k K) (plusSyl K k) := rfl
    rw [hS]
    refine ⟨?_, isPGroup_oSylStep (quadPlus_plusOe k) h1' h2, ?_⟩
    · rw [← coe_quadPlus]
      exact (oSylStep_le_oXt h1').trans (oXt_le_statedOmega (quadPlus_plusOe k) hSL ht0 ht1)
    · rw [card_oSylStep (quadPlus_plusOe k) h1', h3, ← pow_add, Fintype.card_sum,
        Fintype.card_fin]
      congr 1
      rcases k with _ | k
      · rfl
      · rw [show k + 1 + 2 - 1 = k + 2 by omega, show k + 1 - 1 = k by omega]
        ring

end Syl

section Main

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem orthPlus_m123 (h4 : 4 ≤ Nat.card K) {n : ℕ} (hn : 4 ≤ n)
    {M : GL (Fin n ⊕ Fin n) K} (hMH : M ∈ StatedOmega (StatedQuadPlus n K))
    (hM2 : orderOf M = 2) (hr : commRank M = 2)
    (hsing : ∀ v,
      StatedQuadPlus n K (((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) *ᵥ v) = 0) :
    (∃ S : Subgroup (StatedProj (StatedOmega (StatedQuadPlus n K))), IsSylowOf 2 S ⊤ ∧
      S ≤ perfectCore (centralizer ({(QuotientGroup.mk ⟨M, hMH⟩ :
        StatedProj (StatedOmega (StatedQuadPlus n K)))} :
          Set (StatedProj (StatedOmega (StatedQuadPlus n K)))))) ∧
    (∀ z : StatedProj (StatedOmega (StatedQuadPlus n K)), orderOf z = 2 →
      (∃ S : Subgroup (StatedProj (StatedOmega (StatedQuadPlus n K))), IsSylowOf 2 S ⊤ ∧
        S ≤ centralizer ({z} : Set _)) →
        ∃ a : StatedProj (StatedOmega (StatedQuadPlus n K)), a * z * a⁻¹ =
          QuotientGroup.mk ⟨M, hMH⟩) ∧
    (∀ z : StatedProj (StatedOmega (StatedQuadPlus n K)), orderOf z = 2 →
      z ∈ centralizer (perfectCore (centralizer ({(QuotientGroup.mk ⟨M, hMH⟩ :
        StatedProj (StatedOmega (StatedQuadPlus n K)))} :
          Set (StatedProj (StatedOmega (StatedQuadPlus n K))))) :
            Set (StatedProj (StatedOmega (StatedQuadPlus n K)))) →
        ∃ (N : GL (Fin n ⊕ Fin n) K) (hN : N ∈ StatedOmega (StatedQuadPlus n K)),
          (QuotientGroup.mk ⟨N, hN⟩ : StatedProj (StatedOmega (StatedQuadPlus n K))) = z ∧
          ∃ a : K, (N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1 =
            a • ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have hSL : commutator SL(2, K) = ⊤ :=
    (CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K h4).commutator_eq_top
  obtain ⟨t, ht0, ht1⟩ := exists_ne_zero_ne_one h4
  obtain ⟨h1, h2, h3⟩ := plusSyl_spec hSL ht0 ht1 k
  have hperf : commutator (StatedOmega (StatedQuadPlus k K)) = ⊤ := by
    rcases (show k = 2 ∨ 3 ≤ k by omega) with rfl | hk
    · exact commutator_statedOmega_quadPlus_two h4
    · exact (isPerfect_statedOmega_quadPlus hk).commutator_eq_top
  have : Nonempty (Fin k ⊕ Fin k) := ⟨.inl ⟨0, by omega⟩⟩
  have hq : Even (Nat.card K : ℤ) := by
    have := Fintype.ofFinite K
    obtain ⟨m, -, hm⟩ := FiniteField.card K 2
    rw [Nat.card_eq_fintype_card, hm]
    push_cast
    exact (even_two).pow_of_ne_zero m.ne_zero
  have hodd : ∀ j, j ≠ 0 → Odd ((Nat.card K : ℤ) ^ j - 1) := fun j hj =>
    (hq.pow_of_ne_zero hj).sub_odd odd_one
  have hexp : (k + 2) * (k + 2 - 1) = 2 * (k + k) + 2 + k * (k - 1) := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [show j + 1 + 2 - 1 = j + 2 by omega, show j + 1 - 1 = j by omega]
    ring
  have key : OrthM123 (StatedQuadPlus (k + 2) K) M hMH :=
    orthM123_of_singular (oe := plusOe k) (coe_quadPlus _ K) (coe_quadPlus _ K)
      (nondegenerate_polarBilin_quadPlus _ K) (nondegenerate_polarBilin_quadPlus _ K)
      (statedQuadPlus_plusOe k) hSL ht0 ht1 hperf (oProj_injective_plus (by omega)) h1 h2
      (R := ((Nat.card K : ℤ) ^ (k + 2) - 1) *
        ∏ i ∈ Finset.Icc 1 (k + 2 - 1), ((Nat.card K : ℤ) ^ (2 * i) - 1))
      ((hodd _ (by omega)).mul (Finset.prod_induction _ Odd (fun _ _ ha hb => ha.mul hb)
        odd_one fun i hi => hodd _ (by rw [Finset.mem_Icc] at hi; omega)))
      (by
        rw [card_statedProj_statedOmega_quadPlus (by omega), h3, Fintype.card_sum,
          Fintype.card_fin, hexp, pow_add]
        push_cast
        ring) hMH hM2 hr hsing
  exact key

end Main

end CFSG.ComponentClassification.RankTwoClassical.ORigid
