module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSpYFour
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofSymplecticLevi
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSpYDefs
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix Subgroup CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

section Choice

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

theorem minFac_dvd_card_SL {K : Type} [Field K] [Finite K] {f : ℕ} (hK : Nat.card K = 2 ^ f) :
    Nat.minFac (2 ^ f + 1) ∣ Nat.card SL(2, K) := by
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK]
  refine (Nat.minFac_dvd _).trans (Dvd.dvd.mul_left ?_ _)
  rw [show (2 ^ f) ^ 2 - 1 = (2 ^ f) ^ 2 - 1 ^ 2 by rw [one_pow], Nat.sq_sub_sq]
  exact Dvd.intro _ rfl

theorem minFac_ne_two {f : ℕ} (hf : 1 ≤ f) : Nat.minFac (2 ^ f + 1) ≠ 2 := by
  intro h
  have h2 : 2 ∣ 2 ^ f + 1 := by
    have := Nat.minFac_dvd (2 ^ f + 1)
    rwa [h] at this
  have h3 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
  omega

theorem symplecticYChoice : SymplecticYChoice := by
  intro G _ _ A D hD hA hZ hq p hp
  cases D with
  | symplectic n f hn hf hnf K hK e =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hf2 : 2 ≤ f := by
      have hq' : 2 ^ 2 ≤ 2 ^ f := hq
      exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hq'
    have hm : 1 ≤ m := by omega
    have : CharP K 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have := Fintype.ofFinite K
      exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
    have h4 : ∃ s : Finset K, s.card = 4 := by
      have : Fintype K := Fintype.ofFinite K
      obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
        (by
          rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hK]
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2)
      exact ⟨s, hs⟩
    have hp' : IsInvolutionOfRank e p 1 := hp
    obtain ⟨θ, hker, hθ, hα⟩ := exists_spLeviTheta hm e hp'
    have hW : LeviChoice (.symplectic (m + 1) f hn hf hnf K hK e) p (spLeviW θ) (spLeviW θ) := by
      refine leviChoice_symplectic_of hn hf hnf hK e hZ hf2 hker hθ hα le_rfl
        (levLift_le_liftSub.trans (liftSub_mono spBarW_le_centralizer_spBarL))
        (noInv_sp hA.1 hker hθ h4 hm) ?_ ?_
      · intro h σ hσ hfix
        have h' : m + 1 = 2 ∧ f = 2 := h
        obtain rfl : m = 1 := by omega
        have hK4 : Nat.card K = 4 := by rw [hK, h'.2]; norm_num
        exact outerFree_sp_four hK4 hker hθ h4 σ hσ hfix
      · intro h
        have h' : m + 1 = 2 ∧ f = 2 := h
        obtain rfl : m = 1 := by omega
        have hK4 : Nat.card K = 4 := by rw [hK, h'.2]; norm_num
        exact sym_sp_four hA.1 hker hθ hZ hK4 h4
    have hLY : spLeviL θ ≤ A ⊓ centralizer (spLeviW θ : Set G) :=
      le_inf levLift_le (levLift_le_centralizer_levLift hker fun _ hs _ hs' =>
        (spBarW_commute_spBarL hs' hs).symm)
    have hlayer : AS76b.layerCentralizer A (spLeviW θ) = spLeviL θ :=
      layerCentralizer_eq_spLeviL hker hθ h4 hm le_rfl hLY
    have hr : Fact (Nat.minFac (2 ^ f + 1)).Prime :=
      ⟨Nat.minFac_prime (by have := Nat.one_le_two_pow (n := f); omega)⟩
    have hr2 := minFac_ne_two (by omega : 1 ≤ f)
    have hodd : ∀ {r : ℕ}, r.Prime → r ≠ 2 → ∀ {z : G}, orderOf z = r →
        Odd (orderOf z) ∧ z ≠ 1 := @fun r hrp hr2' z hz =>
      ⟨hz ▸ hrp.odd_of_ne_two hr2', fun h1 => by
        rw [h1, orderOf_one] at hz
        exact hrp.one_lt.ne hz⟩
    obtain ⟨X, y, hyA, hyW, hyθ, hyr, hXr, hX⟩ :=
      exists_mem_spLeviW_orderOf hker hθ h4 hZ hf2 hK _ hr2 (minFac_dvd_card_SL hK)
    have hy : LeviOddElt A (spLeviW θ) (AS76b.layerCentralizer A (spLeviW θ)) y := by
      rw [hlayer]
      exact ⟨hyW, (hodd hr.out hr2 hyr).1, (hodd hr.out hr2 hyr).2,
        layerCentralizer_zpowers_eq_spLeviL hker hθ h4 hm hX hyW hyA hyθ,
        noInv_spY hA.1 hker hθ h4 hm hX hyA hyθ⟩
    refine ⟨spLeviW θ, y, hW, hy, fun hfour => ?_⟩
    have h' : m + 1 = 2 ∧ f = 2 := hfour
    obtain rfl : m = 1 := by omega
    obtain rfl : f = 2 := h'.2
    have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
    have hr5 : Nat.minFac (2 ^ 2 + 1) = 5 := by norm_num
    have hX5 : orderOf X = 5 := hXr.trans hr5
    obtain ⟨X₃, y₃, hy₃A, hy₃W, hy₃θ, hy₃r, -, hX₃⟩ :=
      exists_mem_spLeviW_orderOf (r := 3) (hr := ⟨Nat.prime_three⟩) hker hθ h4 hZ hf2 hK
        (by norm_num)
        (by rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK4]; norm_num)
    refine ⟨hyr.trans hr5, ?_, ?_, y₃, ?_, hy₃r⟩
    · rw [hlayer]
      exact outerFree_spY_four hK4 hker hθ h4 hX5 hyA hyθ
    · rw [hlayer]
      exact noThree_spY_four hK4 hA.1 hker hθ h4 hX5 hyA hyθ
    · rw [hlayer]
      exact ⟨hy₃W, (hodd Nat.prime_three (by norm_num) hy₃r).1,
        (hodd Nat.prime_three (by norm_num) hy₃r).2,
        layerCentralizer_zpowers_eq_spLeviL hker hθ h4 le_rfl hX₃ hy₃W hy₃A hy₃θ,
        noInv_spY hA.1 hker hθ h4 le_rfl hX₃ hy₃A hy₃θ⟩
  | linear => simp [ClassicalModel.family] at hD
  | unitary => simp [ClassicalModel.family] at hD
  | orthPlus => simp [ClassicalModel.family] at hD
  | orthMinus => simp [ClassicalModel.family] at hD

end Choice

end CFSG.ComponentClassification.RankTwoClassical
