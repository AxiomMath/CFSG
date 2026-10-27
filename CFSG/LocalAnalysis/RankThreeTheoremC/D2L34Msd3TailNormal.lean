module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup

theorem isPGroup_three_of_nilpotent_normal {X : Type*} [Group X] [Finite X]
    (h1 : ∀ K : Subgroup X, K.Normal → Nat.Coprime 3 (Nat.card K) → K = ⊥)
    (Y : Subgroup X) [Y.Normal] [Group.IsNilpotent Y] : IsPGroup 3 Y := by
  have hpr : ∀ r : ℕ, r.Prime → r ∣ Nat.card Y → r = 3 := by
    intro r hr hrY
    by_contra hr3
    have : Fact r.Prime := ⟨hr⟩
    obtain ⟨R⟩ : Nonempty (Sylow r Y) := inferInstance
    have hRc : R.Characteristic := Sylow.characteristic_of_normal R inferInstance
    have hKn : (R.toSubgroup.map Y.subtype).Normal := inferInstance
    have hcop : Nat.Coprime 3 (Nat.card (R.toSubgroup.map Y.subtype)) := by
      rw [Subgroup.card_subtype]
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp R.isPGroup'
      rw [hn]
      exact Nat.Coprime.pow_right n ((Nat.coprime_primes Nat.prime_three hr).mpr (Ne.symm hr3))
    have hbot := h1 _ hKn hcop
    exact R.ne_bot_of_dvd_card hrY
      ((Subgroup.map_eq_bot_iff_of_injective _ Y.subtype_injective).mp hbot)
  exact IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
    (fun hd hdvd => hpr _ hd hdvd))

theorem normal_of_abelian_maximal_of_normal {X : Type*} [Group X] [Finite X]
    (h1 : ∀ K : Subgroup X, K.Normal → Nat.Coprime 3 (Nat.card K) → K = ⊥)
    {Q : Subgroup X} (hQn : Q.Normal) (hQp : IsPGroup 3 Q)
    (hQc : Subgroup.centralizer (Q : Set X) ≤ Q)
    {N S : Subgroup X} (hN : N.Normal) (hSN : S ≤ N) (hS3 : IsPGroup 3 S)
    (hmax : ∀ S' : Subgroup X, S' ≤ N → IsPGroup 3 S' → S ≤ S' → S' ≤ S)
    (hab : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) : S.Normal := by
  have := hQn
  have := hN
  have hQN3 : IsPGroup 3 (N ⊓ Q : Subgroup X) := hQp.to_le inf_le_right
  have hQNS : N ⊓ Q ≤ S :=
    le_sup_right.trans (hmax _ (sup_le hSN inf_le_left)
      (hS3.to_sup_of_normal_right hQN3) le_sup_left)
  set QN : Subgroup X := N ⊓ Q with hQN
  set Y : Subgroup X := N ⊓ centralizer (QN : Set X) with hY
  have hYn : Y.Normal := by rw [hY]; infer_instance
  have hYN : Y ≤ N := inf_le_left
  have hYc : Y ≤ centralizer (QN : Set X) := inf_le_right
  have hSY : S ≤ Y := le_inf hSN fun s hs q hq => hab q (hQNS hq) s hs
  have hYQ : ⁅Y, Q⁆ ≤ QN := (commutator_le_inf Y Q).trans (inf_le_inf_right Q hYN)
  have hYQY : ⁅⁅Y, Q⁆, Y⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (hYQ.trans (le_centralizer_iff.mp hYc))
  have hQYY : ⁅⁅Q, Y⁆, Y⁆ = ⊥ := by rw [commutator_comm Q Y]; exact hYQY
  have hYYQ : ⁅⁅Y, Y⁆, Q⁆ = ⊥ := commutator_commutator_eq_bot_of_rotate hYQY hQYY
  have hYY : ⁅Y, Y⁆ ≤ QN :=
    le_inf ((commutator_le_left Y Y).trans hYN)
      ((commutator_eq_bot_iff_le_centralizer.mp hYYQ).trans hQc)
  have hYYY : ⁅⁅Y, Y⁆, Y⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (hYY.trans (le_centralizer_iff.mp hYc))
  have hnil : Group.IsNilpotent Y := (isNilpotent_iff_lowerCentralSeries Y).mpr ⟨2, hYYY⟩
  have hY3 : IsPGroup 3 Y := isPGroup_three_of_nilpotent_normal h1 Y
  have hSeq : S = Y := le_antisymm hSY (hmax Y hYN hY3 hSY)
  rw [hSeq]
  exact hYn

end CFSG.LocalAnalysis.RankThreeTheoremC
