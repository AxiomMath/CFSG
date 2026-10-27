module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OddCentralCoverAtCenterPrimes
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.KFactU33

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542Three

open CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
open scoped commutatorElement

theorem card_of_isRankTwoLayerType {K : Type} [Group K] (h : IsRankTwoLayerType K) :
    Nat.card K = 360 ∨ Nat.card K = 168 ∨ Nat.card K = 6048 := by
  rcases h with h | h | h
  · obtain ⟨e⟩ := h
    refine .inl ?_
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  · obtain ⟨e⟩ := nonempty_equiv_gl32_of_model h
    exact .inr (.inl (by rw [Nat.card_congr e.toEquiv, SylowL32.card_gl]))
  · obtain ⟨F, hF, hF9, ⟨e⟩⟩ := exists_equiv_statedSU_of_model h
    exact .inr (.inr (by
      rw [Nat.card_congr e.toEquiv, CFSG.LinearGroups.UnitaryThreeOverNine.card_statedSU hF9]))

theorem le_one_of_pow_dvd {n r k : ℕ} (hn : n = 360 ∨ n = 168 ∨ n = 6048) (hr : r.Prime)
    (hr2 : r ≠ 2) (hr3 : r ≠ 3) (hdvd : r ^ k ∣ n) : k ≤ 1 := by
  by_contra hk
  have h2 : r ^ 2 ∣ n := (Nat.pow_dvd_pow r (by omega)).trans hdvd
  have hn0 : 0 < n := by rcases hn with rfl | rfl | rfl <;> norm_num
  have hle : r ^ 2 ≤ 6048 :=
    (Nat.le_of_dvd hn0 h2).trans (by rcases hn with rfl | rfl | rfl <;> norm_num)
  have hr78 : r < 78 := by nlinarith
  rcases hn with rfl | rfl | rfl <;> interval_cases r <;> (revert hr hr2 hr3 h2; norm_num)

theorem center_eq_bot_of_layerType {R : Type} [Group R] [Finite R] [Group.IsPerfect R]
    (hty : IsRankTwoLayerType (R ⧸ Subgroup.center R))
    (h2 : ¬ 2 ∣ Nat.card (Subgroup.center R)) (h3 : ¬ 3 ∣ Nat.card (Subgroup.center R)) :
    Subgroup.center R = ⊥ := by
  have hcard := card_of_isRankTwoLayerType hty
  refine CFSG.GorensteinWalter.oddCentralCover_eq_bot_of_cyclic_sylow_at_center_primes
    Group.IsPerfect.commutator_eq_top (Subgroup.center R) rfl (Nat.odd_iff.mpr ?_) ?_
  · exact Nat.two_dvd_ne_zero.mp h2
  · intro r hr hrZ hr2 S
    have hr3 : r ≠ 3 := by
      rintro rfl
      exact h3 hrZ
    obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
    have hdvd : r ^ k ∣ Nat.card (R ⧸ Subgroup.center R) := by
      rw [← hk]
      exact Subgroup.card_subgroup_dvd_card _
    have hk1 := le_one_of_pow_dvd hcard hr.out hr2 hr3 hdvd
    interval_cases k
    · have h1 : Nat.card (S : Subgroup (R ⧸ Subgroup.center R)) = 1 := by rw [hk, pow_zero]
      have : Subsingleton (S : Subgroup (R ⧸ Subgroup.center R)) :=
        (Nat.card_eq_one_iff_unique.mp h1).1
      show IsCyclic (S : Subgroup (R ⧸ Subgroup.center R))
      infer_instance
    · show IsCyclic (S : Subgroup (R ⧸ Subgroup.center R))
      exact isCyclic_of_prime_card (by rw [hk, pow_one])

end CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542Three
