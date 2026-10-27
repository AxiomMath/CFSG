module

public import CFSG.CGT.T75H.Classify
import CFSG.Adapters.StatedClassicalUnitaryOrders
import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.CGT.T75H

open CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

theorem two_pow_eq_four {s : ℕ} (h : 2 ^ s = 4) : s = 2 := by
  have : (2 : ℕ) ^ s = 2 ^ 2 := by rw [h]; norm_num
  exact Nat.pow_right_injective (le_refl 2) this

theorem card_eq_sixty {Y : Type} [Group Y] (h : StatedClassicalModel Y .PSL 2 2 2) :
    Nat.card Y = 60 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_four h

theorem card_eq_62400 {Y : Type} [Group Y] (h : StatedClassicalModel Y .PSU 3 2 2) :
    Nat.card Y = 62400 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_four h

theorem nine_dvd_classify {Y : Type} [Group Y] [Finite Y] {T : Subgroup Y} (hstd : StdPair Y T)
    (hc4 : Nat.card T = 4) (h9 : 9 ∣ Nat.card Y) :
    Nonempty (Y ≃* alternatingGroup (Fin 6)) ∨ Nonempty (Y ≃* alternatingGroup (Fin 7)) := by
  rcases hstd.listGroup with ⟨m, s, hm2, hs1, hmodel⟩ | ⟨s, hs2, hmodel⟩ |
    ⟨s, hso, hs3, hmodel⟩ | ⟨k, hk6, hk9, ⟨e⟩⟩ | hM | hM | hM
  · rcases Nat.lt_or_ge m 3 with hm | hm
    · have hm2' : m = 2 := by omega
      subst hm2'
      have hT := (hstd.of_psl2 hmodel).1
      rw [hc4] at hT
      have hs : s = 2 := two_pow_eq_four hT.symm
      subst hs
      have := card_eq_sixty hmodel
      rw [this] at h9
      exact absurd h9 (by norm_num)
    · obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := hmodel
      obtain ⟨hcardT, -⟩ := hstd.of_psl hm K hK e
      rw [hc4] at hcardT
      have h2 : s * (m - 1) = 2 := by
        have : (2 : ℕ) ^ 2 = 2 ^ (s * (m - 1)) := by rw [← hcardT]; norm_num
        exact (Nat.pow_right_injective (le_refl 2) this).symm
      have hs : s = 1 := by
        rcases Nat.lt_or_ge s 2 with h | h
        · omega
        · have : s * (m - 1) ≥ 2 * 2 := Nat.mul_le_mul h (by omega)
          omega
      have hm3 : m = 3 := by subst hs; omega
      subst hs
      subst hm3
      have := card_eq_168 ⟨hadm, K, inferInstance, inferInstance, hK, ⟨e⟩⟩
      rw [this] at h9
      exact absurd h9 (by norm_num)
  · have hT := (hstd.of_psu3 hs2 hmodel).1
    rw [hc4] at hT
    have hs : s = 2 := two_pow_eq_four hT.symm
    subst hs
    have := card_eq_62400 hmodel
    rw [this] at h9
    exact absurd h9 (by norm_num)
  · have hT := (hstd.of_sz hso hs3 hmodel).1
    rw [hc4] at hT
    have hs : s = 2 := two_pow_eq_four hT.symm
    exact absurd hso (by rw [hs]; decide)
  · have hcardT := hstd.card_alternating hk6 hk9 ⟨e⟩
    rw [hc4] at hcardT
    have hk : k ≤ 7 := by
      by_contra hk
      simp only [hk, ite_false] at hcardT
      omega
    have hk' : k = 6 ∨ k = 7 := by omega
    rcases hk' with rfl | rfl
    · exact Or.inl ⟨e⟩
    · exact Or.inr ⟨e⟩
  · have := hstd.card_sporadic (Or.inl hM)
    omega
  · have := hstd.card_sporadic (Or.inr (Or.inl hM))
    omega
  · have := hstd.card_sporadic (Or.inr (Or.inr hM))
    omega

end CFSG.CGT.T75H
