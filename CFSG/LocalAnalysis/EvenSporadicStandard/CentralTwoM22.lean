module

public import CFSG.LocalAnalysis.EvenSporadicStandard.CentralTwoRows
public import CFSG.Sporadic.Recognition.M22MultiplierCert

public section

namespace CFSG.EvenSporadicStandard

theorem card_dvd_four_of_dvd_twelve {Z : Type*} [Group Z] [Finite Z] (h2 : IsPGroup 2 Z)
    (h : Nat.card Z ∣ 12) : Nat.card Z ∣ 4 := by
  obtain ⟨n, hn⟩ := h2.exists_card_eq
  rw [hn] at h ⊢
  have hn2 : n ≤ 2 := by
    by_contra hn3
    have : 2 ^ 3 ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
    have := this.trans h
    omega
  exact (pow_dvd_pow 2 hn2).trans (by norm_num)

theorem rowBound_M22 :
    RowBound .M22 :=
  fun L _ _ hq hZ hs => by
    obtain ⟨e⟩ := hs
    obtain ⟨hcyc, hdvd⟩ :=
      CFSG.Sporadic.Recognition.M22Multiplier.center_cyclic_dvd_twelve_of_certificate
        (Group.isPerfect_def.2 hq.1) e
    exact ⟨card_dvd_four_of_dvd_twelve hZ hdvd, fun _ => hcyc⟩

end CFSG.EvenSporadicStandard
