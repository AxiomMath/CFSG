module

public import CFSG.GH74.GLS.Stage4.Glue

public section

namespace CFSG.GH74.GLS.Stage4

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.GH74.BNPair

theorem prime_ne_two_of_odd_pow {p f q : ℕ} (hf : 1 ≤ f) (hpf : p ^ f = q) (hq : Odd q) :
    p ≠ 2 := by
  rintro rfl
  obtain ⟨k, hk⟩ := hq
  have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
  omega

theorem s_ch6_Std_of_bn (hA : Ch6LocalBN) (hB : HexagonClassification) : S_ch6_Std := by
  intro G _ _ hStd hr hIn
  rcases hIn with hAsc | ⟨Gs, _, hT⟩
  · exact Or.inr (Or.inr (Or.inr hAsc))
  · have hG2 : IsTwoCentralG2TypeG2 G Gs := IsTwoCentralG2Type.g2 hStd.nonab hT
    obtain ⟨D, q, hqodd, hcase⟩ := hA G hStd hr Gs hG2
    have : IsSimpleGroup G := hStd.kps.1
    rcases hcase with ⟨h5, hD⟩ | ⟨h3, hD⟩
    · obtain ⟨p, f, hp, hf, hpf, hL⟩ := hB.1 G D q (by omega) hD
      exact Or.inr (Or.inl ⟨p, f, hp, prime_ne_two_of_odd_pow hf hpf hqodd, hf, by omega, hL⟩)
    · obtain ⟨p, f, hp, hf, hpf, hL⟩ := hB.2 G D q (by omega) hD
      exact Or.inr (Or.inr (Or.inl ⟨p, f, hp, prime_ne_two_of_odd_pow hf hpf hqodd, hf, hL⟩))

theorem s_ch6_Std_of (hA : Ch6LocalRGD2) (hB : HexagonClassification) : S_ch6_Std :=
  s_ch6_Std_of_bn (ch6LocalBN_of_rgd2 hA) hB

end CFSG.GH74.GLS.Stage4
