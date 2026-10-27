module

public import CFSG.CGT.T75K.ExoticCore
public import CFSG.CGT.T75K.ExoticHat
public import CFSG.CGT.Timmesfeld75.Sec62Final

public section

namespace CFSG.CGT.T75K

open CFSG.Open CFSG.CGT.Timmesfeld75

theorem sec62ExoticBig_of_noA (h1 : Sec4NoA) : Sec62ExoticBig := by
  intro G _ T T₁ n m hc hn x l T₂ d hne
  have := hc.finite
  have hq : 2 ≤ 2 ^ m :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.2 (m_ne_zero hc))
  rcases hc.hcase with h4 | hnat | ⟨h16, hN, hhat⟩
  · exfalso
    have h5 : 2 ^ 4 ≤ (2 ^ m) ^ n :=
      (Nat.pow_le_pow_right (by norm_num) hn).trans (Nat.pow_le_pow_left hq n)
    rw [← hc.hT, h4] at h5
    norm_num at h5
  · obtain ⟨D⟩ := NaturalSL.toLinData left_le_hSub
      (hSub_le_normalizer (fun z hz => (mem_normIn.1 hz).2)) hnat
    obtain ⟨h, hh⟩ := exists_levi hc (by omega) D le_hSub d.hx d.hx1
    obtain ⟨t, ht, hT₂⟩ := exotic_core h1 hc hn d hne hh
    rw [hT₂]
    exact conjSubgroup_le_of_le_of_mem le_sup_right (Subgroup.mem_sup_left ht)
  · exact (no_hat hc hn h16 le_hSub hhat).elim

end CFSG.CGT.T75K
