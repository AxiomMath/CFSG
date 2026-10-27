module

public import CFSG.CGT.T75P.IdentGen
public import CFSG.CGT.T75Q.OrdersSL
public import CFSG.Sporadic.Mathieu.M22
public import CFSG.Sporadic.Mathieu.M23
public import CFSG.Sporadic.Mathieu.M24

public section

namespace CFSG.CGT.T75Q

open CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.CGT.T75P CFSG.Assembly.LowTwoRank

theorem card_native_M23 :
    Nat.card CFSG.Blueprint.NativeSporadic.M23 = 10200960 := by
  rw [CFSG.Sporadic.Mathieu.nativeM23_eq]
  exact (Nat.card_eq_fintype_card (α := CFSG.M23.M23Group.H0)).trans
    CFSG.M23.M23Group.card_M23

theorem card_eq_of_sixteen
    {K : Type} [Group K] [Finite K] {Tb : Subgroup K} (hstd : StdPair K Tb) (hnb : NonBender K)
    (h16 : Nat.card Tb = 16) (hdvd : 322560 ∣ Nat.card K) :
    Nat.card K = 9999360 ∨ Nat.card K = 244823040 := by
  rcases hnb with ⟨m, s, hm3, hs1, hmod⟩ | ⟨k, hk6, hk9, hk⟩ | h22 | h23 | h24
  · obtain ⟨-, F, hF, hFin, hFc, ⟨e⟩⟩ := hmod
    have h := (hstd.of_psl hm3 F hFc e).1
    rw [h16] at h
    have hsm : s * (m - 1) = 4 := by
      have h' : (2 : ℕ) ^ 4 = 2 ^ (s * (m - 1)) := by rw [← h]; norm_num
      exact (Nat.pow_right_injective (le_refl 2) h').symm
    have hKc : Nat.card K = Nat.card (StatedProj (StatedSL m F)) := Nat.card_congr e.toEquiv
    have hs2 : s ≤ 2 := by
      by_contra hlt
      have : 3 * 2 ≤ s * (m - 1) := Nat.mul_le_mul (by omega) (by omega)
      omega
    interval_cases s
    · have hm5 : m = 5 := by omega
      subst hm5
      left
      have hF2 : Nat.card F = 2 := by simpa using hFc
      rw [hKc, card_statedProj_of_card_two 5 hF2, card_SL_five_two hF2]
    · have hm3' : m = 3 := by omega
      subst hm3'
      exfalso
      have hF4 : Nat.card F = 4 := by simpa using hFc
      have hd := (card_statedProj_dvd 3 (F := F)).trans (card_SL_three_four hF4).dvd
      rw [← hKc] at hd
      have := Nat.le_of_dvd (by norm_num) (hdvd.trans hd)
      omega
  · exfalso
    have h := hstd.card_alternating hk6 hk9 hk
    rw [h16] at h
    split_ifs at h <;> omega
  · exfalso
    obtain ⟨e⟩ := h22
    have hc : Nat.card K = 443520 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.Mathieu.card_M22
    rw [hc] at hdvd
    exact absurd hdvd (by norm_num)
  · exfalso
    obtain ⟨e⟩ := h23
    have hc : Nat.card K = 10200960 := by
      rw [Nat.card_congr e.toEquiv]
      exact card_native_M23
    rw [hc] at hdvd
    exact absurd hdvd (by norm_num)
  · right
    obtain ⟨e⟩ := h24
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Mathieu.card_M24

end CFSG.CGT.T75Q
