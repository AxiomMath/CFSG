module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434Heis
public import CFSG.Monster.B.Pinned.Primes.Extraspecial

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434.SporS1

open CFSG.Monster.B.Pinned (bcomm CommData)

variable {G : Type*} [Group G]

theorem heisRel_of_bcomm {a b z : G} (ha : a ^ 5 = 1) (hb : b ^ 5 = 1) (hz : z ^ 5 = 1)
    (haz : a * z = z * a) (hbz : b * z = z * b) (h : bcomm a b = z) : HeisRel a b z where
  ha := ha
  hb := hb
  hc := hz
  ac := haz
  bc := hbz
  ab := by
    have h1 : a * b = b * a * z := by
      rw [← h, bcomm]
      group
    rw [h1, (Commute.mul_left hbz haz).eq]

theorem hasNonabelianFiveSubgroup_of_commData {n : ℕ} {q : Fin n → G} {z : G}
    {M : Matrix (Fin n) (Fin n) (ZMod 5)} (hD : CommData 5 q z M) {i j : Fin n}
    (hz : bcomm (q i) (q j) = z) : HasNonabelianFiveSubgroup G := by
  have hz5 : z ^ 5 = 1 := by
    rw [← hD.orderOf_z]
    exact pow_orderOf_eq_one z
  refine hasNonabelianFiveSubgroup_of_heis
    (heisRel_of_bcomm (hD.pow_q i) (hD.pow_q j) hz5 (hD.comm_z i) (hD.comm_z j) hz) ?_
  intro h1
  have h := hD.orderOf_z
  rw [h1, orderOf_one] at h
  exact absurd h (by norm_num)

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434.SporS1
