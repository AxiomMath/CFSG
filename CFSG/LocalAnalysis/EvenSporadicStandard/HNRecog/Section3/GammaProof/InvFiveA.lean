module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GammaProof.Orders
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GammaProof.OddA8

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] [Finite G] {a z : G}

theorem gamma_inv_fiveA (H : GammaHyps a z) {y t : G} (hy : y ∈ orb5A a a)
    (ht : t ∈ orb2A a y) : ∃ s : G, orderOf s = 2 ∧ s ∈ Gxyz a y t := by
  have hyA : IsConj a y := hy.1.1
  have ht' : t ∈ orb2A y y := (gamma_orb2A_eq hyA y).symm ▸ ht
  have hXZ : Gxy a y ≤ Gx y := by
    rw [Gxy_eq_inf]
    exact inf_le_right
  have hYZ : Gxy y t ≤ Gx y := by
    rw [Gxy_eq_inf]
    exact inf_le_left
  have hXcard : Nat.card ↥(Gxy a y) = 126000 :=
    H.hU.card_eq ↥(Gxy a y) ((H.hT7.self).shape_5A y hy)
  have hYcard : Nat.card ↥(Gxy y t) = 80640 := by
    have hmem : t ∈ tab5Set y z 0 := by simpa [tab5Set] using ht'
    rw [Gxy_eq_inf]
    simpa using (H.hT5 y z hyA (IsConj.refl z)).card_stab 0 t hmem
  have hZcard : Nat.card ↥(Gx y) = 177408000 := gamma_card_Gx (H.at hyA)
  have hle := gamma_card_mul_le hXZ hYZ
  rw [hXcard, hYcard, hZcard] at hle
  have hgt : 57 < Nat.card ↥(Gxy a y ⊓ Gxy y t) := by
    by_contra h
    rw [not_lt] at h
    have h1 : Nat.card ↥(Gxy a y ⊓ Gxy y t) * 177408000 ≤ 57 * 177408000 :=
      Nat.mul_le_mul_right 177408000 h
    norm_num at hle h1
    omega
  have hM : IsShapeTwoTwoTimesA8 ↥(Gxy y t) :=
    (H.hT5 y z hyA (IsConj.refl z)).shape_2A t ht'
  have heven : Even (Nat.card ↥(Gxy a y ⊓ Gxy y t)) := by
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    have hle57 := gamma_odd_card_le hM inf_le_right hodd
    omega
  have hdvd : 2 ∣ Nat.card ↥(Gxy a y ⊓ Gxy y t) := even_iff_two_dvd.mp heven
  obtain ⟨s, hs, hsord⟩ := gamma_exists_inv_of_two_dvd hdvd
  refine ⟨s, hsord, ?_⟩
  rw [Subgroup.mem_inf] at hs
  rw [mem_Gxyz]
  exact ⟨(mem_Gxy.mp hs.1).1, (mem_Gxy.mp hs.1).2, (mem_Gxy.mp hs.2).2⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
