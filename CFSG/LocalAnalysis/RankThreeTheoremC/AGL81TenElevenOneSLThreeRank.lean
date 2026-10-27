module

import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenElevenOneTypeThreeGroup
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81FourSixteenPGroup
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3E27

open CFSG.Open Subgroup

variable {Y : Type} [Group Y] [Finite Y]

theorem three_le_pRank_centralizer_of_commute_not_mem {p : ℕ} [Fact p.Prime] {D : Subgroup Y}
    (hD : IsElemAbelian p D) (hDc : Nat.card D = p ^ 2) {u : Y} (huD : u ∉ D) (hup : u ^ p = 1)
    (hud : ∀ d ∈ D, d * u = u * d) : 3 ≤ Open.pRank p (centralizer (D : Set Y)) := by
  have hp1 : 1 < p := Fact.out (p := p.Prime) |>.one_lt
  have hDcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb => by
    simpa using congrArg Subtype.val (hD.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  set s : Set Y := (D : Set Y) ∪ {u}
  have hcomm : s.Pairwise Commute := by
    rintro a (ha | rfl) b (hb | rfl) -
    · exact hDcomm a ha b hb
    · exact hud a ha
    · exact (hud b hb).symm
    · exact Commute.refl _
  have hexp : ∀ a ∈ s, a ^ p = 1 := by
    rintro a (ha | rfl)
    · exact hD.2 a ha
    · exact hup
  set D' := closure s
  have hD'e : IsElemAbelian p D' :=
    ⟨isMulCommutative_closure hcomm, fun x hx =>
      FourSixteen.pow_eq_one_of_mem_closure hcomm hexp hx⟩
  have hD'C : D' ≤ centralizer (D : Set Y) := by
    rw [closure_le]
    rintro a (ha | rfl)
    · exact mem_centralizer_iff.2 fun d hd => hDcomm d hd a ha
    · exact mem_centralizer_iff.2 fun d hd => hud d hd
  have hDD' : D < D' := by
    refine lt_of_le_of_ne (fun d hd => subset_closure (Or.inl hd)) fun h => huD ?_
    rw [h]
    exact subset_closure (Or.inr rfl)
  have hD'p : IsPGroup p D' := fun x => ⟨1, Subtype.ext (by simpa using hD'e.2 _ x.2)⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hD'p
  have hlt := Subgroup.card_lt_of_lt hDD'
  rw [hDc, hk] at hlt
  have hk3 : 3 ≤ k := by
    have := (Nat.pow_lt_pow_iff_right hp1).1 hlt
    omega
  exact hk3.trans (CFSG.SectionRank.le_pRank hp1 hD'C hD'e hk)

theorem eq_sup_zpowers_of_card {D : Subgroup Y} (hDc : Nat.card D = 3 ^ 2) {x z : Y}
    (hz : orderOf z = 3) (hzD : z ∈ D) (hxD : x ∈ D) (hxz : x ∉ zpowers z) :
    zpowers x ⊔ zpowers z = D := by
  have hDp : IsPGroup 3 D := IsPGroup.of_card hDc
  set H := zpowers x ⊔ zpowers z
  have hHD : H ≤ D := sup_le (zpowers_le.2 hxD) (zpowers_le.2 hzD)
  have hlt : zpowers z < H := by
    refine lt_of_le_of_ne le_sup_right fun h => hxz ?_
    rw [h]
    exact mem_sup_left (mem_zpowers x)
  have hc1 := Subgroup.card_lt_of_lt hlt
  rw [Nat.card_zpowers, hz] at hc1
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card).1 (hDp.to_le hHD)
  have hdvd : Nat.card H ∣ 3 ^ 2 := hDc ▸ Subgroup.card_dvd_of_le hHD
  rw [hj] at hdvd hc1
  have hj2 : j ≤ 2 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hdvd
  have hj1 : 1 < j :=
    (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).1 (by rw [pow_one]; exact hc1)
  exact Subgroup.eq_of_le_of_card_ge hHD (by rw [hDc, hj, show j = 2 by omega])

theorem three_le_pRank_centralizer_of_commute {z : Y} (hz : orderOf z = 3)
    [(zpowers z).Normal]
    (hw : ∀ x : Y, x ^ 3 = 1 → x ∉ zpowers z →
      ∃ w : Y, w * x = x * w ∧ w ^ 3 = 1 ∧ w ∉ zpowers x ⊔ zpowers z)
    {D : Subgroup Y} (hD : IsElemAbelian 3 D) (hDc : Nat.card D = 3 ^ 2) :
    3 ≤ Open.pRank 3 (centralizer (D : Set Y)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hzc : ∀ g : Y, g ^ 3 = 1 → g * z = z * g := fun g hg =>
    mul_comm_of_conj_mem_zpowers hz
      ((inferInstance : (zpowers z).Normal).conj_mem z (mem_zpowers z) g)
      (odd_orderOf_of_isPGroup_three (isPGroup_zpowers_of_pow_eq_one (n := 1) (by simpa using hg)))
  by_cases hzD : z ∈ D
  ·
    have hlt : zpowers z < D := by
      refine lt_of_le_of_ne (zpowers_le.2 hzD) fun h => ?_
      have := congrArg (fun H : Subgroup Y => Nat.card H) h
      simp only [Nat.card_zpowers, hz, hDc] at this
      norm_num at this
    obtain ⟨x, hxD, hxz⟩ := SetLike.exists_of_lt hlt
    have hx3 : x ^ 3 = 1 := hD.2 x hxD
    obtain ⟨w, hwx, hw3, hwD⟩ := hw x hx3 hxz
    have hDxz := eq_sup_zpowers_of_card hDc hz hzD hxD hxz
    refine three_le_pRank_centralizer_of_commute_not_mem hD hDc
      (fun h => hwD (hDxz ▸ h)) hw3 fun d hd => ?_
    rw [← hDxz] at hd
    have hcw : d ∈ centralizer ({w} : Set Y) := by
      refine (sup_le (zpowers_le.2 ?_) (zpowers_le.2 ?_)) hd
      · exact mem_centralizer_singleton_iff.2 hwx.symm
      · exact mem_centralizer_singleton_iff.2 (hzc w hw3).symm
    exact mem_centralizer_singleton_iff.1 hcw
  · exact three_le_pRank_centralizer_of_commute_not_mem hD hDc hzD
      (by rw [← hz, pow_orderOf_eq_one]) fun d hd => (hzc d (hD.2 d hd))

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3E27
