module

public import CFSG.HardMathSupport.Solomon.Coordinator.I11_2FullCore
public import CFSG.HardMathSupport.Solomon.Coordinator.I11_2VTables
public import CFSG.HardMathSupport.Solomon.Coordinator.I11_2VCentre

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Timmesfeld.ComponentBalance

section Rank

variable {K : Type*} [Group K] [Finite K]

theorem i112v_two_le_pRank_aux {Z : Subgroup K} {x : K} (hZ3 : Nat.card Z = 3)
    (hZx : ∀ z ∈ Z, z * x = x * z) (hxZ : x ∉ Z) (hx3 : x ^ 3 = 1) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup K) := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hx1 : x ≠ 1 := fun h => hxZ (h ▸ Z.one_mem)
  have hox : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hZc : IsCyclic Z := isCyclic_of_prime_card hZ3
  have hZE : IsElemAbelian 3 Z := by
    refine isElemAbelian_of_forall (fun u hu v hv => ?_) fun z hz => ?_
    · have := hZc.commGroup.mul_comm ⟨u, hu⟩ ⟨v, hv⟩
      exact congrArg Subtype.val this
    · have h1 : orderOf (⟨z, hz⟩ : Z) ∣ 3 := hZ3 ▸ orderOf_dvd_natCard _
      exact congrArg Subtype.val (orderOf_dvd_iff_pow_eq_one.1 h1)
  have hXE : IsElemAbelian 3 (Subgroup.zpowers x) := by
    refine isElemAbelian_of_forall (fun u hu v hv => ?_) (fun u hu => ?_)
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
      exact (Commute.zpow_zpow_self x i j).eq
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow]
  have hcomm : ∀ u ∈ Z, ∀ v ∈ Subgroup.zpowers x, u * v = v * u := by
    intro u hu v hv
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
    exact (Commute.zpow_right (hZx u hu : Commute u x) i).eq
  have hinf : Z ⊓ Subgroup.zpowers x ≤ ⊥ := by
    intro v hv
    obtain ⟨hvZ, hvx⟩ := Subgroup.mem_inf.1 hv
    by_contra hv1
    have hcard : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hox]
    have hle : Subgroup.zpowers v ≤ Subgroup.zpowers x := Subgroup.zpowers_le.2 hvx
    have hv3 : orderOf v = 3 := by
      have hdvd : orderOf v ∣ 3 := by
        rw [← Nat.card_zpowers, ← hcard]
        exact Subgroup.card_dvd_of_le hle
      rcases (Nat.dvd_prime hp).1 hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.1 h) (by simpa using hv1)
      · exact h
    have heq : Subgroup.zpowers v = Subgroup.zpowers x :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hv3, hox])
    have hxv : x ∈ Subgroup.zpowers v := heq ▸ Subgroup.mem_zpowers x
    exact hxZ (Subgroup.zpowers_le.2 hvZ hxv)
  have hW : CFSG.Open.pRank 3 (⊥ : Subgroup K) ≤ 0 := by
    refine CFSG.SectionRank.pRank_le hp.one_lt fun E hE _ => ?_
    rw [le_bot_iff.1 hE, Subgroup.card_bot]
    norm_num
  obtain ⟨hEa, hEc⟩ := card_mul_le_card_sup_mul_pow hp hZE hXE hcomm hinf hW
  obtain ⟨e, he⟩ := exists_card_eq_of_isElemAbelian hp hEa
  rw [hZ3, Nat.card_zpowers, hox, he, pow_zero, mul_one,
    show (3 : ℕ) * 3 = 3 ^ 2 by norm_num] at hEc
  have he2 : 2 ≤ e := (Nat.pow_le_pow_iff_right hp.one_lt).1 hEc
  exact he2.trans (CFSG.SectionRank.le_pRank hp.one_lt le_top hEa he)

end Rank

section Sylow

variable {K : Type} [Group K] [Finite K]

theorem i112v_exists_noncentral (TM : Tables112More) (hq : CFSG.Open.IsQuasisimple K)
    (hK : CFSG.Open.IsKGroup K)
    (ht : IsHatSix K ∨ IsHatSeven K ∨ IsHatMTwentyTwo K ∨ IsSLThreeExc K ∨ IsSUThreeExc K) :
    ∃ x : K, x ∉ Subgroup.center K ∧ x ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain R : Sylow 3 K := default
  obtain ⟨-, ⟨r, hr, s, hs, hrs⟩, hexp⟩ := TM.T10_10S K hq hK ht R
  refine ⟨r, fun hrZ => hrs ?_, hexp r hr⟩
  exact (Subgroup.mem_center_iff.1 hrZ s).symm

theorem i112v_two_le_pRank (TM : Tables112More) (hq : CFSG.Open.IsQuasisimple K)
    (hK : CFSG.Open.IsKGroup K) (hZ3 : Nat.card (Subgroup.center K) = 3)
    (ht : IsHatSix K ∨ IsHatSeven K ∨ IsHatMTwentyTwo K ∨ IsSLThreeExc K ∨ IsSUThreeExc K) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup K) := by
  obtain ⟨x, hxZ, hx3⟩ := i112v_exists_noncentral TM hq hK ht
  exact i112v_two_le_pRank_aux hZ3 (fun z hz => (Subgroup.mem_center_iff.1 hz x).symm) hxZ hx3

end Sylow

section Core

variable {X : Type} [Group X] [Finite X]

theorem i112v_core (T : Tables112) (TL : TableL2) (TT : Tables112Types) (TM : Tables112More)
    (hX : CFSG.Open.IsKGroup X) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hO : GLAPPrimeCore p X = ⊥) {B : Subgroup X} (hB : IsElemAbelian p B)
    (hr : GLATwoLocalRank p X ≤ CFSG.Open.pRank p B) {L : Subgroup X}
    (hL : GLAPComponent p ⊤ L) (hnL : ¬ B ≤ Subgroup.normalizer (L : Set X)) :
    p = 3 ∧ (Subgroup.normalizer (L : Set X)).relIndex B = 3 ∧
      CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut ↥L)) ≤ 2 ∧
      IsElemAbelian 3 (i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X)) ∧
      Nat.card ↥(i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X)) ≤ 9 ∧
      ((Nat.card ↥(Subgroup.center ↥L) = 1 ∧
          i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X) = ⊥ ∧
          CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) = 1 ∧ IsLTwoOddPow ↥L) ∨
        (Nat.card ↥(Subgroup.center ↥L) = 3 ∧
          (IsHatSix ↥L ∨ IsHatSeven ↥L ∨ IsHatMTwentyTwo ↥L ∨ IsSLThreeExc ↥L ∨
            IsSUThreeExc ↥L) ∧
          (Nat.card ↥(i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X)) = 3 ∨
            (Nat.card ↥(i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X)) = 9 ∧
              IsSUThreeTwoPow ↥L ∧
              Nat.card ↥((i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X)) ⊓
                Subgroup.centralizer (B : Set X)) = 3 ∧
              CFSG.Open.pRank 3 B < CFSG.Open.pRank 3
                ((B ⊓ Subgroup.centralizer (i112J B L : Set X)) ⊔ i112J B L))))) := by
  obtain ⟨h3, hidx, haut, ⟨hZE, hZ9le⟩, -⟩ := i112f_core T TL TT hX hp hp2 hO hB hr hL hnL
  subst h3
  obtain ⟨-, hz, hmZ⟩ := i112_ok_of_tables T hX hp hp2 hO hB hr hL hnL
  have hLc : CFSG.Open.IsComponentOf L ⊤ := i116pI_isComponentOf hO hL
  have hq : CFSG.Open.IsQuasisimple ↥L := i116e_isQuasisimple hO hL
  have hK : CFSG.Open.IsKGroup ↥L := isKGroup_of_le hX L
  refine ⟨rfl, hidx, haut, hZE, hZ9le, ?_⟩
  rcases hz with ⟨hc1, -, hm, hw⟩ | ⟨-, hc3⟩
  · left
    exact ⟨hc1, i112v_Z_eq_bot hLc hc1, hm,
      i112f_isLTwoOddPow_of_isL2 (TL.T ↥L hq hK hc1 hm hw)⟩
  · right
    have ht5 := i112f_types_three T TT hX hO hB hr hL hnL hidx hc3 hmZ
    refine ⟨hc3, ht5, ?_⟩
    have h2 : ∃ t : ↥L, orderOf t = 2 := T.T0 ↥L hq hK
    obtain ⟨r, a, -, hrel, -, hHr, hmaster⟩ := i112_master hp hO hB hr hL hnL h2
    have hr1 : r = 1 := by
      have h : (3 : ℕ) ^ r = 3 ^ 1 := by rw [← hrel, hidx, pow_one]
      exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h
    subst hr1
    have hz1 := i112f_pRank_center_eq_one hc3
    have hc := i112_pRank_Z_inf_B_le_one hp rfl hO hB hL hnL hidx hc3
    have ha : a ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut ↥L)) :=
      hHr ▸ i112_pRank_H_le (by norm_num)
    have hw := i112_pRank_center_le_twoLocal hp h2
    have hm2 := i112v_two_le_pRank TM hq hK hc3 ht5
    have hmZ1 : 1 ≤ CFSG.Open.pRank 3 (i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X)) := by
      rw [← hz1, ← pRank_centreIn_eq_center (by norm_num) L]
      exact CFSG.SectionRank.pRank_mono (by norm_num) (i112_centreIn_le_Z hLc i112_self_mem_orbit)
    rw [hz1] at hmaster hw
    simp only [pow_one] at hmaster
    obtain ⟨k, hk⟩ :=
      CFSG.HardMathSupport.Timmesfeld.ComponentBalance.exists_card_eq_of_isElemAbelian hp hZE
    have hk' :=
      CFSG.HardMathSupport.Timmesfeld.ComponentBalance.pRank_eq_of_card hp.one_lt hZE hk
    by_cases hw2 : 2 ≤ GLATwoLocalRank 3 ↥L
    · left
      have : k = 1 := by omega
      rw [hk, this, pow_one]
    · have hw1 : GLATwoLocalRank 3 ↥L = 1 := by omega
      have hSU : IsSUThreeTwoPow ↥L := by
        rcases ht5 with h6 | h7 | h22 | hSL | hSUe
        · exact absurd (TM.T10_16 ↥L hq hK (Or.inl h6)) hw2
        · exact absurd (TM.T10_16 ↥L hq hK (Or.inr (Or.inl h7))) hw2
        · exact absurd (TM.T10_16 ↥L hq hK (Or.inr (Or.inr h22))) hw2
        · exact TM.T10_18_3 ↥L hq hK (Or.inl hSL) hw1
        · exact TM.T10_18_3 ↥L hq hK (Or.inr hSUe) hw1
      have hk12 : k = 1 ∨ k = 2 := by omega
      rcases hk12 with h1 | h2'
      · left
        rw [hk, h1, pow_one]
      · right
        have hZ9 : Nat.card ↥(i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X)) = 9 := by
          rw [hk, h2']
          norm_num
        exact ⟨hZ9, hSU, i112v_card_Z_inf_cent_eq hO hB hL hnL hidx hc3,
          i112v_rank_lt hO hB hL hnL hidx hc3 hZ9 hm2 haut⟩

end Core

end CFSG.HardMathSupport.Solomon.Coordinator
