module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion2.QuNotMem
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion2.QuCoreLe

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private theorem natCard_A5WrTwo : Nat.card A5WrTwo = 7200 := by
  unfold A5WrTwo
  rw [RegularWreathProduct.card, nat_card_alternatingGroup, Nat.card_fin,
    Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  norm_num

private theorem natCard_of_isExtraspecialPlusByA5WrTwo {C : Type} [Group C]
    (h : IsExtraspecialPlusByA5WrTwo C) : Nat.card C = 2 ^ 9 * 7200 := by
  obtain ⟨Q, hQ, hw⟩ := h
  haveI : Q.Normal := hQ
  obtain ⟨hplus, _hcent, hquot⟩ := hw
  obtain ⟨_hext, hcardQ, _E, _hEQ, _hEab, _hEcard⟩ := hplus
  obtain ⟨eQ⟩ := hquot
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Q, Nat.card_congr eQ.toEquiv,
    natCard_A5WrTwo, hcardQ]
  norm_num

private theorem eq_of_mem_zpowers_of_orderOf_eq_two {G : Type} [Group G] [DecidableEq G] {x y : G}
    (hx : orderOf x = 2) (hy : y ∈ Subgroup.zpowers x) (hy1 : y ≠ 1) : y = x := by
  have hxfin : IsOfFinOrder x := by
    rw [isOfFinOrder_iff_pow_eq_one]
    exact ⟨2, by norm_num, by rw [← hx]; exact pow_orderOf_eq_one x⟩
  rw [hxfin.mem_zpowers_iff_mem_range_orderOf, hx, Finset.mem_image] at hy
  obtain ⟨n, hn, hny⟩ := hy
  rw [Finset.mem_range] at hn
  interval_cases n
  · simp at hny
    exact absurd hny.symm hy1
  · simp at hny
    exact hny.symm

private lemma two_mul_card_le_of_lt {G : Type} [Group G] {H K : Subgroup G} [Finite K]
    (h : H < K) : 2 * Nat.card ↥H ≤ Nat.card ↥K := by
  haveI : Finite ↥H :=
    Finite.of_injective (Subgroup.inclusion h.le) (Subgroup.inclusion_injective h.le)
  have hdvd : Nat.card ↥H ∣ Nat.card ↥K := Subgroup.card_dvd_of_le h.le
  have hlt : Nat.card ↥H < Nat.card ↥K := Subgroup.card_lt_of_lt h
  obtain ⟨k, hk⟩ := hdvd
  have hHpos : 0 < Nat.card ↥H := Nat.card_pos
  have hk2 : 1 < k := by
    rw [hk] at hlt
    exact (Nat.lt_mul_iff_one_lt_right hHpos).mp hlt
  rw [hk]
  calc 2 * Nat.card ↥H = Nat.card ↥H * 2 := by ring
    _ ≤ Nat.card ↥H * k := by exact Nat.mul_le_mul_left _ (by omega)

theorem qu_general {G : Type} [Group G] {a u : G} (ha : a ^ 2 = 1) (hu : u ^ 2 = 1) (ha1 : a ≠ 1)
    (hu1 : u ≠ 1) (hau : a ≠ u) (hcomm : a * u = u * a)
    (hC : IsExtraspecialPlusByA5WrTwo ↥(Gx u)) (hX : IsShapeTwoTwoTimesTwoFourA5 ↥(Gxy a u))
    (hT : TwoFourData (Gxy a u)) :
    a ∉ Qz u ∧ Qz u ⊓ Gx a = Subgroup.zpowers u ⊔ CFSG.Open.pCoreOf 2 (derivedOf (Gxy a u)) ∧
      Nat.card ↥(Qz u ⊓ Gx a) = 2 ^ 5 ∧ CFSG.Open.pCoreOf 2 (derivedOf (Gxy a u)) ≤ Qz u := by
  classical
  let X : Subgroup G := Gxy a u
  let L : Subgroup G := derivedOf X
  let N : Subgroup G := CFSG.Open.pCoreOf 2 L
  let T : Subgroup G := Qz u ⊓ Gx a
  have ha2 : orderOf a = 2 := orderOf_eq_prime ha ha1
  have haQ : a ∉ Qz u := a_not_mem_Qz ha hu ha1 hu1 hau hcomm hC hX
  have hXu : X ≤ Gx u := (Gxy_eq_inf a u).le.trans inf_le_right
  have hXa : X ≤ Gx a := (Gxy_eq_inf a u).le.trans inf_le_left
  have huGa : u ∈ Gx a := mem_Gx.mpr hcomm
  have haGu : a ∈ Gx u := mem_Gx.mpr hcomm.symm
  have huX : u ∈ X := mem_Gxy.mpr ⟨huGa, self_mem_Gx u⟩
  have haX : a ∈ X := mem_Gxy.mpr ⟨self_mem_Gx a, haGu⟩
  have hQz_le_Gu : Qz u ≤ Gx u := Subgroup.map_subtype_le (CFSG.pCore 2 ↥(Gx u))
  have hN_le_L : N ≤ L := Subgroup.map_subtype_le (CFSG.pCore 2 ↥L)
  have hN_le_X : N ≤ X := hN_le_L.trans (derivedOf_le X)
  have hN_le_Qz : N ≤ Qz u := pCore_derived_le_Qz hXu hC hT
  have hT_le_X : T ≤ X := by
    change T ≤ Gxy a u
    intro t ht
    rw [mem_Gxy]
    exact ⟨ht.2, hQz_le_Gu ht.1⟩
  have hT_le_Gxa : T ≤ Gx a := inf_le_right
  have ha_not_T : a ∉ T := fun h => haQ h.1
  have hcard_Gu : Nat.card ↥(Gx u) = 2 ^ 9 * 7200 :=
    natCard_of_isExtraspecialPlusByA5WrTwo hC
  haveI : Finite ↥(Gx u) := Nat.finite_of_card_ne_zero (by rw [hcard_Gu]; norm_num)
  haveI : Finite ↥X :=
    Finite.of_injective (Subgroup.inclusion hXu) (Subgroup.inclusion_injective hXu)
  haveI : Finite ↥T :=
    Finite.of_injective (Subgroup.inclusion (hT_le_X.trans hXu))
      (Subgroup.inclusion_injective _)
  have huQz : u ∈ Qz u := by
    obtain ⟨Q, hQnorm, hQW, hQz_eq⟩ := exists_Qz_eq hC
    haveI : Q.Normal := hQnorm
    have hmem : (⟨u, self_mem_Gx u⟩ : ↥(Gx u)) ∈ Q := by
      apply hQW.centralizer_le
      rw [Subgroup.mem_centralizer_iff]
      intro q _
      apply Subtype.ext
      exact (mem_Gx.mp q.2).symm
    rw [hQz_eq]
    exact Subgroup.mem_map_of_mem (Gx u).subtype hmem
  have hu_notN : u ∉ N := by
    refine not_mem_pCore_derived_of_central hT ?_ hu hu1
    intro g hg
    have hgu : g ∈ Gx u := hXu hg
    rw [mem_Gx] at hgu
    rw [← hgu, mul_assoc, mul_inv_cancel, mul_one]
  have hQz_normal : ∀ g ∈ Gx u, ∀ q ∈ Qz u, g * q * g⁻¹ ∈ Qz u := by
    intro g hg q hq
    have hq' : q ∈ (CFSG.pCore 2 ↥(Gx u)).map (Gx u).subtype := hq
    obtain ⟨q₀, hq₀, rfl⟩ := Subgroup.mem_map.mp hq'
    have h2 : g * (Gx u).subtype q₀ * g⁻¹ =
        (Gx u).subtype (⟨g, hg⟩ * q₀ * ⟨g, hg⟩⁻¹) := by
      simp [map_mul, map_inv]
    rw [h2]
    exact Subgroup.mem_map_of_mem (Gx u).subtype
      ((inferInstance : (CFSG.pCore 2 ↥(Gx u)).Normal).conj_mem q₀ hq₀ ⟨g, hg⟩)
  have hS_le_T : Subgroup.zpowers u ⊔ N ≤ T := by
    refine sup_le ?_ ?_
    · exact le_inf (Subgroup.zpowers_le.mpr huQz) (Subgroup.zpowers_le.mpr huGa)
    · exact le_inf hN_le_Qz (hN_le_X.trans hXa)
  have hS_le_Gu : Subgroup.zpowers u ⊔ N ≤ Gx u :=
    sup_le (Subgroup.zpowers_le.mpr (self_mem_Gx u)) (hN_le_X.trans hXu)
  haveI : Finite ↥(Subgroup.zpowers u ⊔ N) :=
    Finite.of_injective (Subgroup.inclusion hS_le_Gu) (Subgroup.inclusion_injective hS_le_Gu)
  have hN_card : Nat.card ↥N = 2 ^ 4 := hT.elem_two.2
  have hN_lt_S : N < Subgroup.zpowers u ⊔ N := by
    refine lt_of_le_of_ne le_sup_right ?_
    intro hEq
    apply hu_notN
    rw [hEq]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers u)
  have hS_ge : 32 ≤ Nat.card ↥(Subgroup.zpowers u ⊔ N) := by
    have h := two_mul_card_le_of_lt hN_lt_S
    rw [hN_card] at h
    norm_num at h
    exact h
  have hT'_le_X : T ⊔ Subgroup.zpowers a ≤ X :=
    sup_le hT_le_X (Subgroup.zpowers_le.mpr haX)
  haveI : Finite ↥(T ⊔ Subgroup.zpowers a) :=
    Finite.of_injective (Subgroup.inclusion hT'_le_X) (Subgroup.inclusion_injective hT'_le_X)
  have hT_le_norm_zp : T ≤ Subgroup.normalizer (Subgroup.zpowers a) := by
    have hcent_eq : Gx a = Subgroup.centralizer (Subgroup.zpowers a : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact hT_le_Gxa.trans (hcent_eq.trans_le (Subgroup.centralizer_le_normalizer _))
  have hz_pg : IsPGroup 2 ↥(Subgroup.zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha2]; norm_num)
  have hQz_pg : IsPGroup 2 ↥(Qz u) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥(Gx u))).map (Gx u).subtype
  have hT_pg : IsPGroup 2 ↥T := hQz_pg.to_le inf_le_left
  have hT'_pg : IsPGroup 2 ↥(T ⊔ Subgroup.zpowers a) :=
    hT_pg.to_sup_of_normal_right' hz_pg hT_le_norm_zp
  have hnorm : ∀ g ∈ X, ∀ p ∈ T ⊔ Subgroup.zpowers a,
      g * p * g⁻¹ ∈ T ⊔ Subgroup.zpowers a := by
    have hX_le_normT : X ≤ Subgroup.normalizer T := by
      rw [Subgroup.le_normalizer_iff]
      intro g hg t ht
      exact ⟨hQz_normal g (hXu hg) t ht.1,
        (Gx a).mul_mem ((Gx a).mul_mem (hXa hg) ht.2) ((Gx a).inv_mem (hXa hg))⟩
    have hX_le_normzp : X ≤ Subgroup.normalizer (Subgroup.zpowers a) := by
      rw [Subgroup.le_normalizer_iff]
      intro g hg s hs
      have hga : g * a = a * g := (mem_Gx.mp (hXa hg)).symm
      by_cases hs1 : s = 1
      · rw [hs1, mul_one, mul_inv_cancel]
        exact Subgroup.one_mem _
      · rw [eq_of_mem_zpowers_of_orderOf_eq_two ha2 hs hs1, hga, mul_assoc, mul_inv_cancel,
          mul_one]
        exact Subgroup.mem_zpowers a
    intro g hg p hp
    have hmem : g ∈ Subgroup.normalizer ((T ⊔ Subgroup.zpowers a : Subgroup G) : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_sup T (Subgroup.zpowers a)
        ⟨hX_le_normT hg, hX_le_normzp hg⟩
    exact ((Subgroup.mem_normalizer_iff.mp hmem) p).mp hp
  have hT'_card_le : Nat.card ↥(T ⊔ Subgroup.zpowers a) ≤ 64 :=
    card_le_of_normal_isPGroup hX (T ⊔ Subgroup.zpowers a) hT'_le_X hnorm hT'_pg
  have hT_lt_T' : T < T ⊔ Subgroup.zpowers a := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro hEq
    apply ha_not_T
    rw [hEq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
  have hT_card_le : Nat.card ↥T ≤ 32 := by
    have h := two_mul_card_le_of_lt hT_lt_T'
    have h2 := hT'_card_le
    omega
  have hS_card_le : Nat.card ↥(Subgroup.zpowers u ⊔ N) ≤ Nat.card ↥T :=
    Subgroup.card_le_of_le hS_le_T
  have hS_card_eq32 : Nat.card ↥(Subgroup.zpowers u ⊔ N) = 32 := by omega
  have hT_card_eq32 : Nat.card ↥T = 32 := by omega
  have hS_card_eq : Nat.card ↥(Subgroup.zpowers u ⊔ N) = 2 ^ 5 := by
    rw [hS_card_eq32]; norm_num
  have hT_card_eq : Nat.card ↥T = 2 ^ 5 := by
    rw [hT_card_eq32]; norm_num
  have hT_eq_S : T = Subgroup.zpowers u ⊔ N :=
    (Subgroup.eq_of_le_of_card_ge hS_le_T (by omega)).symm
  refine ⟨haQ, ?_, ?_, ?_⟩
  · show T = Subgroup.zpowers u ⊔ N
    exact hT_eq_S
  · show Nat.card ↥T = 2 ^ 5
    exact hT_card_eq
  · show N ≤ Qz u
    exact hN_le_Qz

end CFSG.EvenSporadicStandard.HNRecog.Section3
