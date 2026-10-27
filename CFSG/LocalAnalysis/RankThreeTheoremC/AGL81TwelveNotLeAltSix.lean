module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeDefs
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFamAltMaxThree
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.AutA6Three
import CFSG.LargeExtraspecial.S45QSylow

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe

namespace AltSix

open CFSG.AGLEmbedding CFSG.AGLEmbedding.KFactProofs.SmallIdent

variable {K : Type} [Group K] [Finite K]

theorem card_centralizer_le_nine (e : K ≃* alternatingGroup (Fin 6)) {a : K}
    (ha : orderOf a = 3) : Nat.card (Subgroup.centralizer ({a} : Set K)) ≤ 9 := by
  have h9 := CFSG.EvenSporadicStandard.HSStd.Zassenhaus.card_centralizer_of_orderOf_eq_three
    (x := e a) (by rw [MulEquiv.orderOf_eq]; exact ha)
  rw [← h9]
  refine Nat.card_le_card_of_injective
    (fun x => ⟨e x.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩) ?_
  · rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp x.2]
  · intro x y hxy
    exact Subtype.ext (e.injective (congrArg Subtype.val hxy))

theorem isSimpleGroup_of_isAltTwoP (hK : IsAltTwoP 3 K) : IsSimpleGroup K := by
  obtain ⟨e⟩ := hK
  exact e.symm.isSimpleGroup_congr.1 (alternatingGroup.isSimpleGroup (by simp))

theorem card_le_sixty (hK : IsAltTwoP 3 K) {U : Subgroup K} (hU : U ≠ ⊤) : Nat.card U ≤ 60 := by
  have hc : Nat.card K = 360 := card_of_isAltTwoP_three hK
  haveI := isSimpleGroup_of_isAltTwoP hK
  have hdvd := CFSG.LargeExtraspecial.S45Q.card_dvd_factorial_index hU
  rw [hc] at hdvd
  have h6 : 6 ≤ U.index := by
    by_contra hlt
    push Not at hlt
    generalize U.index = j at hdvd hlt
    interval_cases j <;> simp [Nat.factorial] at hdvd
  have hmul := U.index_mul_card
  rw [hc] at hmul
  nlinarith

theorem inf_ne_bot_of_card {U E E' : Subgroup K} (hE : Nat.card E = 9) (hE' : Nat.card E' = 9)
    (hEU : E ≤ U) (hEU' : E' ≤ U) (hU : Nat.card U ≤ 60) : E ⊓ E' ≠ ⊥ := by
  intro h
  have h1 := Subgroup.relIndex_inf_le (H := E) (K := E') (L := U)
  rw [h, Subgroup.relIndex_bot_left] at h1
  have h2 := Subgroup.relIndex_mul_card E U
  have h3 := Subgroup.relIndex_mul_card E' U
  rw [inf_eq_left.mpr hEU, hE] at h2
  rw [inf_eq_left.mpr hEU', hE'] at h3
  have hpos : 0 < Nat.card U := Nat.card_pos
  nlinarith

theorem le_centralizer_of_mem (hK : IsAltTwoP 3 K) (E : Sylow 3 K) {a : K}
    (ha : a ∈ (E : Subgroup K)) : (E : Subgroup K) ≤ Subgroup.centralizer ({a} : Set K) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomm : IsMulCommutative (E : Subgroup K) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3)
      (sylowSq_of_isAltTwoP Nat.prime_three (by norm_num) hK E)
  exact (Subgroup.le_centralizer_iff_isMulCommutative.mpr hcomm).trans
    (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha))

theorem eq_of_inf_ne_bot (hK : IsAltTwoP 3 K) {E E' : Sylow 3 K}
    (h : (E : Subgroup K) ⊓ E' ≠ ⊥) : E = E' := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := hK
  have hE : Nat.card (E : Subgroup K) = 3 ^ 2 := sylowSq_of_isAltTwoP Nat.prime_three (by norm_num)
    ⟨e⟩ E
  have hE' : Nat.card (E' : Subgroup K) = 3 ^ 2 :=
    sylowSq_of_isAltTwoP Nat.prime_three (by norm_num) ⟨e⟩ E'
  have hdvd : Nat.card ↥((E : Subgroup K) ⊓ E') ∣ 3 ^ 2 :=
    hE ▸ Subgroup.card_dvd_of_le inf_le_left
  have h3 : 3 ∣ Nat.card ↥((E : Subgroup K) ⊓ E') := by
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    rcases i with _ | i
    · exact absurd (Subgroup.card_eq_one.1 (by simpa using hi)) h
    · rw [hi]
      exact dvd_pow_self 3 (Nat.succ_ne_zero i)
  obtain ⟨⟨a, haI⟩, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥((E : Subgroup K) ⊓ E')) 3 h3
  have ha3 : orderOf a = 3 := by rwa [Subgroup.orderOf_mk] at hx
  have haE := (Subgroup.mem_inf.mp haI).1
  have haE' := (Subgroup.mem_inf.mp haI).2
  have hC := card_centralizer_le_nine e ha3
  have h1 := Subgroup.eq_of_le_of_card_ge (le_centralizer_of_mem ⟨e⟩ E haE)
    (by rw [hE]; simpa using hC)
  have h2 := Subgroup.eq_of_le_of_card_ge (le_centralizer_of_mem ⟨e⟩ E' haE')
    (by rw [hE']; simpa using hC)
  exact Sylow.ext (h1.trans h2.symm)

theorem le_normalizer_of_le (hK : IsAltTwoP 3 K) (E : Sylow 3 K) {U : Subgroup K}
    (hEU : (E : Subgroup K) ≤ U) (hU : U ≠ ⊤) :
    U ≤ Subgroup.normalizer ((E : Subgroup K) : Set K) := by
  intro u hu
  refine Sylow.smul_eq_iff_mem_normalizer.mp (eq_of_inf_ne_bot hK ?_)
  refine inf_ne_bot_of_card (U := U) ?_ ?_ (Sylow.smul_le hEU ⟨u, hu⟩) hEU
    (card_le_sixty hK hU)
  · simpa using sylowSq_of_isAltTwoP Nat.prime_three (by norm_num) hK (u • E)
  · simpa using sylowSq_of_isAltTwoP Nat.prime_three (by norm_num) hK E

theorem map_conj_ne_of_orderOf_eq_four (hK : IsAltTwoP 3 K) (E : Sylow 3 K) {k : K}
    (hk4 : orderOf k = 4) {Z : Subgroup K} (hZE : Z ≤ E) (hZ3 : Nat.card Z = 3) :
    Z.map (MulAut.conj k).toMonoidHom ≠ Z := by
  intro hmap
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨a, haZ⟩, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥Z) 3 (by rw [hZ3])
  have ha3 : orderOf a = 3 := by rwa [Subgroup.orderOf_mk] at hx
  have ha1 : a ^ 3 = 1 := by rw [← ha3]; exact pow_orderOf_eq_one a
  have hZ : Z = Subgroup.zpowers a :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr haZ)
      (by rw [Nat.card_zpowers, ha3, hZ3])).symm
  have hb : k * a * k⁻¹ ∈ Z := by
    have h := Subgroup.mem_map_of_mem (MulAut.conj k).toMonoidHom haZ
    rw [hmap] at h
    simpa [MulAut.conj_apply] using h
  have hcomm : k * k * a = a * (k * k) := by
    rw [hZ] at hb
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hmod : a ^ i = a ^ (i % 3) := zpow_eq_zpow_emod' i ha1
    rcases (by omega : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2) with h0 | h1 | h2
    · exfalso
      rw [h0, zpow_zero] at hmod
      have h : k * a * k⁻¹ = 1 := hi.symm.trans hmod
      have h' : a = 1 := by simpa using h
      exact absurd ha3 (by rw [h', orderOf_one]; norm_num)
    · rw [h1, zpow_one] at hmod
      have hka : k * a = a * k := by
        rw [← mul_inv_eq_iff_eq_mul]
        exact hi.symm.trans hmod
      calc k * k * a = k * (k * a) := mul_assoc _ _ _
        _ = k * (a * k) := by rw [hka]
        _ = (k * a) * k := (mul_assoc _ _ _).symm
        _ = a * k * k := by rw [hka]
        _ = a * (k * k) := mul_assoc _ _ _
    · rw [h2] at hmod
      have hka : k * a * k⁻¹ = a ^ 2 := by
        have := hi.symm.trans hmod
        simpa using this
      have hka2 : k * a ^ 2 * k⁻¹ = a := by
        have h : k * a ^ 2 * k⁻¹ = (k * a * k⁻¹) ^ 2 := conj_pow.symm
        rw [h, hka, ← pow_mul]
        calc a ^ (2 * 2) = a ^ 3 * a := by rw [← pow_succ]
          _ = a := by rw [ha1, one_mul]
      have e1 : k * a = a ^ 2 * k := by
        rw [← mul_inv_eq_iff_eq_mul]
        exact hka
      have e2 : k * a ^ 2 = a * k := by
        rw [← mul_inv_eq_iff_eq_mul]
        exact hka2
      calc k * k * a = k * (k * a) := mul_assoc _ _ _
        _ = k * (a ^ 2 * k) := by rw [e1]
        _ = (k * a ^ 2) * k := (mul_assoc _ _ _).symm
        _ = a * k * k := by rw [e2]
        _ = a * (k * k) := mul_assoc _ _ _
  obtain ⟨e⟩ := hK
  have hE9 : Nat.card (E : Subgroup K) = 9 := by
    simpa using sylowSq_of_isAltTwoP Nat.prime_three (by norm_num) ⟨e⟩ E
  have hEC := le_centralizer_of_mem ⟨e⟩ E (hZE haZ)
  have hEeq := Subgroup.eq_of_le_of_card_ge hEC
    (by rw [hE9]; exact card_centralizer_le_nine e ha3)
  have hkk : k * k ∈ (E : Subgroup K) := by
    rw [hEeq]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm
  have h2 : orderOf (k * k) = 2 := by
    rw [← sq, orderOf_pow' k two_ne_zero, hk4]
    norm_num
  have hdvd := Subgroup.orderOf_dvd_natCard (E : Subgroup K) hkk
  rw [h2, hE9] at hdvd
  omega

theorem exists_two_element_moving (hK : IsAltTwoP 3 K) (E : Sylow 3 K) :
    ∃ t ∈ Subgroup.normalizer ((E : Subgroup K) : Set K), (∃ k : ℕ, t ^ 2 ^ k = 1) ∧
      ∀ Z : Subgroup K, Z ≤ E → Nat.card Z = 3 → Z.map (MulAut.conj t).toMonoidHom ≠ Z := by
  obtain ⟨k, hkN, hk4⟩ := exists_order_four_normalizer_of_isAltTwoP_three hK E
  refine ⟨k, hkN, ⟨2, ?_⟩, fun Z hZE hZ3 => map_conj_ne_of_orderOf_eq_four hK E hk4 hZE hZ3⟩
  rw [show (2 : ℕ) ^ 2 = orderOf k by rw [hk4]; norm_num]
  exact pow_orderOf_eq_one k

theorem card_normalizer (hK : IsAltTwoP 3 K) (E : Sylow 3 K) :
    Nat.card (Subgroup.normalizer ((E : Subgroup K) : Set K)) = 36 := by
  haveI := isSimpleGroup_of_isAltTwoP hK
  set N := Subgroup.normalizer ((E : Subgroup K) : Set K) with hN
  have hE9 : Nat.card (E : Subgroup K) = 9 := by
    simpa using sylowSq_of_isAltTwoP Nat.prime_three (by norm_num) hK E
  have hNtop : N ≠ ⊤ := by
    intro h
    haveI : (E : Subgroup K).Normal := Subgroup.normalizer_eq_top_iff.mp h
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (E : Subgroup K) with h1 | h1
    · rw [h1, Subgroup.card_bot] at hE9
      omega
    · rw [h1, Subgroup.card_top, card_of_isAltTwoP_three hK] at hE9
      omega
  obtain ⟨k, hkN, hk4⟩ := exists_order_four_normalizer_of_isAltTwoP_three hK E
  have h9 : 9 ∣ Nat.card N :=
    hE9 ▸ Subgroup.card_dvd_of_le (Subgroup.le_normalizer : (E : Subgroup K) ≤ N)
  have h4 : 4 ∣ Nat.card N := by
    have : orderOf (⟨k, hkN⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
    rwa [Subgroup.orderOf_mk, hk4] at this
  have h36 : 36 ∣ Nat.card N :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 9 4) h9 h4
  have hle := card_le_sixty hK hNtop
  have hpos : 0 < Nat.card N := Nat.card_pos
  omega

theorem isSolvable_normalizer (hK : IsAltTwoP 3 K) (E : Sylow 3 K) :
    Group.IsSolvable ↥(Subgroup.normalizer ((E : Subgroup K) : Set K)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := Subgroup.normalizer ((E : Subgroup K) : Set K) with hN
  have hEN : (E : Subgroup K) ≤ N := Subgroup.le_normalizer
  have hE9 : Nat.card (E : Subgroup K) = 3 ^ 2 :=
    sylowSq_of_isAltTwoP Nat.prime_three (by norm_num) hK E
  haveI : IsMulCommutative ↥(E : Subgroup K) := IsPGroup.isMulCommutative_of_card_eq_prime_sq hE9
  haveI : Group.IsSolvable ↥((E : Subgroup K).subgroupOf N) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hEN).toMonoidHom) (MulEquiv.injective _)
  have hq : Nat.card (N ⧸ (E : Subgroup K).subgroupOf N) = 2 ^ 2 := by
    have h1 := ((E : Subgroup K).subgroupOf N).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEN).toEquiv, hE9, card_normalizer hK E]
      at h1
    rw [← Subgroup.index_eq_card]
    omega
  haveI : IsMulCommutative (N ⧸ (E : Subgroup K).subgroupOf N) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq hq
  exact Group.isSolvable_of_subgroup_quotient ((E : Subgroup K).subgroupOf N)

end AltSix

theorem kFactTwelveNotLeAltSix_holds : KFactTwelveNotLeAltSix := by
  intro K _ _ hA E
  exact ⟨fun U hEU hU => AltSix.le_normalizer_of_le hA E hEU hU,
    AltSix.isSolvable_normalizer hA E, AltSix.exists_two_element_moving hA E⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe
