module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76RankOneClassSurvive
public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigGood3
public import CFSG.LocalAnalysis.ComponentClassification.Sol76SigExt
public import CFSG.Quasithin.Background.E1Defs

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {N K : Subgroup G}

theorem oddTwoCoreIn_le_coreActionKernel (hK : IsTwoComponentIn K N) :
    oddTwoCoreIn N ≤ coreActionKernel K := by
  rintro _ ⟨x, hx, rfl⟩
  refine R12.mem_coreActionKernel_of_mem_centralizer_image hK (mem_centralizer_iff.mpr ?_)
  rintro _ ⟨a, ha, rfl⟩
  exact R12.commute_of_mem_pCore (R12.isComponent_image hK) (Subgroup.mem_comap.mp hx)
    ⟨a, ha, rfl⟩

theorem exists_inv_mul_mem_coreActionKernel (hK : IsTwoComponentIn K N) {m : G}
    (hm : m ∈ oddTwoCoreIn N ⊔ twoLayerIn N) : ∃ k ∈ K, k⁻¹ * m ∈ coreActionKernel K := by
  have hle : oddTwoCoreIn N ⊔ twoLayerIn N ≤ K ⊔ coreActionKernel K :=
    sup_le ((oddTwoCoreIn_le_coreActionKernel hK).trans le_sup_right)
      (RankOneClass.twoLayerIn_le_sup_coreActionKernel hK)
  have hQK : coreActionKernel K ≤ normalizer (K : Set G) := fun q hq =>
    (mem_coreActionKernel.mp hq).1
  have hm' : m ∈ ((K ⊔ coreActionKernel K : Subgroup G) : Set G) := hle hm
  rw [coe_mul_of_right_le_normalizer_left K _ hQK] at hm'
  obtain ⟨k, hk, q, hq, rfl⟩ := hm'
  exact ⟨k, hk, by rwa [inv_mul_cancel_left]⟩

theorem commute_mk_of_mem_coreActionKernel (hK : IsTwoComponentIn K N) {x y : ↥N}
    (hx : (x : G) ∈ K) (hy : (y : G) ∈ coreActionKernel K) :
    Commute (QuotientGroup.mk' (pPrimeCore 2 ↥N) x) (QuotientGroup.mk' (pPrimeCore 2 ↥N) y) :=
  (mk_mul_comm_iff x y).mpr
    (FooteLit.oddCoreIn_le_of_isTwoComponentIn hK ((mem_coreActionKernel.mp hy).2 _ hx))

omit [Finite G] in
theorem mk_eq_mk_iff {x y : ↥N} :
    QuotientGroup.mk' (pPrimeCore 2 ↥N) x = QuotientGroup.mk' (pPrimeCore 2 ↥N) y ↔
      (x : G)⁻¹ * y ∈ oddCoreIn N := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  constructor
  · intro h
    exact ⟨_, h, rfl⟩
  · rintro ⟨o, ho, he⟩
    have : o = x⁻¹ * y := Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_inv]; exact he)
    rwa [← this]

@[expose] def commModSubgroup (O : Subgroup G) (x₀ : G) : Subgroup G where
  carrier := {p | p ∈ normalizer (O : Set G) ∧ p⁻¹ * x₀⁻¹ * p * x₀ ∈ O}
  mul_mem' := by
    rintro p q ⟨hp, hpx⟩ ⟨hq, hqx⟩
    refine ⟨mul_mem hp hq, ?_⟩
    have h1 : q⁻¹ * (p⁻¹ * x₀⁻¹ * p * x₀) * q⁻¹⁻¹ ∈ O :=
      (mem_normalizer_iff.mp (inv_mem hq) _).mp hpx
    have e : (p * q)⁻¹ * x₀⁻¹ * (p * q) * x₀ =
        (q⁻¹ * (p⁻¹ * x₀⁻¹ * p * x₀) * q⁻¹⁻¹) * (q⁻¹ * x₀⁻¹ * q * x₀) := by group
    rw [e]
    exact mul_mem h1 hqx
  one_mem' := ⟨one_mem _, by simp⟩
  inv_mem' := by
    rintro p ⟨hp, hpx⟩
    refine ⟨inv_mem hp, ?_⟩
    have h1 : p * (p⁻¹ * x₀⁻¹ * p * x₀)⁻¹ * p⁻¹ ∈ O :=
      (mem_normalizer_iff.mp hp _).mp (inv_mem hpx)
    have e : p⁻¹⁻¹ * x₀⁻¹ * p⁻¹ * x₀ = p * (p⁻¹ * x₀⁻¹ * p * x₀)⁻¹ * p⁻¹ := by group
    rw [e]
    exact h1

omit [Finite G] in
theorem mem_commModSubgroup_iff {O : Subgroup G} {x₀ p : G} :
    p ∈ commModSubgroup O x₀ ↔ p ∈ normalizer (O : Set G) ∧ p⁻¹ * x₀⁻¹ * p * x₀ ∈ O :=
  Iff.rfl

theorem exists_involution_mem_coset {O : Subgroup G} (hO : Odd (Nat.card O)) {x₀ : G}
    (hx₀ : x₀ ∈ normalizer (O : Set G)) (hx₀2 : x₀ ^ 2 ∈ O) (hx₀O : x₀ ∉ O) {P : Subgroup G}
    (hP : IsPGroup 2 P) (hPx : P ≤ commModSubgroup O x₀) :
    ∃ x : G, orderOf x = 2 ∧ x₀⁻¹ * x ∈ O ∧ ∀ p ∈ P, p * x = x * p := by
  set Y := zpowers x₀ ⊔ O with hY
  have hYcoe : (Y : Set G) = (zpowers x₀ : Set G) * (O : Set G) :=
    coe_mul_of_left_le_normalizer_right _ _ (zpowers_le.mpr hx₀)
  have hx₀Y : x₀ ∈ Y := mem_sup_left (mem_zpowers x₀)
  have hconj : ∀ p ∈ P, ∀ y ∈ Y, p * y * p⁻¹ ∈ Y := by
    intro p hp y hy
    obtain ⟨hpO, -⟩ := (mem_commModSubgroup_iff.mp (hPx hp))
    obtain ⟨-, hpx'⟩ := (mem_commModSubgroup_iff.mp (hPx (inv_mem hp)))
    have hc : p * x₀ * p⁻¹ ∈ Y := by
      have h1 : x₀⁻¹ * (p * x₀ * p⁻¹) ∈ O := by
        have e : x₀⁻¹ * (p * x₀ * p⁻¹) = (p⁻¹⁻¹ * x₀⁻¹ * p⁻¹ * x₀)⁻¹ := by group
        rw [e]
        exact inv_mem hpx'
      have e : p * x₀ * p⁻¹ = x₀ * (x₀⁻¹ * (p * x₀ * p⁻¹)) := by group
      rw [e]
      exact mul_mem hx₀Y (mem_sup_right h1)
    have hmap : Y.map (MulAut.conj p).toMonoidHom ≤ Y := by
      rw [hY, Subgroup.map_sup, MonoidHom.map_zpowers]
      refine sup_le (zpowers_le.mpr ?_) ?_
      · simpa [MulAut.conj_apply] using hc
      · rw [show O.map (MulAut.conj p).toMonoidHom = O from mem_normalizer_iff_map_conj_eq.mp hpO]
        exact le_sup_right
    exact hmap ⟨y, hy, by simp [MulAut.conj_apply]⟩
  have hPY : P ≤ normalizer (Y : Set G) := fun p hp => mem_normalizer_iff.mpr fun y =>
    ⟨fun hy => hconj p hp y hy, fun hy => by
      have h := hconj p⁻¹ (inv_mem hp) _ hy
      rwa [show p⁻¹ * (p * y * p⁻¹) * p⁻¹⁻¹ = y by group] at h⟩
  have hY2 : Even (Nat.card Y) := by
    have hodd : ¬ Odd (orderOf x₀) := by
      rintro ⟨j, hj⟩
      apply hx₀O
      have e : x₀ = (x₀ ^ 2) ^ (j + 1) := by
        rw [← pow_mul]
        calc x₀ = x₀ ^ orderOf x₀ * x₀ := by rw [pow_orderOf_eq_one, one_mul]
          _ = x₀ ^ (orderOf x₀ + 1) := (pow_succ x₀ _).symm
          _ = x₀ ^ (2 * (j + 1)) := by rw [hj]; congr 1
      rw [e]
      exact pow_mem hx₀2 _
    have hdvd : orderOf x₀ ∣ Nat.card Y := Y.orderOf_dvd_natCard hx₀Y
    exact even_iff_two_dvd.mpr ((even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)).trans hdvd)
  obtain ⟨x, hxY, hx2, hxP⟩ :=
    CFSG.GroupTheory.exists_involution_commute_of_isPGroup_le_normalizer hP hPY hY2
  refine ⟨x, hx2, ?_, hxP⟩
  have hxY' : x ∈ (zpowers x₀ : Set G) * (O : Set G) := by rw [← hYcoe]; exact hxY
  obtain ⟨_, ⟨i, rfl⟩, o, ho, rfl⟩ := hxY'
  have h2z : x₀ ^ (2 : ℤ) ∈ O := by
    rw [zpow_two, ← sq]
    exact hx₀2
  have hev : ∀ n : ℤ, x₀ ^ (2 * n) ∈ O := fun n => by
    rw [zpow_mul]
    exact zpow_mem h2z n
  obtain ⟨n, hn | hn⟩ := Int.even_or_odd' i
  · exfalso
    have hmem : x₀ ^ i * o ∈ O := by
      rw [hn]
      exact mul_mem (hev n) ho
    have hdvd := O.orderOf_dvd_natCard hmem
    rw [hx2] at hdvd
    exact (Nat.not_even_iff_odd.mpr hO) (even_iff_two_dvd.mpr hdvd)
  · have e : x₀⁻¹ * (x₀ ^ i * o) = x₀ ^ (2 * n) * o := by
      rw [hn]
      group
    rw [e]
    exact mul_mem (hev n) ho

theorem exists_not_mem_sup_of_card_eight (hK : K ∈ kStarComponents N)
    (h2K : CFSG.Open.pRank 2 K ≤ 2) {A : Subgroup G} (hA2 : ∀ x ∈ A, x ^ 2 = 1)
    (hA8 : Nat.card A = 8) : ∃ a ∈ A, a ∉ K ⊔ oddCoreIn N := by
  by_contra h
  push Not at h
  have hKO : K ≤ normalizer (oddCoreIn N : Set G) :=
    (le_of_mem_kStarComponents hK).trans (le_normalizer_oddCoreIn N)
  have hOodd : Odd (Nat.card (oddCoreIn N)) :=
    Nat.coprime_two_left.mp (coprime_card_oddCoreIn N)
  have hAKO : A ≤ K ⊔ oddCoreIn N := fun a ha => h a ha
  obtain ⟨m, -, hm⟩ := exists_conj_le_of_sup_odd le_sup_left hKO hOodd rfl hAKO
    (isPGroup_of_sq_eq_one hA2)
  have hE : CFSG.Open.IsElemAbelian 2 (A.map (MulAut.conj m).toMonoidHom) :=
    SectionRank.isElemAbelian_map ⟨FooteLit.isMulCommutative_of_sq_eq_one hA2, hA2⟩ _
  have hcard : Nat.card (A.map (MulAut.conj m).toMonoidHom) = 2 ^ 3 := by
    rw [card_map_of_injective (MulAut.conj m).injective, hA8]
    norm_num
  have h3 := SectionRank.le_pRank (by norm_num) hm hE hcard
  omega

open scoped commutatorElement in
theorem oddTwoCoreIn_sup_twoLayerIn_le_of_components_and_centralizer
    {N J K S H : Subgroup G}
    (hJ : IsTwoComponentIn J N) (hK : IsTwoComponentIn K N)
    (hS : IsPGroup 2 S) (hSJK : S ≤ J ⊔ K)
    (hJH : J ≤ H) (hKH : K ≤ H)
    (hOH : oddCoreIn N ≤ H)
    (hCH : N ⊓ centralizer (S : Set G) ≤ H) :
    oddTwoCoreIn N ⊔ twoLayerIn N ≤ H := by
  set D : Subgroup G := oddTwoCoreIn N with hD
  have absorb : ∀ L : Subgroup G, L ≤ N → oddCoreIn L ≤ oddCoreIn N →
      S ≤ coreActionKernel L → L ≤ H := by
    intro L hLN hLO hSL
    refine (Sol76.inf_centralizer_sup_oddCoreIn_eq (L := L) hS hSL).symm.le.trans
      (sup_le ?_ (hLO.trans hOH))
    rw [inf_comm]
    exact (inf_le_inf_left _ hLN).trans (by rwa [inf_comm] at hCH)
  have hDN : D ≤ N := by
    rw [hD]
    exact Subgroup.map_subtype_le _
  have hND : N ≤ normalizer (D : Set G) := by
    rw [hD]
    exact Sol76.le_normalizer_map_subtype'
      ((pCore 2 (↥N ⧸ pPrimeCore 2 ↥N)).comap (QuotientGroup.mk' (pPrimeCore 2 ↥N)))
  have hOD : oddCoreIn N ≤ D := by
    have hker : pPrimeCore 2 ↥N ≤
        (pCore 2 (↥N ⧸ pPrimeCore 2 ↥N)).comap (QuotientGroup.mk' (pPrimeCore 2 ↥N)) := by
      have h := MonoidHom.ker_le_comap (QuotientGroup.mk' (pPrimeCore 2 ↥N))
        (pCore 2 (↥N ⧸ pPrimeCore 2 ↥N))
      rwa [QuotientGroup.ker_mk'] at h
    rw [hD]
    exact Subgroup.map_mono hker
  have hODN : oddCoreIn D ≤ oddCoreIn N := oddCoreIn_le_of_le_normalizer hDN hND
  have hOND : oddCoreIn N ≤ oddCoreIn D := by
    have h := Sol76.oddCoreIn_inf_le (D := D) (N := N) hDN
    rwa [inf_of_le_left hOD] at h
  have kernel_of_comm : ∀ {A : Subgroup G}, A ≤ normalizer (D : Set G) →
      ⁅A, D⁆ ≤ oddCoreIn D → A ≤ coreActionKernel D := by
    intro A hAN hAD a ha
    refine mem_coreActionKernel.mpr ⟨hAN ha, fun d hd => ?_⟩
    have hDA : ⁅D, A⁆ ≤ oddCoreIn D := (Subgroup.commutator_comm D A).le.trans hAD
    have h := hDA (Subgroup.commutator_mem_commutator (D.inv_mem hd) (A.inv_mem ha))
    simpa only [commutatorElement_def, inv_inv, oddCoreIn] using h
  have hJD : J ≤ coreActionKernel D := by
    refine kernel_of_comm (hJ.1.trans hND) ?_
    have h1 : ⁅J, D⁆ ≤ oddCoreIn J :=
      Sol76.Sig.commutator_le_oddCoreIn_of_le_coreActionKernel
        (oddTwoCoreIn_le_coreActionKernel hJ)
    exact h1.trans ((oddCoreIn_le_of_isTwoComponentIn hJ).trans hOND)
  have hKD : K ≤ coreActionKernel D := by
    refine kernel_of_comm (hK.1.trans hND) ?_
    have h1 : ⁅K, D⁆ ≤ oddCoreIn K :=
      Sol76.Sig.commutator_le_oddCoreIn_of_le_coreActionKernel
        (oddTwoCoreIn_le_coreActionKernel hK)
    exact h1.trans ((oddCoreIn_le_of_isTwoComponentIn hK).trans hOND)
  have hSD : S ≤ coreActionKernel D := hSJK.trans (sup_le hJD hKD)
  have hDH : D ≤ H := absorb D hDN hODN hSD
  have hLayer : twoLayerIn N ≤ H := by
    refine Sol76T13.twoLayerIn_le_of_forall ?_
    intro M hM
    by_cases hMJ : M = J
    · simpa [hMJ] using hJH
    by_cases hMK : M = K
    · simpa [hMK] using hKH
    · have hJM : J ≤ coreActionKernel M :=
        GSThmB.B5a.le_coreActionKernel_of_ne hM.1 hJ.1 hM.2 hJ.2 hMJ
      have hKM : K ≤ coreActionKernel M :=
        GSThmB.B5a.le_coreActionKernel_of_ne hM.1 hK.1 hM.2 hK.2 hMK
      exact absorb M hM.1 (oddCoreIn_le_of_isTwoComponentIn hM)
        (hSJK.trans (sup_le hJM hKM))
  simpa only [hD] using sup_le hDH hLayer

end CFSG.ComponentClassification.Sol76.Sig
