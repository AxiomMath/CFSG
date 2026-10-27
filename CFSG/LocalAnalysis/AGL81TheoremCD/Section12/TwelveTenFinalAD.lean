module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveTenFinalReduction
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveTenNine
public import CFSG.ClassicalInvolution.Q3.Q3MFOU4F9

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem IsThreeOnePlusTwo.centerIn_le_of_card_nine {D E : Subgroup G}
    (hD : IsThreeOnePlusTwo ↥D) (hED : E ≤ D) (hEcard : Nat.card E = 9) :
    CFSG.centerIn D ≤ E := by
  set E' : Subgroup ↥D := E.subgroupOf D with hE'def
  have hE'card : Nat.card E' = 9 := by
    rw [hE'def, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hED).toEquiv]
    exact hEcard
  have hE'index : E'.index = 3 := by
    have h := E'.card_mul_index
    rw [hE'card, hD.2.1] at h
    omega
  have hE'normal : E'.Normal := by
    apply Subgroup.normal_of_index_eq_minFac_card
    rw [hE'index, hD.2.1]
    norm_num
  haveI : E'.Normal := hE'normal
  have hquotcard : Nat.card (↥D ⧸ E') = 3 := by
    rw [← Subgroup.index_eq_card, hE'index]
  have hqcomm : IsMulCommutative (↥D ⧸ E') := by
    haveI : Fact (Nat.card (↥D ⧸ E')).Prime := ⟨by rw [hquotcard]; norm_num⟩
    exact (isCyclic_of_prime_card (p := 3) hquotcard).isMulCommutative
  have hcommle : _root_.commutator ↥D ≤ E' :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hqcomm
  have hcenterle : Subgroup.center ↥D ≤ E' := by
    rw [← hD.1.2.1]
    exact hcommle
  rw [CFSG.centerIn_eq_map_center]
  calc (Subgroup.center ↥D).map D.subtype
      ≤ E'.map D.subtype := Subgroup.map_mono (f := D.subtype) hcenterle
    _ = E := by rw [hE'def, Subgroup.map_subgroupOf_eq_of_le hED]

theorem twelveTenFinalA_false_of_twelveNineA {M H Q : Subgroup G} {p : ℕ}
    (hp : p.Prime) (h9 : TwelveNineA M H p Q) :
    ¬ TwelveTenFinalA M H Q p := by
  rintro ⟨E, D, _hEQ, _hE, hEcard, hΓ, hD, hDQ, hED⟩
  have hp3 : p = 3 := by
    have hdvd : p ^ 2 ∣ 27 := by
      have := Subgroup.card_dvd_of_le hED
      rwa [hEcard, hD.2.1] at this
    have hp_dvd3 : p ∣ 3 := by
      have h27 : (27 : ℕ) = 3 ^ 3 := by norm_num
      refine hp.dvd_of_dvd_pow (n := 3) ?_
      exact h27 ▸ ((dvd_pow_self p (by norm_num : 2 ≠ 0)).trans hdvd)
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hp_dvd3
  subst hp3
  have hEcard9 : Nat.card E = 9 := by
    rw [hEcard]
    norm_num
  have hZle : CFSG.centerIn D ≤ E :=
    IsThreeOnePlusTwo.centerIn_le_of_card_nine hD hED hEcard9
  have hZcard : Nat.card (CFSG.centerIn D) = 3 := IsThreeOnePlusTwo.card_centerIn hD
  have hZel : IsElemAbelian 3 (CFSG.centerIn D) := by
    rw [CFSG.centerIn_eq_map_center]
    have hcenter_el : IsElemAbelian 3 (Subgroup.center ↥D) := by
      refine ⟨inferInstance, fun x _hx => ?_⟩
      simpa using hD.2.2 x
    exact hcenter_el.map D.subtype
  have hrankZ : 1 ≤ CFSG.Open.pRank 3 (CFSG.centerIn D) := by
    have h := CFSG.SectionRank.le_pRank (p := 3) (by norm_num : 1 < 3)
      (H := CFSG.centerIn D) (E := CFSG.centerIn D) le_rfl hZel
      (k := 1) (by rw [hZcard]; norm_num)
    simpa using h
  have hNle : Subgroup.normalizer (CFSG.centerIn D : Set G) ≤
      rankThreeGamma 1 3 E := by
    change _ ≤ CFSG.Open.GLBCore 3 1 E
    unfold CFSG.Open.GLBCore
    exact le_sSup ⟨CFSG.centerIn D, hZle, hrankZ, rfl⟩
  exact (h9.center_not_le D hD hDQ) (le_trans inf_le_right (hNle.trans hΓ))

theorem not_twelveTenFinalA_of_twelveCtx_of_twelveNineA {M H Q : Subgroup G} {p : ℕ}
    (h : TwelveCtx G M p Q H) (h9 : TwelveNineA M H p Q) :
    ¬ TwelveTenFinalA M H Q p :=
  twelveTenFinalA_false_of_twelveNineA h.p_prime h9

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
