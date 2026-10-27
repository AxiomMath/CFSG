module

public import CFSG.FeitThompson.Local.CentralProductPlaneCentralizer
public import CFSG.FeitThompson.Local.SmallRankLineInMaximalPlane
import CFSG.FeitThompson.Local.CriticalEnlargementCharacteristic
import CFSG.FeitThompson.Local.NormalPlaneNotMaximalHighRank
import CFSG.FeitThompson.Local.NormalSubgroupCentralPrimeTorsion

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Pointwise Subgroup

variable {p n : ℕ} {R : Type*} [Group R] {A S Y H : Subgroup R}

theorem inf_centralizer_eq_map_center_subtype (H : Subgroup R) :
    H ⊓ centralizer (H : Set R) = (center H).map H.subtype :=
  (map_center_subtype H).symm

theorem isMulCommutative_centralizer_of_isInternalDirectProduct (hp : p.Prime)
    (hS : Nat.card S = p) (hY : IsCyclic Y)
    (hC : IsInternalDirectProduct (centralizer (S : Set R)) S Y) :
    IsMulCommutative (centralizer (S : Set R)) := by
  have := hY
  have hSea : IsElementaryAbelian p S := IsElementaryAbelian.of_natCard_eq_prime hp hS
  have hcl : centralizer (S : Set R) = Subgroup.closure ((S : Set R) ∪ (Y : Set R)) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
    exact hC.sup_eq.symm
  rw [hcl]
  refine Subgroup.isMulCommutative_closure ?_
  rintro a (ha | ha) b (hb | hb) -
  · exact hSea.mul_comm ha hb
  · exact hC.commute ha hb
  · exact (hC.commute hb ha).symm
  · exact setLike_mul_comm (s := Y) ha hb

theorem le_omega1Subgroup_centralizer_self (hp : p.Prime) (hS : Nat.card S = p) :
    S ≤ omega1Subgroup p (centralizer (S : Set R)) := by
  have hSea : IsElementaryAbelian p S := IsElementaryAbelian.of_natCard_eq_prime hp hS
  exact fun x hx => mem_omega1Subgroup (hSea.le_centralizer le_rfl hx) (hSea.pow_eq_one hx)

theorem natCard_omega1Subgroup_centralizer_le_sq [Finite R] (hp : p.Prime) (hS : Nat.card S = p)
    (hY : IsCyclic Y) (hC : IsInternalDirectProduct (centralizer (S : Set R)) S Y) :
    Nat.card (omega1Subgroup p (centralizer (S : Set R))) ≤ p ^ 2 := by
  have hSea : IsElementaryAbelian p S := IsElementaryAbelian.of_natCard_eq_prime hp hS
  have hCcomm := isMulCommutative_centralizer_of_isInternalDirectProduct hp hS hY hC
  set T := omega1Subgroup p (centralizer (S : Set R)) with hTdef
  set W := T ⊓ Y with hWdef
  have hTmem : ∀ x : R, x ∈ T ↔ x ∈ centralizer (S : Set R) ∧ x ^ p = 1 := fun _ =>
    mem_omega1Subgroup_iff_of_isMulCommutative hCcomm
  have := hY
  have : IsCyclic W := isCyclic_of_injective (Subgroup.inclusion (inf_le_right : W ≤ Y))
    (Subgroup.inclusion_injective _)
  have hWcard : Nat.card W ∣ p := by
    rw [← IsCyclic.exponent_eq_card]
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun g => ?_
    have h := ((hTmem g.1).1 (Subgroup.mem_inf.1 g.2).1).2
    exact Subtype.ext (by simpa using h)
  have hsub : (T : Set R) ⊆ (S : Set R) * (W : Set R) := by
    intro x hx
    obtain ⟨hxC, hxp⟩ := (hTmem x).1 hx
    obtain ⟨s, hs, y, hy, rfl⟩ : x ∈ (S : Set R) * (Y : Set R) :=
      hC.coe_eq_mul ▸ (hxC : x ∈ ((centralizer (S : Set R)) : Set R))
    have hcomm : Commute s y := hC.commute hs hy
    have hyp : y ^ p = 1 := by
      rw [hcomm.mul_pow, hSea.pow_eq_one hs, one_mul] at hxp; exact hxp
    exact ⟨s, hs, y, Subgroup.mem_inf.2 ⟨(hTmem y).2 ⟨hC.right_le hy, hyp⟩, hy⟩, rfl⟩
  have hle : Nat.card T ≤ Nat.card ((S : Set R) * (W : Set R)) :=
    Nat.card_le_card_of_injective (Set.inclusion hsub) (Set.inclusion_injective hsub)
  have hdvd : Nat.card ((S : Set R) * (W : Set R)) ∣ Nat.card S * Nat.card W :=
    ⟨Nat.card (S ⊓ W : Subgroup R), (natCard_mul_mul_natCard_inf S W).symm⟩
  have hpos : 0 < Nat.card S * Nat.card W := by
    rw [hS]; exact Nat.mul_pos hp.pos Nat.card_pos
  calc Nat.card T ≤ Nat.card ((S : Set R) * (W : Set R)) := hle
    _ ≤ Nat.card S * Nat.card W := Nat.le_of_dvd hpos hdvd
    _ ≤ p * p := by
        rw [hS]; exact Nat.mul_le_mul_left _ (Nat.le_of_dvd hp.pos hWcard)
    _ = p ^ 2 := (sq p).symm

theorem natCard_le_sq_of_isElementaryAbelian_le_centralizer [Finite R] (hp : p.Prime)
    (hS : Nat.card S = p) (hY : IsCyclic Y)
    (hC : IsInternalDirectProduct (centralizer (S : Set R)) S Y)
    (hA : IsElementaryAbelian p A) (hAC : A ≤ centralizer (S : Set R)) :
    Nat.card A ≤ p ^ 2 :=
  le_trans (Subgroup.card_le_of_le fun _ hx => mem_omega1Subgroup (hAC hx) (hA.pow_eq_one hx))
    (natCard_omega1Subgroup_centralizer_le_sq hp hS hY hC)

theorem exists_isElementaryAbelian_cube_le_natCard [Finite R] (hp : p.Prime)
    (hrank : 3 ≤ elementaryAbelianPRank p R) :
    ∃ A : Subgroup R, IsElementaryAbelian p A ∧ p ^ 3 ≤ Nat.card A := by
  obtain ⟨A, hcomm, hexp, hAcard⟩ := (mem_elementaryAbelianRanks_iff_exists_subgroup hp).1
    (elementaryAbelianPRank_mem_elementaryAbelianRanks (X := R) (p := p) hp.one_lt)
  exact ⟨A, isElementaryAbelian_iff.2 ⟨hcomm, hexp⟩, by
    rw [hAcard]; exact Nat.pow_le_pow_right hp.pos hrank⟩

theorem le_center_of_normal_of_natCard_eq_prime (hp : p.Prime) (hcard : Nat.card R = p ^ n)
    [S.Normal] (hS : Nat.card S = p) : S ≤ center R := by
  have hne : S ⊓ center R ≠ ⊥ := inf_center_ne_bot S hp hcard
    (fun h => by rw [h, Subgroup.card_bot] at hS; exact hp.one_lt.ne hS)
  have hfin : Finite R := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.ne_zero)
  have hdvd : Nat.card (S ⊓ center R : Subgroup R) ∣ p := hS ▸ Subgroup.card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime hp).1 hdvd with h1 | hpp
  · exact absurd (Subgroup.card_eq_one.1 h1) hne
  · exact inf_eq_left.1 (Subgroup.eq_of_le_of_card_ge (inf_le_left (b := center R))
      (by rw [hS, hpp]))

theorem centralizer_ne_top [Finite R] (hp : p.Prime) (hrank : 3 ≤ elementaryAbelianPRank p R)
    (hS : Nat.card S = p) (hY : IsCyclic Y)
    (hC : IsInternalDirectProduct (centralizer (S : Set R)) S Y) :
    centralizer (S : Set R) ≠ ⊤ := by
  intro htop
  obtain ⟨A, hAea, hAcard⟩ := exists_isElementaryAbelian_cube_le_natCard hp hrank
  have h2 : Nat.card A ≤ p ^ 2 := natCard_le_sq_of_isElementaryAbelian_le_centralizer hp hS hY hC
    hAea (by rw [htop]; exact le_top)
  have := (Nat.pow_le_pow_iff_right hp.one_lt).1 (hAcard.trans h2)
  omega

theorem not_le_of_normal_of_pow_eq_one (hp : p.Prime) (hodd : Odd p) (hcard : Nat.card R = p ^ n)
    (hrank : 3 ≤ elementaryAbelianPRank p R) (hS : Nat.card S = p) (hY : IsCyclic Y)
    (hC : IsInternalDirectProduct (centralizer (S : Set R)) S Y) [H.Normal]
    (hHexp : ∀ h ∈ H, h ^ p = 1) (hHcomm : ⁅(⊤ : Subgroup R), H⁆ ≤ H ⊓ centralizer (H : Set R)) :
    ¬ S ≤ H := by
  intro hSH
  have hfin : Finite R := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.ne_zero)
  have hSea : IsElementaryAbelian p S := IsElementaryAbelian.of_natCard_eq_prime hp hS
  set ZH := H ⊓ centralizer (H : Set R) with hZHdef
  have hZHnormal : ZH.Normal := inferInstance
  have hZHea : IsElementaryAbelian p ZH :=
    isElementaryAbelian_iff.2 ⟨IsMulCommutative.of_setLike_mul_comm fun a ha b hb =>
      ((mem_centralizer_iff.1 (mem_inf.1 hb).2) a (mem_inf.1 ha).1),
      fun x hx => hHexp x (mem_inf.1 hx).1⟩
  have hScZH : S ≤ centralizer (ZH : Set R) := fun s hs =>
    mem_centralizer_iff.2 fun z hz => ((mem_centralizer_iff.1 (mem_inf.1 hz).2) s (hSH hs)).symm
  set U := S ⊔ ZH with hUdef
  have hUea : IsElementaryAbelian p U := hSea.sup_of_le_centralizer hZHea hScZH
  have hUnormal : U.Normal := by
    refine commutator_top_left_le_iff.1 ?_
    refine le_trans (commutator_top_sup_le (N := ZH) ?_ ?_) le_sup_right
    · exact le_trans (commutator_mono le_rfl hSH) hHcomm
    · exact commutator_top_left_le_iff.2 hZHnormal
  have hUC : U ≤ centralizer (S : Set R) :=
    sup_le (hSea.le_centralizer le_rfl) (fun z hz => mem_centralizer_iff.2 fun s hs =>
      (mem_centralizer_iff.1 (mem_inf.1 hz).2) s (hSH hs))
  have hUle : Nat.card U ≤ p ^ 2 :=
    natCard_le_sq_of_isElementaryAbelian_le_centralizer hp hS hY hC hUea hUC
  have hSU : S ≤ U := le_sup_left
  obtain ⟨k, hkn, hk⟩ := (Nat.dvd_prime_pow hp).1
    (hcard ▸ Subgroup.card_subgroup_dvd_card U : Nat.card U ∣ p ^ n)
  have hk1 : 1 ≤ k := by
    have h : p ^ 1 ≤ p ^ k := by
      rw [pow_one, ← hk]; exact hS ▸ Subgroup.card_le_of_le hSU
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 h
  have hk2 : k ≤ 2 := (Nat.pow_le_pow_iff_right hp.one_lt).1 (hk ▸ hUle)
  interval_cases k
  ·
    have hUS : U = S := (Subgroup.eq_of_le_of_card_ge hSU (by rw [hk, hS, pow_one])).symm
    have : S.Normal := hUS ▸ hUnormal
    have hSZ : S ≤ center R := le_center_of_normal_of_natCard_eq_prime hp hcard hS
    exact centralizer_ne_top hp hrank hS hY hC (centralizer_eq_top_iff_subset.2 hSZ)
  ·
    have := hUnormal
    obtain ⟨D, hDnormal, hDea, hUD⟩ :=
      exists_normal_isElementaryAbelian_gt_of_natCard_eq_sq hp hodd hcard hrank hUea hk
    have hDC : D ≤ centralizer (S : Set R) := hDea.le_centralizer (hSU.trans hUD.le)
    have hDle : Nat.card D ≤ p ^ 2 :=
      natCard_le_sq_of_isElementaryAbelian_le_centralizer hp hS hY hC hDea hDC
    exact absurd (Subgroup.eq_of_le_of_card_ge hUD.le (by rw [hk]; exact hDle)) hUD.ne

theorem inf_eq_bot_of_normal_of_pow_eq_one (hp : p.Prime) (hodd : Odd p)
    (hcard : Nat.card R = p ^ n) (hrank : 3 ≤ elementaryAbelianPRank p R) (hS : Nat.card S = p)
    (hY : IsCyclic Y) (hC : IsInternalDirectProduct (centralizer (S : Set R)) S Y) [H.Normal]
    (hHexp : ∀ h ∈ H, h ^ p = 1) (hHcomm : ⁅(⊤ : Subgroup R), H⁆ ≤ H ⊓ centralizer (H : Set R)) :
    S ⊓ H = ⊥ := by
  have hfin : Finite R := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.ne_zero)
  have hdvd : Nat.card (S ⊓ H : Subgroup R) ∣ p := hS ▸ Subgroup.card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime hp).1 hdvd with h1 | hpp
  · exact Subgroup.card_eq_one.1 h1
  · exact absurd (inf_eq_left.1 (Subgroup.eq_of_le_of_card_ge (inf_le_left (b := H))
      (by rw [hS, hpp])))
      (not_le_of_normal_of_pow_eq_one hp hodd hcard hrank hS hY hC hHexp hHcomm)

theorem natCard_inf_centralizer_eq (hp : p.Prime) (hodd : Odd p) (hcard : Nat.card R = p ^ n)
    (hrank : 3 ≤ elementaryAbelianPRank p R) (hS : Nat.card S = p) (hY : IsCyclic Y)
    (hC : IsInternalDirectProduct (centralizer (S : Set R)) S Y) [H.Normal] (hH : H ≠ ⊥)
    (hHexp : ∀ h ∈ H, h ^ p = 1) (hHcomm : ⁅(⊤ : Subgroup R), H⁆ ≤ H ⊓ centralizer (H : Set R)) :
    Nat.card (H ⊓ centralizer (S : Set R) : Subgroup R) = p := by
  have hfin : Finite R := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.ne_zero)
  set T := omega1Subgroup p (centralizer (S : Set R)) with hTdef
  set K := H ⊓ centralizer (S : Set R) with hKdef
  have hKT : K ≤ T := fun x hx =>
    mem_omega1Subgroup (mem_inf.1 hx).2 (hHexp x (mem_inf.1 hx).1)
  have hTle : Nat.card T ≤ p ^ 2 := natCard_omega1Subgroup_centralizer_le_sq hp hS hY hC
  have hKle : Nat.card K ≤ p ^ 2 := le_trans (Subgroup.card_le_of_le hKT) hTle
  have hZK : H ⊓ center R ≤ K :=
    le_inf inf_le_left (le_trans inf_le_right (center_le_centralizer _))
  have hpdvd : p ∣ Nat.card K :=
    dvd_trans (dvd_natCard_inf_center H hp hcard hH) (Subgroup.card_dvd_of_le hZK)
  obtain ⟨j, hjn, hj⟩ := (Nat.dvd_prime_pow hp).1
    (hcard ▸ Subgroup.card_subgroup_dvd_card K : Nat.card K ∣ p ^ n)
  have hj1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with rfl | h
    · rw [pow_zero] at hj; exact absurd (hj ▸ hpdvd) (by simpa using hp.one_lt.ne')
    · exact h
  have hj2 : j ≤ 2 := (Nat.pow_le_pow_iff_right hp.one_lt).1 (hj ▸ hKle)
  have hjne : j ≠ 2 := by
    rintro rfl
    have hKeqT : K = T := Subgroup.eq_of_le_of_card_ge hKT (by rw [hj]; exact hTle)
    have hST : S ≤ T := le_omega1Subgroup_centralizer_self hp hS
    rw [← hKeqT] at hST
    exact not_le_of_normal_of_pow_eq_one hp hodd hcard hrank hS hY hC hHexp hHcomm
      (le_trans hST inf_le_left)
  have hj' : j = 1 := by omega
  rw [hj, hj', pow_one]

theorem inf_eq_bot_and_natCard_inf_centralizer_eq (hp : p.Prime) (hodd : Odd p)
    (hcard : Nat.card R = p ^ n) (hrank : 3 ≤ elementaryAbelianPRank p R) (hS : Nat.card S = p)
    (hY : IsCyclic Y) (hC : IsInternalDirectProduct (centralizer (S : Set R)) S Y) [H.Normal]
    (hH : H ≠ ⊥) (hHexp : ∀ h ∈ H, h ^ p = 1)
    (hHcomm : ⁅(⊤ : Subgroup R), H⁆ ≤ H ⊓ centralizer (H : Set R)) :
    S ⊓ H = ⊥ ∧ Nat.card (H ⊓ centralizer (S : Set R) : Subgroup R) = p :=
  ⟨inf_eq_bot_of_normal_of_pow_eq_one hp hodd hcard hrank hS hY hC hHexp hHcomm,
    natCard_inf_centralizer_eq hp hodd hcard hrank hS hY hC hH hHexp hHcomm⟩

theorem inf_eq_bot_and_natCard_inf_centralizer_eq_of_characteristic (hp : p.Prime) (hodd : Odd p)
    (hcard : Nat.card R = p ^ n) (hrank : 3 ≤ elementaryAbelianPRank p R) (hS : Nat.card S = p)
    (hY : IsCyclic Y) (hC : IsInternalDirectProduct (centralizer (S : Set R)) S Y)
    [H.Characteristic] (hH : H ≠ ⊥) (hHexp : ∀ h ∈ H, h ^ p = 1)
    (hHcomm : ⁅(⊤ : Subgroup R), H⁆ ≤ (center ↥H).map H.subtype) :
    S ⊓ H = ⊥ ∧ Nat.card (H ⊓ centralizer (S : Set R) : Subgroup R) = p := by
  rw [map_center_subtype] at hHcomm
  exact inf_eq_bot_and_natCard_inf_centralizer_eq hp hodd hcard hrank hS hY hC hH hHexp hHcomm

end

end CFSG.FeitThompson
