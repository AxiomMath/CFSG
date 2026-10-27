module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.WpGTypes
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapTgrp
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.PairTypes

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern

variable {G : Type} [Group G] {z : G} {ι : Perm (Fin 10) →* G}

theorem Tgrp_le_centralizer_x₂ (hC : CentData z ι) {Q : Subgroup (Perm (Fin 10))} (hQ : GoodQ Q) :
    Tgrp z ι Q ≤ centralizer ({z * ι τ₀} : Set G) := by
  intro g hg
  obtain ⟨i, q, hq, rfl⟩ := (mem_Tgrp_iff hC).mp hg
  rw [mem_centralizer_singleton_iff]
  have hzq : Commute z (ι τ₀) := hC.comm τ₀
  have hqt : Commute (ι q) (ι τ₀) := by
    show ι q * ι τ₀ = ι τ₀ * ι q
    rw [← map_mul, ← map_mul, (hQ.τ₀_comm q hq).symm]
  have hqz : Commute (ι q) z := (hC.comm q).symm
  have h1 : Commute (z ^ (i : ℕ)) (z * ι τ₀) :=
    ((Commute.refl z).pow_left _).mul_right (hzq.pow_left _)
  have h2 : Commute (ι q) (z * ι τ₀) := hqz.mul_right hqt
  exact h1.mul_left h2

theorem x₂_mem_Tgrp (hC : CentData z ι) {Q : Subgroup (Perm (Fin 10))} (hQ : GoodQ Q) :
    z * ι τ₀ ∈ Tgrp z ι Q :=
  mul_mem (z_mem_Tgrp Q) (map_le_Tgrp Q (Subgroup.mem_map_of_mem ι hQ.τ₀_mem))

theorem exists_sylow_ge [Finite G] {T C : Subgroup G} (hT : IsPGroup 2 T) (hTC : T ≤ C) :
    ∃ T₂ : Subgroup G, T ≤ T₂ ∧ T₂ ≤ C ∧ IsPGroup 2 T₂ ∧ ¬ 2 ∣ T₂.relIndex C := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT' : IsPGroup 2 (T.subgroupOf C) := by
    have e := Subgroup.subgroupOfEquivOfLe hTC
    exact hT.of_equiv e.symm
  obtain ⟨P, hP⟩ := hT'.exists_le_sylow
  refine ⟨(P : Subgroup C).map C.subtype, ?_, Subgroup.map_subtype_le _, ?_, ?_⟩
  · rw [← Subgroup.map_subgroupOf_eq_of_le hTC]
    exact Subgroup.map_mono hP
  · obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp P.isPGroup'
    refine IsPGroup.of_card (n := n) ?_
    rw [Subgroup.card_map_of_injective C.subtype_injective]
    exact hn
  · rw [Subgroup.relIndex,
      show ((P : Subgroup C).map C.subtype).subgroupOf C = P from
        Subgroup.comap_map_eq_self_of_injective C.subtype_injective _]
    exact P.not_dvd_index

theorem center_le_Fgrp (hC : CentData z ι) {Q : Subgroup (Perm (Fin 10))} (hQ : GoodQ Q)
    {T₂ : Subgroup G} (hT : Tgrp z ι Q ≤ T₂) (h2 : IsPGroup 2 T₂) :
    centralizer (T₂ : Set G) ⊓ T₂ ≤ Fgrp (Tgrp z ι Q) := by
  intro w hw
  obtain ⟨hwc, hwT₂⟩ := Subgroup.mem_inf.mp hw
  have hwT : w ∈ centralizer ((Tgrp z ι Q : Subgroup G) : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun h hh => Subgroup.mem_centralizer_iff.mp hwc h (hT hh)
  refine Subgroup.mem_inf.mpr ⟨hwT, ?_⟩
  have hTz : Tgrp z ι Q ≤ centralizer ({z} : Set G) := by
    intro g hg
    obtain ⟨i, q, hq, rfl⟩ := (mem_Tgrp_iff hC).mp hg
    rw [mem_centralizer_singleton_iff]
    exact (((Commute.refl z).pow_left _).mul_left (hC.comm q).symm : Commute _ z)
  have hwz : w ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hwT z (z_mem_Tgrp Q)).symm
  have hRz : (Tgrp z ι Q ⊔ zpowers w : Subgroup G) ≤ centralizer ({z} : Set G) :=
    sup_le hTz (zpowers_le.mpr hwz)
  haveI : Finite (centralizer ({z} : Set G)) :=
    Nat.finite_of_card_ne_zero (by rw [card_centralizer_z hC]; norm_num)
  haveI : Finite (Tgrp z ι Q ⊔ zpowers w : Subgroup G) :=
    Finite.of_injective (Subgroup.inclusion hRz) (Subgroup.inclusion_injective hRz)
  have hR2 : IsPGroup 2 (Tgrp z ι Q ⊔ zpowers w : Subgroup G) :=
    h2.to_le (sup_le hT (zpowers_le.mpr hwT₂))
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hR2
  have hdvd := Subgroup.card_dvd_of_le hRz
  rw [card_centralizer_z hC, hm] at hdvd
  have hTcard : Nat.card (Tgrp z ι Q) = 2 ^ 9 := by
    rw [Tgrp_card hC, hQ.card]; norm_num
  have hTR : Nat.card (Tgrp z ι Q) ∣ Nat.card (Tgrp z ι Q ⊔ zpowers w : Subgroup G) :=
    Subgroup.card_dvd_of_le le_sup_left
  rw [hTcard, hm] at hTR
  have h9 : 9 ≤ m := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hTR
  have hm9 : m ≤ 9 := by
    by_contra hlt
    have h10 : 2 ^ 10 ∣ 2 ^ m := pow_dvd_pow 2 (by omega)
    have := h10.trans hdvd
    norm_num at this
  have hmeq : m = 9 := le_antisymm hm9 h9
  have hcardeq : Nat.card (Tgrp z ι Q ⊔ zpowers w : Subgroup G) ≤ Nat.card (Tgrp z ι Q) := by
    rw [hm, hmeq, hTcard]
  have hEq := Subgroup.eq_of_le_of_card_ge (le_sup_left : Tgrp z ι Q ≤ Tgrp z ι Q ⊔ zpowers w)
    hcardeq
  rw [hEq]
  exact Subgroup.mem_sup_right (mem_zpowers w)

theorem eq_x₂_of_mem_Fgrp (hC : CentData z ι) {Q : Subgroup (Perm (Fin 10))} (hQ : GoodQ Q)
    (hfr : IsConj z (ι τ₀)) (hP2 : ¬ IsConj z (z * ι τ₀))
    (hAll : ∀ c : G, IsConj z c → c ∈ centralizer ({z * ι τ₀} : Set G) →
      pairOrder c (z * ι τ₀) = N10 1)
    {w : G} (hw : w ∈ Fgrp (Tgrp z ι Q)) (hconj : IsConj (z * ι τ₀) w) : w = z * ι τ₀ := by
  obtain ⟨i, j, k, hijk⟩ := (mem_Fgrp_iff hC hQ).mp hw
  have hF : ∀ i j : Fin 2, w = z ^ (i : ℕ) * (ι τ₀) ^ (j : ℕ) * ι ρ₄ → False := by
    intro i j hij
    obtain ⟨n, hn⟩ := isConj_iff.mp hconj
    have hzw : z * w = w * z :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hw).1 z (z_mem_Tgrp Q)
    have hx : z * ι τ₀ = n⁻¹ * w * n := by rw [← hn]; group
    have hcc : n⁻¹ * z * n ∈ centralizer ({z * ι τ₀} : Set G) := by
      rw [mem_centralizer_singleton_iff, hx]
      calc n⁻¹ * z * n * (n⁻¹ * w * n) = n⁻¹ * (z * w) * n := by group
        _ = n⁻¹ * (w * z) * n := by rw [hzw]
        _ = n⁻¹ * w * n * (n⁻¹ * z * n) := by group
    have hzc : IsConj z (n⁻¹ * z * n) := isConj_iff.mpr ⟨n⁻¹, by simp⟩
    have h1 := hAll _ hzc hcc
    have h2 := pairOrder_conj n⁻¹ z w
    rw [inv_inv, ← hx] at h2
    have h3 : pairOrder z w = N10 1 := h2.symm.trans h1
    rw [hij] at h3
    exact pairOrder_z_ne_N10_one hC i j h3
  have hx1 : (z * ι τ₀) ≠ 1 := x₂_ne_one hC
  fin_cases k
  · fin_cases i <;> fin_cases j <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
        one_mul, mul_one] at hijk
    ·
      subst hijk
      exact absurd (isConj_one_left.mp hconj) hx1
    ·
      subst hijk
      exact absurd (hfr.trans hconj.symm) hP2
    ·
      subst hijk
      exact absurd hconj.symm hP2
    · exact hijk
  · exfalso
    exact hF i j (by simpa using hijk)

theorem normalizer_le_centralizer_x₂ (hC : CentData z ι) {Q : Subgroup (Perm (Fin 10))}
    (hQ : GoodQ Q) (hfr : IsConj z (ι τ₀)) (hP2 : ¬ IsConj z (z * ι τ₀))
    (hAll : ∀ c : G, IsConj z c → c ∈ centralizer ({z * ι τ₀} : Set G) →
      pairOrder c (z * ι τ₀) = N10 1)
    {T₂ : Subgroup G} (hT : Tgrp z ι Q ≤ T₂) (hT₂ : T₂ ≤ centralizer ({z * ι τ₀} : Set G))
    (h2 : IsPGroup 2 T₂) : normalizer (T₂ : Set G) ≤ centralizer ({z * ι τ₀} : Set G) := by
  intro n hn
  have hx₂T : z * ι τ₀ ∈ T₂ := hT (x₂_mem_Tgrp hC hQ)
  have hwT₂ : n * (z * ι τ₀) * n⁻¹ ∈ T₂ := (Subgroup.mem_normalizer_iff.mp hn _).mp hx₂T
  have hwc : n * (z * ι τ₀) * n⁻¹ ∈ centralizer (T₂ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have ht' : n⁻¹ * t * n ∈ T₂ := by
      simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem hn) t).mp ht
    have hcomm := mem_centralizer_singleton_iff.mp (hT₂ ht')
    calc t * (n * (z * ι τ₀) * n⁻¹) = n * ((n⁻¹ * t * n) * (z * ι τ₀)) * n⁻¹ := by group
      _ = n * ((z * ι τ₀) * (n⁻¹ * t * n)) * n⁻¹ := by rw [hcomm]
      _ = n * (z * ι τ₀) * n⁻¹ * t := by group
  have hwF := center_le_Fgrp hC hQ hT h2 (Subgroup.mem_inf.mpr ⟨hwc, hwT₂⟩)
  have hw : n * (z * ι τ₀) * n⁻¹ = z * ι τ₀ :=
    eq_x₂_of_mem_Fgrp hC hQ hfr hP2 hAll hwF (isConj_iff.mpr ⟨n, rfl⟩)
  rw [mem_centralizer_singleton_iff]
  exact mul_inv_eq_iff_eq_mul.mp hw

end CFSG.OddStandard.AltStdSec.SwapPartner
