module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.P1Normalizer
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.P1SylowCrit

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern

private theorem card_centralizer_eq_of_isConj {G : Type*} [Group G] {a b : G}
    (h : IsConj a b) :
    Nat.card ↥(Subgroup.centralizer ({a} : Set G)) =
      Nat.card ↥(Subgroup.centralizer ({b} : Set G)) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  rw [Subgroup.nat_card_centralizer_nat_card_stabilizer a,
    Subgroup.nat_card_centralizer_nat_card_stabilizer b]
  have hg : b = ConjAct.toConjAct c • a := by rw [ConjAct.toConjAct_smul, hc]
  exact Nat.card_congr (MulAction.stabilizerEquivStabilizer hg).toEquiv

variable {G : Type} [Group G] {z : G} {ι : Perm (Fin 10) →* G}

variable [Finite G]

theorem not_two_dvd_index_Tgrp_P1 (hC : CentData z ι) (hx : IsConj z (ι τ₀))
    (hP1 : IsConj z (z * ι τ₀)) {Q : Subgroup (Perm (Fin 10))} (hQ : GoodQ Q) :
    ¬ 2 ∣ (Tgrp z ι Q).index := by
  have hTpg : IsPGroup 2 (Tgrp z ι Q) := Tgrp_isPGroup hC hQ.pgroup
  have hTcard : Nat.card (Tgrp z ι Q) = 2 ^ 9 := by
    rw [Tgrp_card hC Q, hQ.card]
    norm_num
  refine not_two_dvd_index_of_two_elements hTpg hTcard ?_
  intro x hxN hx2
  obtain ⟨m, hm⟩ := hx2
  let E : Set G := {z, ι τ₀, z * ι τ₀}
  have hpres : ∀ w ∈ E, x * w * x⁻¹ ∈ E :=
    normalizer_Tgrp_preserves_Esharp hC hx hP1 hQ hxN
  have hz_ne_tau : z ≠ ι τ₀ := fun h => hC.ne_z τ₀ h.symm
  have htau_ne_one : ι τ₀ ≠ 1 := fun h =>
    (by decide : τ₀ ≠ 1) (hC.inj (by rw [h, map_one]))
  have hz_ne_one : z ≠ 1 := fun h => by
    have h2 := hC.order
    rw [h, orderOf_one] at h2
    exact absurd h2 (by decide)
  have hz_ne_ztau : z ≠ z * ι τ₀ := by
    intro h
    have h1 : (1 : G) = ι τ₀ := by
      refine mul_left_cancel (a := z) ?_
      rw [mul_one]
      exact h
    exact htau_ne_one h1.symm
  have hztau_ne_tau : z * ι τ₀ ≠ ι τ₀ := by
    intro h
    have h1 : z = 1 := by
      refine mul_right_cancel (b := ι τ₀) ?_
      rw [one_mul]
      exact h
    exact hz_ne_one h1
  have hcardE : Nat.card ↥E = 3 := by
    change Nat.card ↥({z, ι τ₀, z * ι τ₀} : Set G) = 3
    rw [Nat.card_coe_set_eq,
      Set.ncard_insert_of_notMem (by simp [hz_ne_tau, hz_ne_ztau]),
      Set.ncard_insert_of_notMem (by simp [hztau_ne_tau.symm]),
      Set.ncard_singleton]
  have hoddE : Odd (Nat.card ↥E) := by rw [hcardE]; norm_num
  let conjMap : ↥E → ↥E := fun w => ⟨x * (w : G) * x⁻¹, hpres w w.2⟩
  have hconj_inj : Function.Injective conjMap := by
    intro u v huv
    apply Subtype.ext
    have hv : x * (u : G) * x⁻¹ = x * (v : G) * x⁻¹ := congrArg Subtype.val huv
    exact mul_left_cancel (mul_right_cancel hv)
  let f : Equiv.Perm ↥E :=
    Equiv.ofBijective conjMap (Finite.injective_iff_bijective.mp hconj_inj)
  have hmem : ∀ n (w : G), w ∈ E → x ^ n * w * (x ^ n)⁻¹ ∈ E := by
    intro n
    induction n with
    | zero => intro w hw; simpa using hw
    | succ n ih =>
        intro w hw
        have h2 := hpres _ (ih w hw)
        have heq : x ^ (n + 1) * w * (x ^ (n + 1))⁻¹ =
            x * (x ^ n * w * (x ^ n)⁻¹) * x⁻¹ := by
          rw [pow_succ]; group
        rwa [heq]
  have hpow : ∀ n (v : ↥E), (f ^ n) v =
      (⟨x ^ n * (v : G) * (x ^ n)⁻¹, hmem n v v.2⟩ : ↥E) := by
    intro n
    induction n with
    | zero =>
        intro v
        apply Subtype.ext
        simp
    | succ n ih =>
        intro v
        rw [pow_succ, Equiv.Perm.mul_apply]
        have hfv : f v = (⟨x * (v : G) * x⁻¹, hpres v v.2⟩ : ↥E) := by
          simp [f, conjMap]
        rw [hfv, ih]
        apply Subtype.ext
        simp only [Subtype.coe_mk]
        rw [pow_succ]
        group
  have hfpow : f ^ 2 ^ m = 1 := by
    apply Equiv.ext
    intro v
    rw [hpow (2 ^ m) v]
    apply Subtype.ext
    simp [hm]
  obtain ⟨u, hu⟩ :=
    exists_fixedPoint_of_pow_two_pow_eq_one (α := ↥E) hoddE f hfpow
  have hxu : x * (u : G) * x⁻¹ = (u : G) := by
    have hfu : f u = (⟨x * (u : G) * x⁻¹, hpres u u.2⟩ : ↥E) := by
      simp [f, conjMap]
    have h := congrArg Subtype.val hu
    rw [hfu] at h
    simpa using h
  let H : Subgroup G := Subgroup.centralizer ({(u : G)} : Set G)
  have hxH : x ∈ H := by
    change x ∈ Subgroup.centralizer ({(u : G)} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (mul_inv_eq_iff_eq_mul).mp hxu
  have hTH : Tgrp z ι Q ≤ H := by
    intro t ht
    change t ∈ Subgroup.centralizer ({(u : G)} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have huE : (u : G) ∈ ({z, ι τ₀, z * ι τ₀} : Set G) := u.2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false,
      or_false] at huE
    have huF : (u : G) ∈ Fgrp (Tgrp z ι Q) := by
      rcases huE with huz | hut | huzt
      · rw [huz]; exact (mem_Fgrp_iff hC hQ).mpr ⟨1, 0, 0, by simp⟩
      · rw [hut]; exact (mem_Fgrp_iff hC hQ).mpr ⟨0, 1, 0, by simp⟩
      · rw [huzt]; exact (mem_Fgrp_iff hC hQ).mpr ⟨1, 1, 0, by simp⟩
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp huF).1) t ht
  have hHcard : Nat.card ↥H = 2 * Nat.card (Perm (Fin 10)) := by
    change Nat.card ↥(Subgroup.centralizer ({(u : G)} : Set G)) =
      2 * Nat.card (Perm (Fin 10))
    have huE : (u : G) ∈ ({z, ι τ₀, z * ι τ₀} : Set G) := u.2
    have hconj : IsConj z (u : G) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false,
        or_false] at huE
      rcases huE with huz | hut | huzt
      · rw [huz]
      · rw [hut]; exact hx
      · rw [huzt]; exact hP1
    rw [card_centralizer_eq_of_isConj hconj.symm, card_centralizer_of_centData hC]
  have hnot : ¬ 2 ^ (9 + 1) ∣ Nat.card ↥H := by
    rw [hHcard, Nat.card_perm, Nat.card_fin]
    norm_num
  exact ⟨H, hTH, hxH, hnot⟩

end CFSG.OddStandard.AltStdSec.SwapPartner
