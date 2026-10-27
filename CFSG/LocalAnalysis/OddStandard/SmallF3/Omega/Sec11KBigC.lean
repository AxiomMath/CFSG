module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec79BA
public import CFSG.ClassicalInvolution.Q3.Q3T8AF01

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem sec11KB_oddCore_le (X : Subgroup G) : oddCoreIn X ≤ X :=
  Subgroup.map_subtype_le (CFSG.oddCore X)

theorem sec11KB_oddCore_odd [Finite G] (X : Subgroup G) : Odd (Nat.card (oddCoreIn X)) :=
  odd_card_oddCoreIn X

theorem sec11KB_oddCore_norm (X : Subgroup G) {x : G} (hx : x ∈ X) {n : G}
    (hn : n ∈ oddCoreIn X) : x * n * x⁻¹ ∈ oddCoreIn X := by
  rw [oddCoreIn, CFSG.inSubgroup, Subgroup.mem_map] at hn
  obtain ⟨y, hy, rfl⟩ := hn
  rw [oddCoreIn, CFSG.inSubgroup, Subgroup.mem_map]
  refine ⟨⟨x, hx⟩ * y * ⟨x, hx⟩⁻¹, ?_, ?_⟩
  · exact Subgroup.Normal.conj_mem (inferInstance) y hy ⟨x, hx⟩
  · rfl

theorem sec11KB_le_oddCore [Finite G] {X Y : Subgroup G} (hYX : Y ≤ X)
    (hYn : ∀ x ∈ X, ∀ y ∈ Y, x * y * x⁻¹ ∈ Y) (hYo : Odd (Nat.card Y)) : Y ≤ oddCoreIn X := by
  refine le_oddCoreIn_of_normal hYX ?_ hYo
  rw [Subgroup.normal_subgroupOf_iff hYX]
  intro y x hy hx
  exact hYn x hx y hy

theorem sec11KB_conj_oddCore [Finite G] {X : Subgroup G} {h : G} (hh : h ∈ normalizer (X : Set G))
    {n : G} (hn : n ∈ oddCoreIn X) : h * n * h⁻¹ ∈ oddCoreIn X :=
  conj_mem_oddCoreIn hh hn

theorem sec11KB_frattini [Finite G] {X : Subgroup G} {t w : G} (ht2 : t * t = 1) (htX : t ∈ X)
    (hw : w ∈ normalizer (X : Set G)) (hwt : w * t * w⁻¹ * t⁻¹ ∈ oddCoreIn X) :
    ∃ o ∈ oddCoreIn X, o⁻¹ * w ∈ centralizer ({t} : Set G) := by
  set a : G := w * t * w⁻¹ with ha
  have ha2 : a * a = 1 := by
    rw [ha]
    calc (w * t * w⁻¹) * (w * t * w⁻¹) = w * (t * t) * w⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have htaO : t⁻¹ * a ∈ oddCoreIn X := by
    have h : a * t ∈ oddCoreIn X := by
      rw [ha] at hwt
      simpa [hti] using hwt
    have hinv := (oddCoreIn X).inv_mem h
    have hgoal : (a * t)⁻¹ = t⁻¹ * a := by
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ha2]
    rwa [hgoal] at hinv
  obtain ⟨o, ho, huo⟩ := CFSG.ClassicalInvolution.Q3.Q3T8.AF.exists_conj_of_inv_mul_mem
    ht2 ha2 (sec11KB_oddCore_odd X) htaO
  refine ⟨o, ho, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  rw [ha] at huo
  calc o⁻¹ * w * t = o⁻¹ * (w * t * w⁻¹) * w := by group
    _ = o⁻¹ * (o * t * o⁻¹) * w := by rw [huo]
    _ = t * (o⁻¹ * w) := by group

theorem sec11KB_odd_lift [Finite G] {O : Subgroup G} (hO : Odd (Nat.card O)) {w : G}
    (hwO : ∀ n ∈ O, w * n * w⁻¹ ∈ O) (hw : Odd (orderOf w)) {o : G} (ho : o ∈ O) :
    Odd (orderOf (o⁻¹ * w)) := by
  set c : G := o⁻¹ * w with hc
  have key : ∀ k : ℕ, c ^ k * w ^ (-(k : ℤ)) ∈ O := by
    intro k
    induction k with
    | zero => simpa using O.one_mem
    | succ k ih =>
        have hz : w ^ (-(((k + 1 : ℕ) : ℤ))) = w ^ (-(k : ℤ)) * w⁻¹ := by
          rw [show -(((k + 1 : ℕ) : ℤ)) = -(k : ℤ) + (-1 : ℤ) by push_cast; ring,
            zpow_add, zpow_neg_one]
        have heq : c ^ (k + 1) * w ^ (-(((k + 1 : ℕ) : ℤ))) =
            o⁻¹ * (w * (c ^ k * w ^ (-(k : ℤ))) * w⁻¹) := by
          rw [pow_succ', hz, hc]
          group
        rw [heq]
        exact O.mul_mem (O.inv_mem ho) (hwO _ ih)
  have hwm : w ^ (-(orderOf w : ℤ)) = 1 := by
    rw [zpow_neg, zpow_natCast, pow_orderOf_eq_one, inv_one]
  have hcm : c ^ orderOf w ∈ O := by
    have h := key (orderOf w)
    rwa [hwm, mul_one] at h
  have hpow : (c ^ orderOf w) ^ Nat.card O = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (O.orderOf_dvd_natCard hcm)
  have hdvd : orderOf c ∣ orderOf w * Nat.card O :=
    orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_mul]; exact hpow)
  exact (hw.mul hO).of_dvd_nat hdvd

end CFSG.OddStandard.SmallF3.Omega
