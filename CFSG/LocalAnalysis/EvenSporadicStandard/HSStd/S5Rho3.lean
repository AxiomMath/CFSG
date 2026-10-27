module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Cent
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G}
  {W X : Type} [Group W] [Group X] [Finite W] (D : AutModelData L W X)

omit [Finite G] in
theorem mem_sup_of_pow_odd (hidx : (L ⊔ zpowers t).relIndex (centralizer ({t} : Set G)) = 2)
    {u : G} (hu : u ∈ centralizer ({t} : Set G)) {m : ℕ} (hm : u ^ (2 * m + 1) = 1) :
    u ∈ L ⊔ zpowers t := by
  have hH2 : ((L ⊔ zpowers t).subgroupOf (centralizer ({t} : Set G))).index = 2 := hidx
  have h1 := Subgroup.mul_self_mem_of_index_two hH2 ⟨u, hu⟩
  have h2 : u * u ∈ L ⊔ zpowers t := mem_subgroupOf.1 h1
  have h3 : u = (u * u) ^ (m + 1) := by
    calc u = u ^ (2 * m + 1) * u := by rw [hm, one_mul]
      _ = (u * u) ^ (m + 1) := by
        rw [← pow_succ, ← pow_two, ← pow_mul]
        rfl
  rw [h3]
  exact pow_mem h2 _

omit [Finite G] [Finite W] in
theorem commute_of_pow_odd (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (hC : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hker : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {u x : G} (hu : u ∈ centralizer ({t} : Set G)) (hx : x ∈ centralizer ({t} : Set G))
    {m : ℕ} (hm : u ^ (2 * m + 1) = 1)
    (h : D.rhoC hC ⟨u, hu⟩ * D.rhoC hC ⟨x, hx⟩ = D.rhoC hC ⟨x, hx⟩ * D.rhoC hC ⟨u, hu⟩) :
    u * x = x * u := by
  have h1 : D.rhoC hC (⟨u, hu⟩ * ⟨x, hx⟩ * ⟨u, hu⟩⁻¹ * ⟨x, hx⟩⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h]
    group
  have h2 : u * x * u⁻¹ * x⁻¹ ∈ zpowers t := (rhoC_eq_one_iff D hC hker _).1 h1
  obtain ⟨j, hj⟩ := mem_zpowers_iff.1 h2
  have hut : u * t = t * u := mem_centralizer_singleton_iff.1 hu
  rcases zpow_eq_one_or_self ht2 j with h3 | h3
  · rw [h3] at hj
    calc u * x = (u * x * u⁻¹ * x⁻¹) * (x * u) := by group
      _ = x * u := by rw [← hj, one_mul]
  · exfalso
    rw [h3] at hj
    have hux : u * x = t * x * u := by
      calc u * x = (u * x * u⁻¹ * x⁻¹) * x * u := by group
        _ = t * x * u := by rw [← hj]
    have key : ∀ k : ℕ, u ^ k * x = t ^ k * x * u ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have hc : u ^ k * t = t * u ^ k := (show Commute u t from hut).pow_left k |>.eq
        calc u ^ (k + 1) * x = u ^ k * (u * x) := by rw [pow_succ]; group
          _ = u ^ k * (t * x * u) := by rw [hux]
          _ = (u ^ k * t) * x * u := by group
          _ = (t * u ^ k) * x * u := by rw [hc]
          _ = t * (u ^ k * x) * u := by group
          _ = t * (t ^ k * x * u ^ k) * u := by rw [ih]
          _ = t ^ (k + 1) * x * u ^ (k + 1) := by rw [pow_succ t, pow_succ u]; group
    have h4 := key (2 * m + 1)
    rw [hm, mul_one, one_mul] at h4
    have h5 : t ^ (2 * m + 1) = t := by
      rw [pow_succ, pow_mul, pow_two, ht2, one_pow, one_mul]
    rw [h5] at h4
    apply ht1
    exact mul_right_cancel (b := x) (by rw [one_mul]; exact h4.symm)

omit [Finite G] [Finite W] in
theorem exists_lift_pow_five (ht2 : t * t = 1)
    (hC : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hker : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hsurj : Function.Surjective (D.rhoC hC)) {r : W} (hr : r ^ 5 = 1) :
    ∃ (u : G) (hu : u ∈ centralizer ({t} : Set G)), D.rhoC hC ⟨u, hu⟩ = r ∧ u ^ 5 = 1 := by
  obtain ⟨c, hc⟩ := hsurj r
  refine ⟨((c ^ 6 : centralizer ({t} : Set G)) : G), (c ^ 6).2, ?_, ?_⟩
  · have : D.rhoC hC (c ^ 6) = r := by
      rw [map_pow, hc]
      calc r ^ 6 = r ^ 5 * r := pow_succ r 5
        _ = r := by rw [hr, one_mul]
    exact this
  · have h1 : D.rhoC hC (c ^ 5) = 1 := by rw [map_pow, hc, hr]
    have h2 : ((c ^ 5 : centralizer ({t} : Set G)) : G) ∈ zpowers t :=
      (rhoC_eq_one_iff D hC hker _).1 h1
    obtain ⟨j, hj⟩ := mem_zpowers_iff.1 h2
    have h3 : ((c : G) ^ 5) * ((c : G) ^ 5) = 1 := by
      have hj' : (c : G) ^ 5 = t ^ j := hj.symm
      rcases zpow_eq_one_or_self ht2 j with h | h
      · rw [hj', h, one_mul]
      · rw [hj', h, ht2]
    calc (((c ^ 6 : centralizer ({t} : Set G)) : G)) ^ 5 = ((c : G) ^ 5 * (c : G) ^ 5) ^ 3 := by
          rw [Subgroup.coe_pow, ← pow_mul, ← pow_add, ← pow_mul]
      _ = 1 := by rw [h3, one_pow]

end CFSG.EvenSporadicStandard.HSStd
