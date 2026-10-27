module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPropTwelveK

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoTwelve

open Subgroup CFSG.Semidihedral.Principal.PrimewiseScalar

variable {G : Type} [Group G] [Finite G] {z : G}

omit [Finite G] in
theorem mem_normalizer_sup {A B : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G))
    (hB : g ∈ normalizer (B : Set G)) : g ∈ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

namespace Hyp

variable {fr : JankoFrame G z}

theorem card_K_inf_centralizer (h : Hyp fr) {y : G} (hy : y ∈ fr.P3bar) (hy1 : y ≠ 1) :
    Nat.card (fr.K ⊓ centralizer ({y} : Set G) : Subgroup G) = 6 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyS : y ∈ fr.S := (le_sup_left : fr.P3bar ≤ fr.S) hy
  have hys : IsConj y fr.s₃ := h.isConj_s₃_of_mem_S hyS hy1
  set c := Nat.card (fr.K ⊓ centralizer ({y} : Set G) : Subgroup G)
  have horb : {w | ∃ k ∈ fr.K, k * y * k⁻¹ = w}.ncard * c = 48 := by
    have := card_conj_orbit_mul fr.K y
    rwa [fr.card_K] at this
  have hsub : {w | ∃ k ∈ fr.K, k * y * k⁻¹ = w} ⊆ (fr.S : Set G) \ {1} := by
    rintro _ ⟨k, hk, rfl⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp (h.K_le_normalizer_S hk) y).mp hyS, ?_⟩
    intro h1
    apply hy1
    calc y = k⁻¹ * (k * y * k⁻¹) * k := by group
      _ = 1 := by rw [Set.mem_singleton_iff.mp h1]; group
  have hn8 : {w | ∃ k ∈ fr.K, k * y * k⁻¹ = w}.ncard ≤ 8 := by
    refine (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ?_
    rw [Set.ncard_sdiff_singleton_of_mem (one_mem fr.S), ← Nat.card_coe_set_eq,
      SetLike.coe_sort_coe, h.card_S]
  have hc6 : 6 ≤ c := by
    by_contra hlt
    push Not at hlt
    have := Nat.mul_le_mul hn8 (Nat.le_of_lt_succ hlt)
    omega
  have hc48 : c ∣ 48 := fr.card_K ▸ Subgroup.card_dvd_of_le inf_le_left
  have hc4 : ¬ 4 ∣ c := by
    intro h4
    obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime
      (G := (fr.K ⊓ centralizer ({y} : Set G) : Subgroup G)) 2 (n := 2)
      (by rw [show (2 : ℕ) ^ 2 = 4 by norm_num]; exact h4)
    have hP'c : Nat.card (P.map (fr.K ⊓ centralizer ({y} : Set G)).subtype) = 4 := by
      rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hP]
      norm_num
    have := h.p7.card_le_two y hys _ ((Subgroup.map_subtype_le _).trans inf_le_right)
      (IsPGroup.of_card (n := 2) (by rw [hP'c]; norm_num))
    omega
  have hc48' := Nat.le_of_dvd (by norm_num) hc48
  interval_cases c <;> omega

theorem P3bbar_eq_S_inf (h : Hyp fr) :
    fr.P3bbar = fr.S ⊓ centralizer ({fr.t * z} : Set G) := by
  refine le_antisymm (le_inf (le_sup_right : fr.P3bbar ≤ fr.S) inf_le_right) ?_
  intro x hx
  obtain ⟨hxS, hxtz⟩ := Subgroup.mem_inf.mp hx
  exact Subgroup.mem_inf.mpr ⟨h.S_le_ZN hxS, hxtz⟩

theorem eq_one_of_comm_t (h : Hyp fr) {m : G} (hmK : m ∈ fr.K) (hm3 : orderOf m = 3)
    (hmP : m ∈ centralizer (fr.P3bar : Set G)) (hmt : m * fr.t = fr.t * m) : m = 1 := by
  obtain ⟨y', hy'P, hy'3⟩ := h.exists_P3bbar_eq
  have hmz : m * z = z * m := Subgroup.mem_centralizer_singleton_iff.mp (fr.K_le hmK)
  have hmtz : m * (fr.t * z) = fr.t * z * m := by
    rw [← mul_assoc, hmt, mul_assoc, hmz, ← mul_assoc]
  have hmN : m ∈ normalizer (fr.P3bbar : Set G) := by
    refine CFSG.Walter.J1.mem_normalizer_of_conj_mem fun x hx => ?_
    rw [h.P3bbar_eq_S_inf] at hx ⊢
    obtain ⟨hxS, hxtz⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (h.K_le_normalizer_S hmK) x).mp
      hxS, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hxtz
    have hm' : m⁻¹ * (fr.t * z) = fr.t * z * m⁻¹ := by
      calc m⁻¹ * (fr.t * z) = m⁻¹ * (fr.t * z * m) * m⁻¹ := by group
        _ = m⁻¹ * (m * (fr.t * z)) * m⁻¹ := by rw [hmtz]
        _ = fr.t * z * m⁻¹ := by group
    calc m * x * m⁻¹ * (fr.t * z) = m * x * (m⁻¹ * (fr.t * z)) := by group
      _ = m * (x * (fr.t * z)) * m⁻¹ := by rw [hm']; group
      _ = m * (fr.t * z * x) * m⁻¹ := by rw [hxtz]
      _ = fr.t * z * (m * x * m⁻¹) := by rw [← mul_assoc, hmtz]; group
  rw [hy'P] at hmN
  have hmy' := conj_eq_of_odd hy'3 hmN (by rw [hm3]; decide)
  have hS : fr.S ≤ centralizer ({m} : Set G) := by
    refine sup_le (fun x hx => ?_) ?_
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hmP x hx)
    · rw [hy'P, Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      calc y' * m = m * y' * m⁻¹ * m := by rw [hmy']
        _ = m * y' := by group
  exact h.eq_one_of_le_centralizer hmK hS

theorem t_mem_normalizer_zpowers {m : G} (h : Hyp fr) (htm : fr.t * m * fr.t⁻¹ = m⁻¹) :
    fr.t ∈ normalizer ((zpowers m : Subgroup G) : Set G) := by
  have := h.t_inv
  refine CFSG.Walter.J1.mem_normalizer_of_conj_mem fun x hx => ?_
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← conj_zpow, htm]
  exact zpow_mem (inv_mem (Subgroup.mem_zpowers m)) k

theorem exists_m (h : Hyp fr) : ∃ m : G, m ∈ fr.K ∧ orderOf m = 3 ∧
    m ∈ centralizer (fr.P3bar : Set G) ∧ fr.t * m * fr.t⁻¹ = m⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hyP, hy3⟩ := h.exists_P3bar_eq
  have hy : y ∈ fr.P3bar := hyP ▸ Subgroup.mem_zpowers y
  have hy1 : y ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hy3
    exact absurd hy3 (by norm_num)
  set D := fr.K ⊓ centralizer ({y} : Set G)
  have hD := h.card_K_inf_centralizer hy hy1
  obtain ⟨m₀, hm₀⟩ := exists_prime_orderOf_dvd_card' (G := D) 3 (by rw [hD]; norm_num)
  obtain ⟨m, hmD', hm3⟩ : ∃ m ∈ D, orderOf m = 3 :=
    ⟨m₀.1, m₀.2, by rw [Subgroup.orderOf_coe]; exact hm₀⟩
  obtain ⟨hmK, hmy⟩ := Subgroup.mem_inf.mp hmD'
  have hmP : m ∈ centralizer (fr.P3bar : Set G) := by
    rw [hyP, centralizer_zpowers]
    exact hmy
  have htD : fr.t ∈ D := Subgroup.mem_inf.mpr ⟨h.t_mem_K, h.t_mem_centralizer_of_mem_P3bar hy⟩
  have hmD : zpowers m ≤ D := Subgroup.zpowers_le.mpr hmD'
  have hidx : ((zpowers m).subgroupOf D).index = 2 := by
    have := Subgroup.relIndex_mul_card (zpowers m) D
    rw [inf_of_le_left hmD, Nat.card_zpowers, hm3, hD] at this
    change (zpowers m).relIndex D = 2
    omega
  have hnorm := Subgroup.normal_of_index_eq_two hidx
  have htm : fr.t * m * fr.t⁻¹ ∈ zpowers m := by
    have := hnorm.conj_mem ⟨m, hmD'⟩ (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers m))
      ⟨fr.t, htD⟩
    exact Subgroup.mem_subgroupOf.mp this
  have htm' : fr.t * m * fr.t⁻¹ = m⁻¹ := by
    rcases eq_one_or_eq_or_eq_inv_of_mem_zpowers hm3 htm with h1 | h1 | h1
    · exfalso
      have : m = 1 := by
        calc m = fr.t⁻¹ * (fr.t * m * fr.t⁻¹) * fr.t := by group
          _ = 1 := by rw [h1]; group
      rw [this, orderOf_one] at hm3
      exact absurd hm3 (by norm_num)
    · exfalso
      have hc : m * fr.t = fr.t * m := by
        calc m * fr.t = fr.t * m * fr.t⁻¹ * fr.t := by rw [h1]
          _ = fr.t * m := by group
      have := h.eq_one_of_comm_t hmK hm3 hmP hc
      rw [this, orderOf_one] at hm3
      exact absurd hm3 (by norm_num)
    · exact h1
  exact ⟨m, hmK, hm3, hmP, htm'⟩

end Hyp

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoTwelve
