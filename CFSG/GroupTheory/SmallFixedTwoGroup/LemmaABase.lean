module

public import CFSG.GroupTheory.SmallFixedTwoGroup.LemmaACentral
public import CFSG.GroupTheory.SmallFixedTwoGroup.LemmaAIndex
public import CFSG.GroupTheory.SmallFixedTwoGroup.LemmaAQ
public import CFSG.GroupTheory.SmallFixedTwoGroup.LemmaAV
public import CFSG.GroupTheory.SmallFixedTwoGroup.LemmaAQ8

public section

namespace CFSG.GroupTheory.SmallFixedTwoGroup

open Subgroup

theorem exists_index_two_involutions_central_of_card_sixteen
    {T : Type*} [Group T] [Finite T] (hcard : Nat.card T = 16)
    {s : T} (hs : s * s = 1) (hsz : s ∉ center T)
    (hab : ∀ a ∈ centralizer ({s} : Set T), ∀ b ∈ centralizer ({s} : Set T), a * b = b * a)
    (h8 : Nat.card (centralizer ({s} : Set T)) ≤ 8) :
    ∃ M : Subgroup T, M.index = 2 ∧ ∀ u ∈ M, u * u = 1 → u ∈ center T := by
  haveI hnt : Nontrivial T :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)
  have hTp : IsPGroup 2 T :=
    IsPGroup.of_card (p := 2) (n := 4) (by rw [hcard]; norm_num)
  obtain ⟨z, hz, hzord⟩ := exists_mem_center_orderOf_eq_two hTp
  have hz2 : z * z = 1 := by
    have h := pow_orderOf_eq_one z
    rw [hzord] at h
    simpa [pow_two] using h
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hzord
    omega
  by_cases Hcase : ∃ z' ∈ center T, z' * z' = 1 ∧ z' ≠ 1 ∧
      ∃ p : T, p * p ≠ 1 ∧ p * p ≠ z' ∧ (p ^ 4 = 1 ∨ p ^ 4 = z')
  · obtain ⟨z', hz', hz'2, hz'1, p, hp1, hp2, hp4⟩ := Hcase
    exact exists_index_two_involutions_central_of_order_four_quotient
      hcard hz' hz'2 hz'1 hp1 hp2 hp4
  · have hnone : ¬ ∃ p : T, p * p ≠ 1 ∧ p * p ≠ z ∧ (p ^ 4 = 1 ∨ p ^ 4 = z) := by
      rintro ⟨p, hp1, hp2, hp4⟩
      exact Hcase ⟨z, hz, hz2, hz1, p, hp1, hp2, hp4⟩
    have hsq : ∀ g : T, g * g = 1 ∨ g * g = z :=
      sq_cases_of_card_sixteen hcard hz hz2 hz1 hnone
    have hno : ∀ w ∈ center T, w * w = 1 → w = 1 ∨ w = z := by
      intro w hw hw2
      by_contra hcon
      push Not at hcon
      obtain ⟨hw1, hwz⟩ := hcon
      have hnone_w : ¬ ∃ p : T, p * p ≠ 1 ∧ p * p ≠ w ∧
          (p ^ 4 = 1 ∨ p ^ 4 = w) := by
        rintro ⟨p, hp1, hp2, hp4⟩
        exact Hcase ⟨w, hw, hw2, hw1, p, hp1, hp2, hp4⟩
      have hsq_w : ∀ g : T, g * g = 1 ∨ g * g = w :=
        sq_cases_of_card_sixteen hcard hw hw2 hw1 hnone_w
      have hsq_all : ∀ g : T, g * g = 1 := by
        intro g
        rcases hsq g with h1 | h2
        · exact h1
        · rcases hsq_w g with h3 | h4
          · exact h3
          · exact absurd (h4 ▸ h2) hwz
      have hcommT : ∀ g h : T, g * h = h * g := by
        intro g h
        have hg : g * g = 1 := hsq_all g
        have hh : h * h = 1 := hsq_all h
        have hgh : (g * h) * (g * h) = 1 := hsq_all (g * h)
        have e1 : (g * h)⁻¹ = g * h := inv_eq_of_mul_eq_one_right hgh
        have e2 : (g * h)⁻¹ = h * g := by
          rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hg, inv_eq_of_mul_eq_one_right hh]
        rw [← e1, e2]
      exact hsz (Subgroup.mem_center_iff.mpr (fun g => hcommT g s))
    have hCidx : (centralizer ({s} : Set T)).index ≤ 2 :=
      index_centralizer_le_two (fun g => conj_cases_of_sq_cases hz hz2 hsq g s)
    have hCidx_ne0 : (centralizer ({s} : Set T)).index ≠ 0 :=
      Subgroup.index_ne_zero_of_finite
    have hCidx_ne1 : (centralizer ({s} : Set T)).index ≠ 1 := by
      intro h1
      have htop : centralizer ({s} : Set T) = ⊤ := Subgroup.index_eq_one.mp h1
      exact hsz (Subgroup.mem_center_iff.mpr (fun g => by
        have hg : g ∈ centralizer ({s} : Set T) := by
          rw [htop]; exact Subgroup.mem_top g
        exact (Subgroup.mem_centralizer_iff.mp hg s (by simp)).symm))
    have hCidx2 : (centralizer ({s} : Set T)).index = 2 := by omega
    have hC8 : Nat.card (centralizer ({s} : Set T)) = 8 := by
      have hcardmul := Subgroup.card_mul_index (H := centralizer ({s} : Set T))
      rw [hcard, hCidx2] at hcardmul
      omega
    obtain ⟨v, hv_center, hv_sq⟩ :=
      exists_mem_center_sq_eq_of_exponent_two_quotient
        hcard hz hz2 hsq hno hs hsz hab hC8
    have hxex : ∃ x : T, x * s ≠ s * x :=
      not_forall.mp (fun h => hsz (Subgroup.mem_center_iff.mpr h))
    obtain ⟨x, hx⟩ := hxex
    have hxs : x * s * x⁻¹ = z * s := by
      rcases conj_cases_of_sq_cases hz hz2 hsq x s with h | h
      · exfalso
        exact hx (by
          have hc := congrArg (fun t => t * x) h
          simpa [mul_assoc] using hc)
      · exact h
    have hvs : v * s = s * v := (Subgroup.mem_center_iff.mp hv_center s).symm
    have ha : (s * v) * (s * v) = z := by
      rw [mul_assoc s v (s * v), ← mul_assoc v s v, hvs, mul_assoc s v v,
        ← mul_assoc s s, hs, one_mul, hv_sq]
    have hnorm : ∀ g : T, g * (s * v) * g⁻¹ = s * v ∨
        g * (s * v) * g⁻¹ = z * (s * v) :=
      fun g => conj_cases_of_sq_cases hz hz2 hsq g (s * v)
    have hxa : x * (s * v) * x⁻¹ = z * (s * v) := by
      have hvx : v * x⁻¹ = x⁻¹ * v :=
        (Subgroup.mem_center_iff.mp hv_center x⁻¹).symm
      calc x * (s * v) * x⁻¹ = (x * s) * (v * x⁻¹) := by group
        _ = (x * s) * (x⁻¹ * v) := by rw [hvx]
        _ = (x * s * x⁻¹) * v := by group
        _ = (z * s) * v := by rw [hxs]
        _ = z * (s * v) := by rw [mul_assoc]
    rcases hsq x with hxx | hxx
    · refine exists_index_two_involutions_central_of_quaternion_pair
        (b := x * v) hcard hz hz2 hz1 ha ?_ ?_ hnorm
      · rw [mul_assoc x v (x * v), ← mul_assoc v x v,
          (Subgroup.mem_center_iff.mp hv_center x).symm, mul_assoc x v v,
          ← mul_assoc x x, hxx, one_mul, hv_sq]
      · have hvsconj : v * s * v⁻¹ = s := by
          rw [(Subgroup.mem_center_iff.mp hv_center s).symm, mul_assoc,
            mul_inv_cancel, mul_one]
        have hv1 : v * (s * v) * v⁻¹ = s * v := by
          rw [show v * (s * v) * v⁻¹ = (v * s * v⁻¹) * v by group, hvsconj]
        rw [mul_inv_rev,
          show (x * v) * (s * v) * (v⁻¹ * x⁻¹) =
              x * (v * (s * v) * v⁻¹) * x⁻¹ by group,
          hv1]
        exact hxa
    · exact exists_index_two_involutions_central_of_quaternion_pair
        (b := x) hcard hz hz2 hz1 ha hxx hxa hnorm

end CFSG.GroupTheory.SmallFixedTwoGroup
