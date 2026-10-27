module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13c7
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13c8b

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

private lemma q13c_commute_of_mul_right {a c f : G} (h : Commute (a * c) f)
    (hc : Commute c f) : Commute a f := by
  have h1 : a * f * c = f * a * c := by
    calc a * f * c = a * (f * c) := by group
      _ = a * (c * f) := by rw [hc.eq]
      _ = (a * c) * f := by group
      _ = f * (a * c) := h.eq
      _ = f * a * c := by group
  exact mul_right_cancel h1

private lemma q13c_commute_of_mul_left {a b f : G} (h : Commute (b * a) f)
    (hb : Commute b f) : Commute a f := by
  have h1 : b * (a * f) = b * (f * a) := by
    calc b * (a * f) = (b * a) * f := by group
      _ = f * (b * a) := h.eq
      _ = f * b * a := by group
      _ = b * f * a := by rw [← hb.eq]
      _ = b * (f * a) := by group
  exact mul_left_cancel h1

private lemma q13c_om_mul_t (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    om * t = t * tau * om := by
  calc om * t = (om * t * om⁻¹) * om := by group
    _ = (t * tau) * om := by rw [h.t_om]

private lemma q13c_om_not_comm_t (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    om * t ≠ t * om := by
  intro hc
  have h2 : tau * om = 1 * om := by
    apply mul_left_cancel (a := t)
    calc t * (tau * om) = t * tau * om := by group
      _ = om * t := (q13c_om_mul_t h).symm
      _ = t * om := hc
      _ = t * (1 * om) := by group
  exact q13b_tau_ne_one h (mul_right_cancel h2)

private lemma q13c_om_not_cent (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hl : lam * om * lam⁻¹ = om) : om * (t * lam) ≠ (t * lam) * om := by
  intro hc
  have hlam_om : lam * om = om * lam := by
    calc lam * om = lam * om * lam⁻¹ * lam := by group
      _ = om * lam := by rw [hl]
  apply q13c_om_not_comm_t h
  have h1 : om * t * lam = t * om * lam := by
    calc om * t * lam = om * (t * lam) := by group
      _ = (t * lam) * om := hc
      _ = t * (lam * om) := by group
      _ = t * (om * lam) := by rw [hlam_om]
      _ = t * om * lam := by group
  exact mul_right_cancel h1

theorem q13c_card_CU_le (h : Q13Om t L S x₁ x₂ lam rho tau om) (hB : Q13Bs t x₁ x₂ lam tau) :
    Nat.card ↥(ctxU t tau x₁ x₂ lam ⊓ centralizer ({t * lam} : Set G)) ≤ 2 ^ 6 := by
  set D : Subgroup G := ctxU t tau x₁ x₂ lam ⊓ centralizer ({t * lam} : Set G) with hD
  have hD2 : IsPGroup 2 D := (q13b_isPGroup_U h).to_le inf_le_left
  have hDc : D ≤ centralizer ({t * lam} : Set G) := inf_le_right
  obtain ⟨n, hn⟩ := hD2.exists_card_eq
  have hle7 : 2 ^ n ≤ 2 ^ 7 := by
    rw [← hn]
    exact q13c_card_le h hD2 hDc
  have hne7 : 2 ^ n ≠ 2 ^ 7 := by
    rw [← hn]
    exact q13c_key h hB (q13b_isPGroup_U h) le_rfl
  have hn7 : n ≤ 7 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle7
  have hn_ne : n ≠ 7 := by
    rintro rfl
    exact hne7 rfl
  have hn6 : n ≤ 6 := by omega
  calc Nat.card ↥D = 2 ^ n := hn
    _ ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num : 0 < 2) hn6

theorem q13c_lam_om_eq (h : Q13Om t L S x₁ x₂ lam rho tau om) (hB : Q13Bs t x₁ x₂ lam tau) :
    lam * om * lam⁻¹ = om := by
  rcases q13a_lam_om h with hcase | hcase
  · exact hcase
  · exfalso
    have hge := q13c_card_CU_ge_II h hcase
    have hle := q13c_card_CU_le h hB
    norm_num at hge hle
    omega

theorem q13c_card_CU (h : Q13Om t L S x₁ x₂ lam rho tau om) (hB : Q13Bs t x₁ x₂ lam tau) :
    Nat.card ↥(ctxU t tau x₁ x₂ lam ⊓ centralizer ({t * lam} : Set G)) = 2 ^ 6 := by
  apply le_antisymm
  · exact q13c_card_CU_le h hB
  · norm_num
    exact q13c_card_CU_ge h

theorem q13c_C_dih (h : Q13Om t L S x₁ x₂ lam rho tau om) (hB : Q13Bs t x₁ x₂ lam tau) :
    closure {t, om} ⊓ centralizer ({t * lam} : Set G) = closure {t, tau} := by
  have hl : lam * om * lam⁻¹ = om := q13c_lam_om_eq h hB
  have ht_comm : Commute t (t * lam) := (Commute.refl t).mul_right (q13a_t_comm h).1
  have h_tau_t : Commute tau t := ((q13a_t_comm h).2.2).symm
  have h_tau_lam : Commute tau lam := (q13c_lam_cent_tau h).symm
  have htau_comm : Commute tau (t * lam) := h_tau_t.mul_right h_tau_lam
  have htau_mem : tau ∈ closure ({t, om} : Set G) := by
    have h1 : om * t * om⁻¹ ∈ closure ({t, om} : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _
        (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)))
        (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp)))
    have h2 : t * (om * t * om⁻¹) ∈ closure ({t, om} : Set G) :=
      Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) h1
    rwa [h.t_om, ← mul_assoc, q13a_t_mul_self h, one_mul] at h2
  apply le_antisymm
  · intro g hg
    obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.mp hg
    have hg2' : Commute g (t * lam) := Subgroup.mem_centralizer_singleton_iff.mp hg2
    rcases q13a_D8_cases h hg1 with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
    · rw [h1]; exact one_mem _
    · rw [h1]; exact Subgroup.subset_closure (by simp)
    · rw [h1]; exact Subgroup.subset_closure (by simp)
    · rw [h1]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
    · rw [h1] at hg2'
      exact absurd hg2' (q13c_om_not_cent h hl)
    · rw [h1] at hg2'
      exact absurd hg2'
        (fun hc => q13c_om_not_cent h hl (q13c_commute_of_mul_right hc htau_comm))
    · rw [h1] at hg2'
      exact absurd hg2'
        (fun hc => q13c_om_not_cent h hl (q13c_commute_of_mul_left hc ht_comm))
    · rw [h1] at hg2'
      exact absurd hg2' (fun hc => q13c_om_not_cent h hl
        (q13c_commute_of_mul_left (q13c_commute_of_mul_right hc htau_comm) ht_comm))
  · refine le_inf ?_ ?_
    · rw [Subgroup.closure_le]
      intro x hx
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Subgroup.subset_closure (by simp)
      · exact htau_mem
    · rw [Subgroup.closure_le]
      intro x hx
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Subgroup.mem_centralizer_singleton_iff.mpr ht_comm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr htau_comm

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
