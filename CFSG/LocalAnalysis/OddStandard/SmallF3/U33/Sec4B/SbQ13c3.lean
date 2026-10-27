module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13c0

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

private lemma q13c_eq_four_of_dvd_eight {n : ℕ} (hge : 3 ≤ n) (hlt : n < 8)
    (hdvd : n ∣ 2 ^ 3) : n = 4 := by
  obtain ⟨c, hc⟩ := hdvd
  have h8 : (2:ℕ) ^ 3 = 8 := by norm_num
  rw [h8] at hc
  have hclow : 1 ≤ c := Nat.one_le_iff_ne_zero.mpr (by rintro rfl; norm_num at hc)
  have hcle : c ≤ 2 := by nlinarith
  interval_cases c <;> omega

theorem q13c_N_cent_gens (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    tau ∈ ctxN tau x₁ x₂ ⊓ centralizer ({t * lam} : Set G) ∧
      (x₁ * x₂) ^ 2 ∈ ctxN tau x₁ x₂ ⊓ centralizer ({t * lam} : Set G) := by
  constructor
  · refine ⟨q13b_tau_mem_N h, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc tau * (t * lam) = (tau * t) * lam := by group
      _ = (t * tau) * lam := by rw [(q13a_t_comm h).2.2]
      _ = t * (tau * lam) := by group
      _ = t * (lam * tau) := by rw [q13c_lam_cent_tau h]
      _ = (t * lam) * tau := by group
  · have hzN : (x₁ * x₂) ^ 2 ∈ ctxN tau x₁ x₂ :=
      q13b_V_le_N h (Subgroup.subset_closure (by simp))
    refine ⟨hzN, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc (x₁ * x₂) ^ 2 * (t * lam) = ((x₁ * x₂) ^ 2 * t) * lam := by group
      _ = (t * (x₁ * x₂) ^ 2) * lam := by rw [(q13c_t_cent_N h _ hzN).symm]
      _ = t * ((x₁ * x₂) ^ 2 * lam) := by group
      _ = t * (lam * (x₁ * x₂) ^ 2) := by rw [q13c_lam_z h]
      _ = (t * lam) * (x₁ * x₂) ^ 2 := by group

theorem q13c_card_N_cent (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    Nat.card ↥(ctxN tau x₁ x₂ ⊓ centralizer ({t * lam} : Set G)) = 4 := by
  classical
  set K : Subgroup G := ctxN tau x₁ x₂ ⊓ centralizer ({t * lam} : Set G) with hK
  have hle : K ≤ ctxN tau x₁ x₂ := by rw [hK]; exact inf_le_left
  have hyN : x₁ ^ 2 ∈ ctxN tau x₁ x₂ := Subgroup.subset_closure (by simp)
  have hyK : x₁ ^ 2 ∉ K := by
    intro hyK
    have hmem : x₁ ^ 2 ∈ ctxN tau x₁ x₂ ⊓ centralizer ({t * lam} : Set G) := by
      rw [← hK]; exact hyK
    have hcomm : x₁ ^ 2 * (t * lam) = (t * lam) * x₁ ^ 2 :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hmem).2
    have h2 : t * x₁ ^ 2 = x₁ ^ 2 * t := q13c_t_cent_N h _ hyN
    have h4 : t * (x₁ ^ 2 * lam) = t * (lam * x₁ ^ 2) := by
      calc t * (x₁ ^ 2 * lam) = (t * x₁ ^ 2) * lam := by group
        _ = (x₁ ^ 2 * t) * lam := by rw [h2]
        _ = x₁ ^ 2 * (t * lam) := by group
        _ = (t * lam) * x₁ ^ 2 := hcomm
        _ = t * (lam * x₁ ^ 2) := by group
    exact q13c_lam_not_cent_y h (mul_left_cancel h4).symm
  have hKne : K ≠ ctxN tau x₁ x₂ := fun heq => hyK (heq ▸ hyN)
  have hlt : K < ctxN tau x₁ x₂ := lt_of_le_of_ne hle hKne
  have hcardlt : Nat.card ↥K < 8 := by
    have hc := Subgroup.card_lt_of_lt hlt
    rwa [q13b_card_N h] at hc
  have hdvd : Nat.card ↥K ∣ 2 ^ 3 := by
    rw [show (2:ℕ) ^ 3 = 8 from by norm_num]
    have hc := Subgroup.card_dvd_of_le hle
    rwa [q13b_card_N h] at hc
  have hge : 3 ≤ Nat.card ↥K := by
    have h1K : (1 : G) ∈ K := one_mem K
    have hτK : tau ∈ K := by rw [hK]; exact (q13c_N_cent_gens h).1
    have hzK : (x₁ * x₂) ^ 2 ∈ K := by rw [hK]; exact (q13c_N_cent_gens h).2
    have hzV : (x₁ * x₂) ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
    have hz_ne_tau : (x₁ * x₂) ^ 2 ≠ tau := fun heq =>
      l12_tau_not_mem_V h.c11.toCtx10.toCtx4 (heq ▸ hzV)
    have hz_ne_one : (x₁ * x₂) ^ 2 ≠ 1 := (q13b_z_facts h).1
    have hτ_ne_one : tau ≠ 1 := q13b_tau_ne_one h
    let s : Finset ↥K := {⟨1, h1K⟩, ⟨tau, hτK⟩, ⟨(x₁ * x₂) ^ 2, hzK⟩}
    have h1not : (⟨1, h1K⟩ : ↥K) ∉
        ({⟨tau, hτK⟩, ⟨(x₁ * x₂) ^ 2, hzK⟩} : Finset ↥K) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq]
      rintro (h1 | h1)
      · exact hτ_ne_one h1.symm
      · exact hz_ne_one h1.symm
    have hτnot : (⟨tau, hτK⟩ : ↥K) ∉
        ({⟨(x₁ * x₂) ^ 2, hzK⟩} : Finset ↥K) := by
      simp only [Finset.mem_singleton, Subtype.mk.injEq]
      exact fun h1 => hz_ne_tau h1.symm
    have hcard : s.card = 3 := by
      rw [Finset.card_insert_of_notMem h1not, Finset.card_insert_of_notMem hτnot,
        Finset.card_singleton]
    letI : Fintype ↥K := Fintype.ofFinite ↥K
    have hle_univ : s.card ≤ Fintype.card ↥K := Finset.card_le_univ s
    rw [hcard] at hle_univ
    rwa [Nat.card_eq_fintype_card]
  exact q13c_eq_four_of_dvd_eight hge hcardlt hdvd

theorem q13c_N_cent_elem (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    CFSG.Open.IsElemAbelian 2 (ctxN tau x₁ x₂ ⊓ centralizer ({t * lam} : Set G)) :=
  CFSG.Open.IsElemAbelian.mono (q13b_N_elemAbelian h) inf_le_left

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
