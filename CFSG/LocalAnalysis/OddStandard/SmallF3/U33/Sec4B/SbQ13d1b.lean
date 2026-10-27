module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13d1a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13c0

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

private theorem conjIn_mono_aux {K₁ K₂ : Subgroup G} (hK : K₁ ≤ K₂) (x : G) :
    conjIn K₁ x ⊆ conjIn K₂ x := by
  rintro u ⟨k, hk, hku⟩
  exact ⟨k, hK hk, hku⟩

private theorem q13d_two_le_ncard_conjIn_U_y (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    2 ≤ (conjIn (ctxU t tau x₁ x₂ lam) (x₁ ^ 2)).ncard := by
  have hlamU : lam ∈ ctxU t tau x₁ x₂ lam :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers lam)
  have hy_mem : x₁ ^ 2 ∈ conjIn (ctxU t tau x₁ x₂ lam) (x₁ ^ 2) :=
    ⟨1, one_mem _, by group⟩
  have hyz_mem : x₁ ^ 2 * (x₁ * x₂) ^ 2 ∈ conjIn (ctxU t tau x₁ x₂ lam) (x₁ ^ 2) := by
    refine ⟨lam, hlamU, ?_⟩
    rw [q13c_lam_y h]
  have hne : x₁ ^ 2 ≠ x₁ ^ 2 * (x₁ * x₂) ^ 2 := by
    intro hc
    have hz1 : (x₁ * x₂) ^ 2 = 1 := by
      have hthis := congrArg (fun w => (x₁ ^ 2)⁻¹ * w) hc
      simpa [mul_assoc] using hthis.symm
    exact (q13b_z_facts h).1 hz1
  have hpair : ({x₁ ^ 2, x₁ ^ 2 * (x₁ * x₂) ^ 2} : Set G).ncard = 2 :=
    Set.ncard_pair hne
  have hsub : ({x₁ ^ 2, x₁ ^ 2 * (x₁ * x₂) ^ 2} : Set G) ⊆
      conjIn (ctxU t tau x₁ x₂ lam) (x₁ ^ 2) := by
    intro a ha
    rcases ha with rfl | rfl
    · exact hy_mem
    · exact hyz_mem
  calc 2 = ({x₁ ^ 2, x₁ ^ 2 * (x₁ * x₂) ^ 2} : Set G).ncard := hpair.symm
    _ ≤ _ := Set.ncard_le_ncard hsub

private theorem q13d_card_inf_cent_y_le (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    Nat.card ↥(ctxU t tau x₁ x₂ lam ⊓ centralizer ({x₁ ^ 2} : Set G)) ≤ 2 ^ 9 := by
  have horb := card_eq_ncard_conjIn_mul (ctxU t tau x₁ x₂ lam) (x₁ ^ 2)
  rw [q13b_card_U h] at horb
  have h2 := q13d_two_le_ncard_conjIn_U_y h
  have hmul : 2 * Nat.card ↥(ctxU t tau x₁ x₂ lam ⊓ centralizer ({x₁ ^ 2} : Set G))
      ≤ 2 ^ 10 := by
    rw [horb]
    exact Nat.mul_le_mul_right _ h2
  have hpow : (2 : ℕ) ^ 10 = 2 * 2 ^ 9 := by norm_num
  rw [hpow] at hmul
  exact Nat.le_of_mul_le_mul_left hmul (by norm_num)

private theorem q13d_Q_le_inf_cent_y (_h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ctxQ t tau x₁ x₂ rho ≤ ctxU t tau x₁ x₂ lam ⊓ centralizer ({x₁ ^ 2} : Set G) := by
  refine le_inf (q13b_Q_normal_U _h).1 ?_
  intro q hq
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (q13a_V_central _h (x₁ ^ 2) (Subgroup.subset_closure (by simp)) q hq).symm

private theorem q13d_four_le_ncard_conjIn_inf_cent_y_tau (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    4 ≤ (conjIn (ctxU t tau x₁ x₂ lam ⊓ centralizer ({x₁ ^ 2} : Set G)) tau).ncard := by
  have hsub := conjIn_mono_aux (q13d_Q_le_inf_cent_y h) tau
  have hcard4 : (conjIn (ctxQ t tau x₁ x₂ rho) tau).ncard = 4 := by
    rw [q13a_tauQ h, Set.ncard_smul_set, ← Nat.card_coe_set_eq]
    exact h.c11.wreath.fourGrp_eq_omega.2.2
  calc 4 = (conjIn (ctxQ t tau x₁ x₂ rho) tau).ncard := hcard4.symm
    _ ≤ _ := Set.ncard_le_ncard hsub

private theorem q13d_card_inf_cent_y_inf_cent_tau_le (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    Nat.card ↥((ctxU t tau x₁ x₂ lam ⊓ centralizer ({x₁ ^ 2} : Set G))
      ⊓ centralizer ({tau} : Set G)) ≤ 2 ^ 7 := by
  have horb := card_eq_ncard_conjIn_mul
    (ctxU t tau x₁ x₂ lam ⊓ centralizer ({x₁ ^ 2} : Set G)) tau
  have h4 := q13d_four_le_ncard_conjIn_inf_cent_y_tau h
  have hDy := q13d_card_inf_cent_y_le h
  have hmul : 4 * Nat.card ↥((ctxU t tau x₁ x₂ lam ⊓ centralizer ({x₁ ^ 2} : Set G))
      ⊓ centralizer ({tau} : Set G)) ≤ 2 ^ 9 := by
    calc 4 * _ ≤ (conjIn (ctxU t tau x₁ x₂ lam ⊓ centralizer ({x₁ ^ 2} : Set G)) tau).ncard
          * Nat.card ↥((ctxU t tau x₁ x₂ lam ⊓ centralizer ({x₁ ^ 2} : Set G))
              ⊓ centralizer ({tau} : Set G)) := Nat.mul_le_mul_right _ h4
      _ = Nat.card ↥(ctxU t tau x₁ x₂ lam ⊓ centralizer ({x₁ ^ 2} : Set G)) := horb.symm
      _ ≤ 2 ^ 9 := hDy
  have hpow : (2 : ℕ) ^ 9 = 4 * 2 ^ 7 := by norm_num
  rw [hpow] at hmul
  exact Nat.le_of_mul_le_mul_left hmul (by norm_num)

theorem q13d_card_cent_N_U_le (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    Nat.card ↥(ctxU t tau x₁ x₂ lam ⊓ centralizer ((ctxN tau x₁ x₂ : Subgroup G) : Set G))
      ≤ 2 ^ 7 := by
  have hle1 : ctxU t tau x₁ x₂ lam ⊓ centralizer ((ctxN tau x₁ x₂ : Subgroup G) : Set G)
      ≤ ctxU t tau x₁ x₂ lam ⊓ centralizer ({x₁ ^ 2} : Set G) := by
    refine le_inf inf_le_left ?_
    intro u hu
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hu).2 (x₁ ^ 2)
      (Subgroup.subset_closure (by simp)))).symm
  have hle2 : ctxU t tau x₁ x₂ lam ⊓ centralizer ((ctxN tau x₁ x₂ : Subgroup G) : Set G)
      ≤ centralizer ({tau} : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hu).2 tau
      (Subgroup.subset_closure (by simp)))).symm
  exact (Subgroup.card_le_of_le (le_inf hle1 hle2)).trans
    (q13d_card_inf_cent_y_inf_cent_tau_le h)

theorem q13d_cent_N_U_eq (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ctxU t tau x₁ x₂ lam ⊓ centralizer ((ctxN tau x₁ x₂ : Subgroup G) : Set G)
      = q13A t tau x₁ x₂ rho ⊔ closure ({t, om} : Set G) := by
  symm
  refine Subgroup.eq_of_le_of_card_ge (q13d_AC_le_cent h) ?_
  rw [q13d_card_AC h]
  exact q13d_card_cent_N_U_le h

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
