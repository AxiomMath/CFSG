module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4DiagUf
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Basic

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace CSU

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher UnitaryOut UnitaryConj HBlocks StabU DiagU
  ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.GSThmB

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

include h in
theorem exists_order_eight (hp2 : p ≠ 2) : ∃ ζ : K, ζ ^ 8 = 1 ∧ ζ ^ 4 = -1 := by
  classical
  have : Finite K := h.finite
  obtain ⟨μ, hμ⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf μ = Nat.card K - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hμ, Nat.card_units]
  have h8 : 8 ∣ orderOf μ := by
    rw [hord, h.card]
    obtain ⟨m, hm⟩ : Odd (p ^ f) := (h.prime.odd_of_ne_two hp2).pow
    rw [show p ^ (2 * f) = (p ^ f) ^ 2 by rw [← pow_mul, mul_comm], hm]
    obtain ⟨k, hk⟩ := Nat.even_mul_succ_self m
    have e : (2 * m + 1) ^ 2 = 4 * (m * (m + 1)) + 1 := by ring
    refine ⟨k, ?_⟩
    rw [e, Nat.add_sub_cancel, hk]
    ring
  set ζu := μ ^ (orderOf μ / 8) with hζu
  have hζord : orderOf ζu = 8 := orderOf_pow_orderOf_div (orderOf_pos μ).ne' h8
  refine ⟨(ζu : K), ?_, ?_⟩
  · rw [← Units.val_pow_eq_pow_val, ← hζord, pow_orderOf_eq_one, Units.val_one]
  · have h4 : ζu ^ 4 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hζord]; norm_num)
    have h44 : ((ζu : K) ^ 4) * ((ζu : K) ^ 4) = 1 := by
      rw [← pow_add, ← Units.val_pow_eq_pow_val, show 4 + 4 = orderOf ζu by rw [hζord],
        pow_orderOf_eq_one, Units.val_one]
    rcases mul_self_eq_one_iff.mp h44 with h1 | h1
    · exact absurd (Units.ext (by rw [Units.val_pow_eq_pow_val, h1, Units.val_one])) h4
    · exact h1

include h in
theorem card_mod_four_of_inner (hp2 : p ≠ 2) {l : K} (hl4 : l ^ 4 = 1)
    (hbl : h.bar l * l = -1) : p ^ f % 4 = 1 := by
  have hodd : Odd (p ^ f) := (h.prime.odd_of_ne_two hp2).pow
  have h13 : p ^ f % 4 = 1 ∨ p ^ f % 4 = 3 := by
    obtain ⟨m, hm⟩ := hodd
    omega
  rcases h13 with h1 | h3
  · exact h1
  · exfalso
    obtain ⟨k, hk⟩ : ∃ k, p ^ f = 4 * k + 3 := ⟨p ^ f / 4, by omega⟩
    rw [h.bar_apply, hk, ← pow_succ, show 4 * k + 3 + 1 = 4 * (k + 1) by ring, pow_mul, hl4,
      one_pow] at hbl
    exact two_ne_zero_of_odd h hp2 (by linear_combination hbl)

omit h in
theorem cP_eq_of_mul (P : GL (Fin 4) K) {g : unitarySU p f K 4} {M : Matrix (Fin 4) (Fin 4) K}
    (hg : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * P = P * M) : cP P g = M := by
  rw [cP, Matrix.mul_assoc, hg, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, Matrix.one_mul]

omit h in
theorem X1_eq_blk (l : K) : X1 l = blk l 0 0 (-l) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [X1, blk]

theorem normalizes_of_mem_CAU {J' : Subgroup (StatedProj (StatedSU 4 (p ^ f) K))}
    {x : StatedProj (StatedSU 4 (p ^ f) K)} (hx : MulAut.conj x ∈ CAU J') (y) :
    y ∈ J' ↔ x * y * x⁻¹ ∈ J' := by
  constructor
  · intro hy
    have := hx y hy
    rw [MulAut.conj_apply] at this
    rwa [this]
  · intro hy
    have hinv : (MulAut.conj x)⁻¹ ∈ CAU J' := inv_mem hx
    have := hinv _ hy
    rw [← map_inv, MulAut.conj_apply] at this
    have e : x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y := by group
    rw [e] at this
    rw [this]
    exact hy

end CSU

end CFSG.ComponentClassification.CatFactsL4U4
