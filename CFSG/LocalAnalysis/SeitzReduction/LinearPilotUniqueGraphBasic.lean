module

public import CFSG.Timmesfeld.Orders.Bang
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotEndFieldBasic

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.Timmesfeld (IsPrimitivePrimeDivisor)
open CFSG.Assembly.LowTwoRank (StatedSp)

section AutOrder

variable {n : ℕ} {K : Type*} [Field K] [Finite K]

theorem card_mulAut_projectiveSL_dvd (hn : 3 ≤ n) {f : ℕ} (hK : Nat.card K = 2 ^ f) :
    Nat.card (MulAut (projectiveSL n K)) ∣ 2 * f * Nat.card (GL (Fin n) K) := by
  set E := semilinearAutGroup n K with hE
  set D := (conjAut n K).range with hD
  set Φ := (fieldAut n K).range with hΦ
  have hDn : D.Normal := conjAut_range_normal hn
  have hEidx : E.index ∣ 2 := by
    rw [Subgroup.index_dvd_two_iff]
    refine ⟨dualAut n K, fun b => ?_⟩
    have hb : b ∈ standardAutGroup n K := by
      rw [(automorphism_generation (K := K) hn).1]
      exact mem_top b
    rcases mem_or_mul_dualAut_mem hb with h | h
    · exact Or.inr h
    · exact Or.inl h
  have hEsup : E = Φ ⊔ D := by
    rw [hE, semilinearAutGroup, Subgroup.closure_union, linearAutGroup_eq_range,
      Subgroup.closure_eq, ← MonoidHom.coe_range, Subgroup.closure_eq, sup_comm]
  have hEDidx : D.relIndex E ∣ f := by
    rw [hEsup, Subgroup.relIndex_sup_right]
    refine (Subgroup.relIndex_dvd_card D Φ).trans ?_
    refine (Subgroup.card_range_dvd (fieldAut n K)).trans ?_
    rw [(card_ringAut_and_isCyclic Nat.prime_two K hK).1]
  have hDE : D ≤ E := by
    rw [hD, ← linearAutGroup_eq_range]
    exact linearAutGroup_le_semilinearAutGroup
  have hEcard : Nat.card E = D.relIndex E * Nat.card D := by
    rw [← Subgroup.relIndex_mul_card D E, inf_eq_left.2 hDE]
  have hDcard : Nat.card D ∣ Nat.card (GL (Fin n) K) := Subgroup.card_range_dvd _
  have hAut : Nat.card (MulAut (projectiveSL n K)) = E.index * (D.relIndex E * Nat.card D) := by
    rw [← hEcard, mul_comm, Subgroup.card_mul_index]
  rw [hAut, mul_assoc]
  exact Nat.mul_dvd_mul hEidx (Nat.mul_dvd_mul hEDidx hDcard)

end AutOrder

theorem index_lt_of_isPrimitivePrimeDivisor {p k : ℕ} (h : IsPrimitivePrimeDivisor p k)
    (hk : 0 < k) : k < p := by
  have hp := h.prime
  have := Fact.mk hp
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h0
    have h0' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
    rw [ZMod.natCast_eq_zero_iff] at h0'
    exact h.ne_two hk ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h0')
  have hferm : p ∣ 2 ^ (p - 1) - 1 :=
    (CFSG.Timmesfeld.Bang.dvd_two_pow_sub_one_iff (p - 1)).2 (ZMod.pow_card_sub_one_eq_one h2)
  have hdvd := (h.dvd_sub_one_iff hk (p - 1)).1 hferm
  have := Nat.le_of_dvd (by have := hp.two_le; omega) hdvd
  omega

section PPD

variable {n : ℕ} {K : Type*} [Field K] [Finite K]

theorem not_dvd_two_mul_card_mulAut_of_ppd (hn : 3 ≤ n) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) {p k : ℕ} (hp : IsPrimitivePrimeDivisor p k) (hk : f * n < k) :
    ¬ p ∣ 2 * Nat.card (MulAut (projectiveSL n K)) := by
  intro hdvd
  have hk0 : 0 < k := by omega
  have hpk := index_lt_of_isPrimitivePrimeDivisor hp hk0
  have hpr := hp.prime
  have hp2 : ¬ p ∣ 2 := fun h =>
    hp.ne_two hk0 ((Nat.prime_dvd_prime_iff_eq hpr Nat.prime_two).1 h)
  have hpf : ¬ p ∣ f := fun h => by
    have h1 := Nat.le_of_dvd (by omega) h
    have h2 : f ≤ f * n := Nat.le_mul_of_pos_right f (by omega)
    omega
  have hpow : ¬ p ∣ (2 ^ f) ^ (n * (n - 1) / 2) := fun h => by
    rw [← pow_mul] at h
    exact hp2 (hpr.dvd_of_dvd_pow h)
  have hprod : ¬ p ∣ ∏ j ∈ Finset.Icc 1 n, ((2 ^ f) ^ j - 1) := by
    rw [Prime.dvd_finsetProd_iff hpr.prime]
    rintro ⟨j, hj, hpj⟩
    rw [← pow_mul] at hpj
    have hj' := Finset.mem_Icc.1 hj
    have h1 := (hp.dvd_sub_one_iff hk0 (f * j)).1 hpj
    have h2 : k ≤ f * j := Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega)) h1
    have h3 : f * j ≤ f * n := Nat.mul_le_mul_left f hj'.2
    omega
  have h1 : p ∣ 2 * (2 * f * Nat.card (GL (Fin n) K)) :=
    hdvd.trans (Nat.mul_dvd_mul_left 2 (card_mulAut_projectiveSL_dvd hn hK))
  rw [card_GL_eq, hK] at h1
  rcases (Nat.Prime.dvd_mul hpr).1 h1 with h | h
  · exact hp2 h
  rcases (Nat.Prime.dvd_mul hpr).1 h with h | h
  · rcases (Nat.Prime.dvd_mul hpr).1 h with h | h
    · exact hp2 h
    · exact hpf h
  rcases (Nat.Prime.dvd_mul hpr).1 h with h | h
  · exact hpow h
  · exact hprod h

end PPD

section Symplectic

variable {F : Type} [Field F] [Finite F]

theorem ppd_dvd_card_statedSp {e s p : ℕ} (hF : Nat.card F = 2 ^ e) (hs : 1 ≤ s)
    (hp : p ∣ 2 ^ (2 * e * s) - 1) : p ∣ Nat.card (StatedSp s F) := by
  rw [SymplecticFlag.card_statedSp, hF]
  refine Dvd.dvd.mul_left ?_ _
  refine dvd_trans ?_ (Finset.dvd_prod_of_mem _ (Finset.mem_Icc.2 ⟨hs, le_rfl⟩))
  rw [← pow_mul, show e * (2 * s) = 2 * e * s by ring]
  exact hp

theorem pow_dvd_card_statedSp (s : ℕ) : Nat.card F ^ (s ^ 2) ∣ Nat.card (StatedSp s F) := by
  rw [SymplecticFlag.card_statedSp]
  exact Dvd.intro _ rfl

end Symplectic

end CFSG.SeitzReduction.LinearPilot
