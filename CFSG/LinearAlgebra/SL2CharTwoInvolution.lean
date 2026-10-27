module

public import CFSG.Timmesfeld.RankOne.SL2
public import CFSG.LinearAlgebra.FinTwoMatrixCharTwo
public import CFSG.Quasithin.Vol2.Ch4Sec3L436InspFFL2

public section

namespace CFSG.LinearAlgebra

open Matrix
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

section SL2WDiag

variable {K : Type} [Field K]

theorem sl2W_mul_sl2Diag_ne_one (a : Kˣ) :
    (sl2W * sl2Diag a : Matrix.SpecialLinearGroup (Fin 2) K) ≠ 1 := by
  intro h
  have h00 := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 2) K =>
    (x : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.one_apply] at h00

end SL2WDiag

variable {K : Type} [Field K] [CharP K 2]

theorem specialLinear_mul_self_eq_one_of_orderOf_eq_two_pow
    (s : Matrix.SpecialLinearGroup (Fin 2) K) {k : ℕ} (h : orderOf s = 2 ^ k) :
    s * s = 1 := by
  have hpow : s ^ 2 ^ k = 1 := by rw [← h, pow_orderOf_eq_one]
  have hm : (s : Matrix (Fin 2) (Fin 2) K) ^ 2 ^ k = 1 := by
    have := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 2) K =>
      (x : Matrix (Fin 2) (Fin 2) K)) hpow
    simpa using this
  have h2 := CFSG.LinearAlgebra.fin_two_sq_eq_one_of_pow_two_pow_eq_one hm
  apply Subtype.ext
  simpa [pow_two] using h2

theorem sl2W_mul_self : (sl2W : Matrix.SpecialLinearGroup (Fin 2) K) * sl2W = 1 := by
  rw [sl2W_mul_sl2W]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_sl2Diag, CharTwo.neg_eq]

theorem sl2W_ne_one : (sl2W : Matrix.SpecialLinearGroup (Fin 2) K) ≠ 1 := by
  intro h
  have h00 := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 2) K =>
    (x : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simp [coe_sl2W] at h00

theorem exists_conj_sl2W [Finite K] {s : Matrix.SpecialLinearGroup (Fin 2) K}
    (h2 : s * s = 1) (h1 : s ≠ 1) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) K, g * sl2W * g⁻¹ = s := by
  obtain ⟨g, hg⟩ := CFSG.Quasithin.H13.Ch4.FFL2.exists_conj_t0
    (F := K) (a := (sl2W : Matrix.SpecialLinearGroup (Fin 2) K)) sl2W_mul_self sl2W_ne_one
  obtain ⟨h, hh⟩ := CFSG.Quasithin.H13.Ch4.FFL2.exists_conj_t0 (F := K) (a := s) h2 h1
  refine ⟨h * g⁻¹, ?_⟩
  rw [← hh]
  have ht0 : CFSG.Quasithin.H13.Ch4.FFL2.t0 (F := K) = g⁻¹ * sl2W * g := by
    rw [← hg]
    group
  rw [ht0]
  group

theorem sl2W_mul_sl2Diag_mul_sl2W_inv (a : Kˣ) :
    (sl2W : Matrix.SpecialLinearGroup (Fin 2) K) * sl2Diag a * sl2W⁻¹ = sl2Diag a⁻¹ := by
  rw [sl2W_mul_sl2Diag]
  group

theorem sl2W_mul_sl2Diag_mul_self (a : Kˣ) :
    ((sl2W : Matrix.SpecialLinearGroup (Fin 2) K) * sl2Diag a) *
      (sl2W * sl2Diag a) = 1 := by
  have hcomm (b : Kˣ) :
      (sl2Diag b : Matrix.SpecialLinearGroup (Fin 2) K) * sl2W =
        sl2W * sl2Diag b⁻¹ := by
    calc (sl2Diag b : Matrix.SpecialLinearGroup (Fin 2) K) * sl2W
        = (sl2W * sl2W) * sl2Diag b * sl2W := by
          rw [sl2W_mul_self]
          group
      _ = sl2W * (sl2W * sl2Diag b) * sl2W := by group
      _ = sl2W * (sl2Diag b⁻¹ * sl2W) * sl2W := by rw [sl2W_mul_sl2Diag]
      _ = sl2W * (sl2Diag b⁻¹ * (sl2W * sl2W)) := by group
      _ = sl2W * sl2Diag b⁻¹ := by
          rw [sl2W_mul_self]
          group
  calc ((sl2W : Matrix.SpecialLinearGroup (Fin 2) K) * sl2Diag a) *
        (sl2W * sl2Diag a)
      = sl2W * (sl2Diag a * sl2W) * sl2Diag a := by group
    _ = sl2W * (sl2W * sl2Diag a⁻¹) * sl2Diag a := by rw [hcomm]
    _ = (sl2W * sl2W) * (sl2Diag a⁻¹ * sl2Diag a) := by group
    _ = 1 := by
        rw [sl2W_mul_self, ← map_mul, inv_mul_cancel, map_one, one_mul]

theorem sl2Diag_injective :
    Function.Injective (sl2Diag : Kˣ →* Matrix.SpecialLinearGroup (Fin 2) K) := by
  intro a b h
  have h00 := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 2) K =>
    (x : Matrix (Fin 2) (Fin 2) K) 0 0) h
  exact Units.ext (by simpa [coe_sl2Diag] using h00)

theorem orderOf_sl2Diag (a : Kˣ) :
    orderOf (sl2Diag a : Matrix.SpecialLinearGroup (Fin 2) K) = orderOf a :=
  orderOf_injective (sl2Diag : Kˣ →* Matrix.SpecialLinearGroup (Fin 2) K)
    sl2Diag_injective a

theorem sl2Diag_pow_24_ne_one [Finite K] {n : ℕ} (hn : 3 ≤ n)
    (hcard : Nat.card K = 2 ^ n) (a : Kˣ) (ha : orderOf a = Nat.card K - 1) :
    (sl2Diag a : Matrix.SpecialLinearGroup (Fin 2) K) ^ 24 ≠ 1 := by
  intro h
  have hdvd : orderOf (sl2Diag a : Matrix.SpecialLinearGroup (Fin 2) K) ∣ 24 :=
    orderOf_dvd_of_pow_eq_one h
  rw [orderOf_sl2Diag, ha, hcard] at hdvd
  have hq8 : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hle : 2 ^ n - 1 ≤ 24 := Nat.le_of_dvd (by norm_num) hdvd
  have hnle : n ≤ 4 := by
    by_contra h5
    have h5' : 5 ≤ n := by omega
    have hpow : 2 ^ 5 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h5'
    norm_num at hpow
    omega
  interval_cases n <;> norm_num at hdvd

theorem eq_top_of_normal_of_mem_sl2Diag_pow_24 [Finite K] {n : ℕ} (hn : 3 ≤ n)
    (hcard : Nat.card K = 2 ^ n) (a : Kˣ) (ha : orderOf a = Nat.card K - 1)
    {N : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)} [N.Normal]
    (hN : (sl2Diag a : Matrix.SpecialLinearGroup (Fin 2) K) ^ 24 ∈ N) : N = ⊤ := by
  classical
  haveI : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) K) := by
    haveI : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
        have hq8 : 8 ≤ 2 ^ n := by
          calc 8 = 2 ^ 3 := by norm_num
            _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
        rw [hcard]
        omega)
    exact (CFSG.Timmesfeld.RankOne.psl2EquivSL2 K).symm.isSimpleGroup
  have hne : N ≠ ⊥ := by
    intro hbot
    have hmem : (sl2Diag a : Matrix.SpecialLinearGroup (Fin 2) K) ^ 24 ∈
        (⊥ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)) := hbot ▸ hN
    exact sl2Diag_pow_24_ne_one hn hcard a ha (Subgroup.mem_bot.mp hmem)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact absurd h hne
  · exact h

end CFSG.LinearAlgebra

end
