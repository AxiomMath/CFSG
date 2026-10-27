module

public import CFSG.ClassicalInvolution.Asc77.AscSCH17

public section

namespace CFSG.ClassicalInvolution.Asc77.SCH

open Matrix CFSG.SectionRank.OddCover CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K]

theorem det_cyc4Mat : (cyc4Mat (K := K)).det = 1 := by
  simp [cyc4Mat, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]

theorem det_w02Mat : (w02Mat (K := K)).det = 1 := by
  simp [w02Mat, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]

theorem det_w13Mat : (w13Mat (K := K)).det = 1 := by
  simp [w13Mat, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]

theorem det_w01Mat : (w01Mat (K := K)).det = 1 := by
  simp [w01Mat, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]

theorem det_cyc4GL : ((cyc4GL : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = 1 := det_cyc4Mat

theorem det_w02GL : ((w02GL : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = 1 := det_w02Mat

theorem det_w13GL : ((w13GL : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = 1 := det_w13Mat

theorem det_w01GL : ((w01GL : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = 1 := det_w01Mat

theorem det_torY₁ (m : Kˣ) : ((torY₁ m : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = 1 := by
  rw [torY₁, det_diagHom]
  simp [Fin.prod_univ_four]

theorem det_torY₂ (m : Kˣ) : ((torY₂ m : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = 1 := by
  rw [torY₂, det_diagHom]
  simp [Fin.prod_univ_four]

theorem det_torY₃ (m : Kˣ) : ((torY₃ m : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = 1 := by
  rw [torY₃, det_diagHom]
  simp [Fin.prod_univ_four]

theorem card_statedSL_four [Finite K] :
    Nat.card (StatedSL 4 K) =
      Nat.card K ^ 6 * (Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1) * (Nat.card K ^ 4 - 1) := by
  have := Fintype.ofFinite K
  rw [← Nat.card_congr (specialLinearGroupEquivStatedSL 4 K).toEquiv, Matrix.card_SL_field,
    ← Nat.card_eq_fintype_card, Fin.prod_univ_four]
  have h3v : ((3 : Fin 4) : ℕ) = 3 := rfl
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, h3v, pow_zero, pow_one]
  set q := Nat.card K
  have hq : 2 ≤ q := Finite.one_lt_card
  have h1 : 1 ≤ q := by omega
  have e2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have e3 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
  have e4 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ (by omega)
  have f1 : q ≤ q ^ 4 := Nat.le_self_pow (by norm_num) q
  have f2 : q ^ 2 ≤ q ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have f3 : q ^ 3 ≤ q ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hprod : (q ^ 4 - 1) * (q ^ 4 - q) * (q ^ 4 - q ^ 2) * (q ^ 4 - q ^ 3) =
      (q - 1) * (q ^ 6 * (q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1)) := by
    zify [e2, e3, e4, f1, f2, f3, h1, Nat.one_le_pow 6 q h1]
    ring
  rw [hprod, Nat.mul_div_cancel_left _ (by omega)]

section Arith

theorem fac_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a * b).factorization 3 = a.factorization 3 + b.factorization 3 := by
  simp [Nat.factorization_mul ha hb]

theorem fac_zero {n : ℕ} (h : ¬ 3 ∣ n) : n.factorization 3 = 0 :=
  Nat.factorization_eq_zero_of_not_dvd h

theorem factorization_sl4_one {q : ℕ} (h3 : 3 ∣ q - 1) (hq : 2 ≤ q) :
    (q ^ 6 * (q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1)).factorization 3 =
      3 * (q - 1).factorization 3 + 1 := by
  have hq3 : q % 3 = 1 := by omega
  have hqn : ¬ 3 ∣ q := by omega
  have hq1 : ¬ 3 ∣ q + 1 := by omega
  have hq2 : ¬ 3 ∣ q ^ 2 + 1 := by
    have : q ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hq3]
    omega
  have hq1' : 1 ≤ q := by omega
  have d2 : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    zify [hq1', Nat.one_le_pow 2 q hq1']
    ring
  have d3 : q ^ 3 - 1 = (q - 1) * (q ^ 2 + q + 1) := by
    zify [hq1', Nat.one_le_pow 3 q hq1']
    ring
  have d4 : q ^ 4 - 1 = (q - 1) * ((q + 1) * (q ^ 2 + 1)) := by
    zify [hq1', Nat.one_le_pow 4 q hq1']
    ring
  have n1 : q - 1 ≠ 0 := by omega
  have n2 : q + 1 ≠ 0 := by omega
  have n3 : q ^ 2 + q + 1 ≠ 0 := by positivity
  have n4 : q ^ 2 + 1 ≠ 0 := by positivity
  have n5 : q ≠ 0 := by omega
  rw [d2, d3, d4, fac_mul (by positivity) (by positivity), fac_mul (by positivity) (by positivity),
    fac_mul (by positivity) (by positivity), fac_mul n1 n2, fac_mul n1 n3,
    fac_mul n1 (by positivity), fac_mul n2 n4, Nat.factorization_pow, Finsupp.smul_apply,
    smul_eq_mul, fac_zero hqn, fac_zero hq1, fac_zero hq2,
    factorization_sq_add_add_one Nat.prime_three hq1' h3, Nat.Prime.factorization_self
      Nat.prime_three]
  ring

theorem factorization_su4_two {q : ℕ} (h3 : 3 ∣ q + 1) (hq : 2 ≤ q) :
    (q ^ 6 * (q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1)).factorization 3 =
      3 * (q + 1).factorization 3 + 1 := by
  have hq3 : q % 3 = 2 := by omega
  have hqn : ¬ 3 ∣ q := by omega
  have hq1 : ¬ 3 ∣ q - 1 := by omega
  have hq2 : ¬ 3 ∣ q ^ 2 + 1 := by
    have : q ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hq3]
    omega
  have hq1' : 1 ≤ q := by omega
  have d2 : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    zify [hq1', Nat.one_le_pow 2 q hq1']
    ring
  have hqq : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
  have d3 : q ^ 3 + 1 = (q + 1) * (q ^ 2 - q + 1) := by
    zify [hq1', hqq]
    ring
  have d4 : q ^ 4 - 1 = (q - 1) * ((q + 1) * (q ^ 2 + 1)) := by
    zify [hq1', Nat.one_le_pow 4 q hq1']
    ring
  have n1 : q - 1 ≠ 0 := by omega
  have n2 : q + 1 ≠ 0 := by omega
  have n3 : q ^ 2 - q + 1 ≠ 0 := by omega
  have n4 : q ^ 2 + 1 ≠ 0 := by positivity
  have n5 : q ≠ 0 := by omega
  rw [d2, d3, d4, fac_mul (by positivity) (by positivity), fac_mul (by positivity) (by positivity),
    fac_mul (by positivity) (by positivity), fac_mul n1 n2, fac_mul n2 n3,
    fac_mul n1 (by positivity), fac_mul n2 n4, Nat.factorization_pow, Finsupp.smul_apply,
    smul_eq_mul, fac_zero hqn, fac_zero hq1, fac_zero hq2,
    factorization_sq_sub_add_one Nat.prime_three h3, Nat.Prime.factorization_self
      Nat.prime_three]
  ring

end Arith

section SL

theorem statedSL_four_perfect_ker_eq_bot_one [Finite K] (h3 : 3 ∣ Nat.card K - 1) {E : Type*}
    [Group E] [Finite E] [Group.IsPerfect E] (π : E →* StatedSL 4 K)
    (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E) (hCp : IsPGroup 3 π.ker) :
    π.ker = ⊥ := by
  obtain ⟨m, hm⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf m = Nat.card K - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hm, Nat.card_units]
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  refine ker_eq_bot_of_monomial_torus m (StatedSL 4 K) (Subgroup.subset_closure (det_torY₁ m))
    (Subgroup.subset_closure (det_torY₂ m)) (Subgroup.subset_closure (det_torY₃ m))
    (Subgroup.subset_closure det_cyc4GL) (Subgroup.subset_closure det_w02GL)
    (Subgroup.subset_closure det_w13GL) (Subgroup.subset_closure det_w01GL) ?_ π hπ hC hCp
  rw [card_statedSL_four, hord, factorization_sl4_one h3 hq]

end SL

end CFSG.ClassicalInvolution.Asc77.SCH
