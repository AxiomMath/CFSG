module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FamilyArith
public import CFSG.LieType.Steinberg.CentralExt.GriessNativeModels
public import CFSG.RankThree.PartTwo.KFacts.KS44Multiplier
public import CFSG.Timmesfeld.Orders.Classical

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open CFSG.Blueprint CFSG.Open Polynomial

theorem matrix_pow_three_eq_zero {K : Type*} [Field K] {N : Matrix (Fin 3) (Fin 3) K}
    (h : IsNilpotent N) : N ^ 3 = 0 := by
  have hφ : IsNilpotent (Matrix.toLinAlgEquiv' N) := h.map (Matrix.toLinAlgEquiv' : _ ≃ₐ[K] _)
  have hc := hφ.charpoly_eq_X_pow_finrank
  have h0 := LinearMap.aeval_self_charpoly (Matrix.toLinAlgEquiv' N)
  rw [hc, map_pow, Polynomial.aeval_X, Module.finrank_fin_fun] at h0
  exact (Matrix.toLinAlgEquiv' (R := K) (n := Fin 3)).injective (by rw [map_pow, h0, map_zero])

theorem matrix_pow_four_eq_one_of_pow_eight {K : Type*} [Field K] [CharP K 2]
    {A : Matrix (Fin 3) (Fin 3) K} (h : A ^ 8 = 1) : A ^ 4 = 1 := by
  have hp : ((X : K[X]) - 1) ^ 8 = X ^ 8 - 1 := by
    simpa using sub_pow_char_pow (X : K[X]) (1 : K[X]) (p := 2) (n := 3)
  have hN : (A - 1) ^ 8 = 0 := by
    have := congrArg (Polynomial.aeval A) hp
    simp only [map_pow, map_sub, aeval_X, map_one, h, sub_self] at this
    exact this
  have h3 : (A - 1) ^ 3 = 0 := matrix_pow_three_eq_zero ⟨8, hN⟩
  have hp4 : ((X : K[X]) - 1) ^ 4 = X ^ 4 - 1 := by
    simpa using sub_pow_char_pow (X : K[X]) (1 : K[X]) (p := 2) (n := 2)
  have h4 : (A - 1) ^ 4 = 0 := by rw [pow_succ, h3, zero_mul]
  have := congrArg (Polynomial.aeval A) hp4
  simp only [map_pow, map_sub, aeval_X, map_one] at this
  rw [h4] at this
  exact (sub_eq_zero.1 this.symm)

theorem projSL_three_no_order_eight {K : Type} [Field K] [CharP K 2]
    (g : ↥(CFSG.Assembly.RankThreeEven.projSL 3 K)) : orderOf g ≠ 8 := by
  intro h8
  have hg8 : g ^ 8 = 1 := by rw [← h8]; exact pow_orderOf_eq_one g
  obtain ⟨A, hA, hAg⟩ := g.2
  have h1 : Matrix.ProjGenLinGroup.mk (A ^ 8) = 1 := by
    rw [map_pow, hAg]
    exact congrArg Subtype.val hg8
  have h2 : A ^ 8 ∈ Subgroup.center (Matrix.GeneralLinearGroup (Fin 3) K) :=
    (QuotientGroup.eq_one_iff _).1 h1
  obtain ⟨a, ha⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.1 h2
  have hdet : (A : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    have := congrArg Units.val (MonoidHom.mem_ker.1 hA)
    simpa using this
  have ha3 : a ^ 3 = 1 := by
    have h := congrArg Matrix.det ha
    simp only [Units.val_pow_eq_pow_val, Matrix.det_pow, hdet, one_pow] at h
    simpa [Matrix.scalar_apply, Matrix.det_diagonal] using h
  have hM24 : ((A : Matrix (Fin 3) (Fin 3) K) ^ 3) ^ 8 = 1 := by
    have e : ((A : Matrix (Fin 3) (Fin 3) K) ^ 3) ^ 8 =
        ((A : Matrix (Fin 3) (Fin 3) K) ^ 8) ^ 3 := by
      rw [← pow_mul, ← pow_mul, mul_comm]
    rw [e, ← Units.val_pow_eq_pow_val, ← ha, ← map_pow, ha3, map_one]
  have hM12 : (A : Matrix (Fin 3) (Fin 3) K) ^ 12 = 1 := by
    have := matrix_pow_four_eq_one_of_pow_eight hM24
    rwa [← pow_mul] at this
  have hA12 : A ^ 12 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hM12]; rfl)
  have hg12 : g ^ 12 = 1 := by
    apply Subtype.ext
    show (g : Matrix.ProjGenLinGroup (Fin 3) K) ^ 12 = 1
    rw [← hAg, ← map_pow, hA12, map_one]
  have := orderOf_dvd_of_pow_eq_one hg12
  rw [h8] at this
  omega

theorem lieModel_psl_three_no_order_eight {X : Type} [Group X] {n : ℕ} (hn : 1 ≤ n)
    (h : LieModel X .PSL 3 2 n) (g : X) : orderOf g ≠ 8 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ :=
    CFSG.LieType.Steinberg.CentralExt.GriessNative.classical_of_lieModel h (by decide)
  have : CharP K 2 :=
    CFSG.LieType.Steinberg.CentralExt.GriessNative.charP_two_of_card hn hK rfl
  let e' : X ≃* CFSG.Assembly.RankThreeEven.projSL 3 K :=
    e.trans (CFSG.RankThree.PartTwo.KFacts.KS44.projSLEquivStatedProj K).symm
  rw [← e'.orderOf_eq]
  exact projSL_three_no_order_eight (e' g)

theorem card_of_lieModel_psl_three {X : Type} [Group X] {n : ℕ} (h : LieModel X .PSL 3 2 n) :
    Nat.card X = ordA 2 (2 ^ n) := by
  rcases h with ⟨-, hc⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · exact (CFSG.Timmesfeld.card_statedClassicalModel_two hc).1 rfl
  all_goals exact absurd h0 (by norm_num)

theorem padicValNat_ordA {n : ℕ} (hn : 1 ≤ n) : padicValNat 2 (ordA 2 (2 ^ n)) = 3 * n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2n : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have h2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h3 : 2 ∣ (2 ^ n) ^ 3 := dvd_pow h2n (by norm_num)
  have h22 : 2 ∣ (2 ^ n) ^ 2 := dvd_pow h2n (by norm_num)
  have h3' : 1 ≤ (2 ^ n) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h22' : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have ho3 : ¬ 2 ∣ (2 ^ n) ^ 3 - 1 := by omega
  have ho2 : ¬ 2 ∣ (2 ^ n) ^ 2 - 1 := by omega
  have hne3 : (2 ^ n) ^ 3 - 1 ≠ 0 := by
    intro h
    have : (2 ^ n) ^ 3 = 1 := by omega
    have : 2 ^ 3 ≤ (2 ^ n) ^ 3 := Nat.pow_le_pow_left h2 3
    omega
  have hne2 : (2 ^ n) ^ 2 - 1 ≠ 0 := by
    intro h
    have : (2 ^ n) ^ 2 = 1 := by omega
    have : 2 ^ 2 ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left h2 2
    omega
  set T := (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) with hT
  set d := Nat.gcd 3 (2 ^ n - 1) with hd
  have hd3 : d ∣ 3 := Nat.gcd_dvd_left _ _
  have hdodd : ¬ 2 ∣ d := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hd3 with h | h <;> rw [h] <;> omega
  have hdT : d ∣ T := by
    have h1 : d ∣ 2 ^ n - 1 := Nat.gcd_dvd_right _ _
    have h2 : 2 ^ n - 1 ∣ (2 ^ n) ^ 2 - 1 := Nat.sub_one_dvd_pow_sub_one (2 ^ n) 2
    exact ((h1.trans h2).mul_right _).mul_left _
  have hv : padicValNat 2 T = 3 * n := by
    rw [hT, padicValNat.mul (by positivity) (mul_ne_zero hne2 hne3),
      padicValNat.mul hne2 hne3, padicValNat.eq_zero_of_not_dvd ho3,
      padicValNat.eq_zero_of_not_dvd ho2, ← pow_mul, padicValNat.prime_pow]
    ring
  have hTd : T / d * d = T := Nat.div_mul_cancel hdT
  have hTdne : T / d ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hTd
    rw [hT] at hTd
    have : (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) ≠ 0 := by positivity
    exact this hTd.symm
  have hd0 : d ≠ 0 := Nat.gcd_ne_zero_left (by norm_num)
  rw [ordA_two]
  have := congrArg (padicValNat 2) hTd
  rw [padicValNat.mul hTdne hd0, padicValNat.eq_zero_of_not_dvd hdodd, add_zero, hv] at this
  exact this

theorem ordA_ne_suz {n : ℕ} (hn : 1 ≤ n) : ordA 2 (2 ^ n) ≠ 448345497600 := by
  intro h
  have := padicValNat_ordA hn
  rw [h] at this
  have h13 : padicValNat 2 448345497600 = 13 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have e : (448345497600 : ℕ) = 2 ^ 13 * 54729675 := by norm_num
    rw [e, padicValNat.mul (by positivity) (by norm_num), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by norm_num)]
  omega

theorem ordA_ne_on {n : ℕ} (hn : 1 ≤ n) : ordA 2 (2 ^ n) ≠ 460815505920 := by
  intro h
  have := padicValNat_ordA hn
  rw [h] at this
  have h9 : padicValNat 2 460815505920 = 9 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have e : (460815505920 : ℕ) = 2 ^ 9 * 900030285 := by norm_num
    rw [e, padicValNat.mul (by positivity) (by norm_num), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by norm_num)]
  have hn3 : n = 3 := by omega
  subst hn3
  rw [ordA_two] at h
  norm_num at h

theorem lieModel_psl_three_four_equiv {A B : Type} [Group A] [Group B]
    (hA : LieModel A .PSL 3 2 2) (hB : LieModel B .PSL 3 2 2) : Nonempty (A ≃* B) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ :=
    CFSG.LieType.Steinberg.CentralExt.GriessNative.classical_of_lieModel hA (by decide)
  obtain ⟨-, K', _, _, hK', ⟨e'⟩⟩ :=
    CFSG.LieType.Steinberg.CentralExt.GriessNative.classical_of_lieModel hB (by decide)
  obtain ⟨f⟩ := CFSG.LieType.Multipliers.L34.nonempty_mulEquiv_PSL3 hK e
  obtain ⟨f'⟩ := CFSG.LieType.Multipliers.L34.nonempty_mulEquiv_PSL3 hK' e'
  exact ⟨f.symm.trans f'⟩

end CFSG.EvenSporadicStandard.Induction
