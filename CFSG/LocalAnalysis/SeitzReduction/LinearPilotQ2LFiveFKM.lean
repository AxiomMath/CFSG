module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveEKM
public import CFSG.RankThree.PartOne.KC.CommonEigenbasis

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial

section FieldFour

variable {K : Type*} [Field K]

theorem unit_pow_three_of_card_eq_four (hK : Nat.card K = 4) (u : Kˣ) : u ^ 3 = 1 := by
  have h : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
  rw [← h]
  exact pow_card_eq_one'

theorem pow_three_of_ne_zero_of_card_four (hK : Nat.card K = 4) {a : K} (ha : a ≠ 0) :
    a ^ 3 = 1 := by
  have h := congrArg Units.val (unit_pow_three_of_card_eq_four hK (Units.mk0 a ha))
  simpa using h

theorem exists_isPrimitiveRoot_three_of_card_four [Finite K] (hK : Nat.card K = 4) :
    ∃ ζ : K, IsPrimitiveRoot ζ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 (by rw [h])
  refine ⟨(x : K), IsPrimitiveRoot.coe_units_iff.2 ?_⟩
  have := IsPrimitiveRoot.orderOf x
  rwa [hx] at this

theorem scalars_four_eq_bot_of_card_four (hK : Nat.card K = 4) : LinearFlag.scalars 4 K = ⊥ := by
  rw [eq_bot_iff]
  rintro A ⟨c, hc4, hA⟩
  rw [Subgroup.mem_bot]
  have hc3 := unit_pow_three_of_card_eq_four hK c
  have hc1 : c = 1 := by
    calc c = c ^ 3 * c := by rw [hc3, one_mul]
      _ = c ^ 4 := by rw [← pow_succ]
      _ = 1 := hc4
  apply Subtype.ext
  change (A : Matrix (Fin 4) (Fin 4) K) = 1
  rw [hA, hc1, Units.val_one, map_one]

theorem proj_four_injective_of_card_four (hK : Nat.card K = 4) :
    Function.Injective (LinearFlag.proj 4 K) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  rwa [LinearFlag.proj_eq_one_iff, scalars_four_eq_bot_of_card_four hK, Subgroup.mem_bot] at hA

end FieldFour

section Diagonal

variable {K : Type*} [Field K]

theorem mul_diagonal_eq_diagonal_mul_of_mem_blockSpecialLinear {n : ℕ} {i j : Fin n}
    {d : Fin n → K} (hd : d i = d j) {M : SpecialLinearGroup (Fin n) K}
    (hM : M ∈ blockSpecialLinear (K := K) ({i, j} : Finset (Fin n))) :
    (M : Matrix (Fin n) (Fin n) K) * diagonal d = diagonal d * (M : Matrix (Fin n) (Fin n) K) := by
  ext a b
  rw [mul_diagonal, diagonal_mul]
  by_cases hab : a = b
  · subst hab
    ring
  · by_cases hin : a ∈ ({i, j} : Finset (Fin n)) ∧ b ∈ ({i, j} : Finset (Fin n))
    · obtain ⟨ha, hb⟩ := hin
      have hdab : d a = d b := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
        rcases ha with ha | ha <;> rcases hb with hb | hb
        · exact absurd (ha.trans hb.symm) hab
        · rw [ha, hb, hd]
        · rw [ha, hb, hd]
        · exact absurd (ha.trans hb.symm) hab
      rw [hdab, mul_comm]
    · have h0 := (mem_blockSpecialLinear.1 hM) a b (not_and_or.1 hin)
      rw [h0, one_apply_ne hab, zero_mul, mul_zero]

end Diagonal

section OrderThree

variable {K : Type*} [Field K] [Finite K]

theorem exists_conj_rootSL2_le_centralizer_of_pow_three (hK : Nat.card K = 4)
    {y : LinearFlag.projectiveSL 4 K} (hy : y ^ 3 = 1) :
    ∃ (g : LinearFlag.projectiveSL 4 K) (i j : Fin 4), i ≠ j ∧
      (rootSL2 (K := K) i j).map (MulAut.conj g).toMonoidHom ≤
        centralizer ({y} : Set (LinearFlag.projectiveSL 4 K)) := by
  classical
  obtain ⟨A, rfl⟩ := LinearFlag.proj_surjective 4 K y
  have hA3 : A ^ 3 = 1 := proj_four_injective_of_card_four hK (by rw [map_pow, hy, map_one])
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_three_of_card_four hK
  have hcomm : ∀ x ∈ zpowers A, ∀ x' ∈ zpowers A, x * x' = x' * x := by
    intro x hx x' hx'
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
    obtain ⟨k', rfl⟩ := mem_zpowers_iff.1 hx'
    exact zpow_mul_comm A k k'
  have hpow : ∀ x ∈ zpowers A, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hA3, _root_.one_zpow]
  obtain ⟨B, hB⟩ := CFSG.RankThree.PartOne.exists_conj_diagonal_of_commuting_pow_eq_one hζ
    (zpowers A) hcomm hpow
  set Bm : Matrix (Fin 4) (Fin 4) K := (B : Matrix (Fin 4) (Fin 4) K) with hBm
  set Bi : Matrix (Fin 4) (Fin 4) K := ((B⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
    with hBi
  have hBBi : Bm * Bi = 1 := by
    rw [hBm, hBi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  set D : Matrix (Fin 4) (Fin 4) K := Bm * (A : Matrix (Fin 4) (Fin 4) K) * Bi with hD
  set d : Fin 4 → K := fun a => D a a with hd
  have hDd : D = diagonal d := by
    ext a b
    by_cases hab : a = b
    · subst hab
      simp [hd]
    · rw [diagonal_apply_ne _ hab]
      exact hB A (mem_zpowers A) a b hab
  have hdetB : Bm.det * Bi.det = 1 := by rw [← det_mul, hBBi, det_one]
  have hdetD : D.det = 1 := by
    rw [hD, det_mul, det_mul, A.2, mul_one, hdetB]
  have hd0 : ∀ a, d a ≠ 0 := by
    intro a ha
    have h1 : D.det = 0 := by
      rw [hDd, det_diagonal]
      exact Finset.prod_eq_zero (Finset.mem_univ a) ha
    rw [hdetD] at h1
    exact one_ne_zero h1
  obtain ⟨i, j, hdij, hij⟩ : ∃ i j : Fin 4, d i = d j ∧ i ≠ j := by
    have hni : ¬ Function.Injective (fun a => Units.mk0 (d a) (hd0 a)) := by
      intro hinj
      have h := Nat.card_le_card_of_injective _ hinj
      rw [Nat.card_units, hK] at h
      simp at h
    rw [Function.not_injective_iff] at hni
    obtain ⟨a, b, hab, hne⟩ := hni
    exact ⟨a, b, congrArg Units.val hab, hne⟩
  have hBdet : Bm.det ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hdetB
    exact zero_ne_one hdetB
  set lam : K := Bm.det⁻¹ with hlam
  have hlam0 : lam ≠ 0 := inv_ne_zero hBdet
  have hlam3 : lam ^ 3 = 1 := pow_three_of_ne_zero_of_card_four hK hlam0
  have hSdet : (lam • Bm).det = 1 := by
    rw [det_smul, Fintype.card_fin, show lam ^ 4 = lam ^ 3 * lam by ring, hlam3, one_mul, hlam,
      inv_mul_cancel₀ hBdet]
  obtain ⟨S, hSm⟩ : ∃ S : SpecialLinearGroup (Fin 4) K,
      (S : Matrix (Fin 4) (Fin 4) K) = lam • Bm := ⟨⟨lam • Bm, hSdet⟩, rfl⟩
  have hSS : ((S⁻¹ : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      (S : Matrix (Fin 4) (Fin 4) K) = 1 := by
    have h := congrArg (fun g : SpecialLinearGroup (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K))
      (inv_mul_cancel S)
    exact h
  have hSinv : ((S⁻¹ : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      lam⁻¹ • Bi := by
    have h1 : (S : Matrix (Fin 4) (Fin 4) K) * (lam⁻¹ • Bi) = 1 := by
      rw [hSm, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hlam0, one_smul,
        hBBi]
    calc ((S⁻¹ : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
        = ((S⁻¹ : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
            ((S : Matrix (Fin 4) (Fin 4) K) * (lam⁻¹ • Bi)) := by rw [h1, Matrix.mul_one]
      _ = (((S⁻¹ : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
            (S : Matrix (Fin 4) (Fin 4) K)) * (lam⁻¹ • Bi) := by rw [Matrix.mul_assoc]
      _ = lam⁻¹ • Bi := by rw [hSS, Matrix.one_mul]
  have hSAS : ((S * A * S⁻¹ : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      diagonal d := by
    show (S : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) *
      ((S⁻¹ : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = diagonal d
    rw [hSinv, hSm, ← hDd, hD]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hlam0, one_smul]
  have hcommM : ∀ M ∈ blockSpecialLinear (K := K) ({i, j} : Finset (Fin 4)),
      (S⁻¹ * M * S) * A = A * (S⁻¹ * M * S) := by
    intro M hM
    have h1 : M * (S * A * S⁻¹) = (S * A * S⁻¹) * M := by
      apply Subtype.ext
      show (M : Matrix (Fin 4) (Fin 4) K) *
          ((S * A * S⁻¹ : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        ((S * A * S⁻¹ : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          (M : Matrix (Fin 4) (Fin 4) K)
      rw [hSAS]
      exact mul_diagonal_eq_diagonal_mul_of_mem_blockSpecialLinear hdij hM
    calc (S⁻¹ * M * S) * A = S⁻¹ * (M * (S * A * S⁻¹)) * S := by group
      _ = S⁻¹ * ((S * A * S⁻¹) * M) * S := by rw [h1]
      _ = A * (S⁻¹ * M * S) := by group
  refine ⟨LinearFlag.proj 4 K S⁻¹, i, j, hij, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  rw [rootSL2_eq] at hz
  obtain ⟨M, hM, rfl⟩ := mem_blockSL.1 hz
  rw [mem_centralizer_singleton_iff]
  have hconj : (MulAut.conj (LinearFlag.proj 4 K S⁻¹)).toMonoidHom (LinearFlag.proj 4 K M) =
      LinearFlag.proj 4 K (S⁻¹ * M * S) := by
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_mul, map_inv, inv_inv]
  rw [hconj, ← map_mul, ← map_mul, hcommM M hM]

theorem exists_perfect_le_centralizer_of_pow_three_projectiveSL_four (hK : Nat.card K = 4)
    {y : LinearFlag.projectiveSL 4 K} (hy : y ^ 3 = 1) :
    ∃ P : Subgroup (LinearFlag.projectiveSL 4 K),
      P ≤ centralizer ({y} : Set (LinearFlag.projectiveSL 4 K)) ∧ ⁅P, P⁆ = P ∧
        5 ∣ Nat.card P := by
  obtain ⟨g, i, j, hij, hle⟩ := exists_conj_rootSL2_le_centralizer_of_pow_three hK hy
  refine ⟨_, hle, ?_, ?_⟩
  · rw [← Subgroup.map_commutator, rootSL2_eq,
      commutator_blockSL_eq_of_card_two (Finset.card_pair hij) (by rw [hK])]
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    obtain ⟨φ⟩ := rootSL2_mulEquiv (K := K) hij (by norm_num)
    rw [Nat.card_congr φ.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK]
    norm_num

end OrderThree

section Consequences

theorem lFourFourCentralizerOrderThreeInput_holds : LFourFourCentralizerOrderThreeInput := by
  intro X _ hX x hx
  obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hX
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  have hy : φ x ^ 3 = 1 := by rw [← map_pow, ← hx, pow_orderOf_eq_one, map_one]
  obtain ⟨P, hPC, hPperf, hP5⟩ :=
    exists_perfect_le_centralizer_of_pow_three_projectiveSL_four hK4 hy
  refine ⟨P.map φ.symm.toMonoidHom, ?_, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    have hp' := mem_centralizer_singleton_iff.1 (hPC hp)
    rw [mem_centralizer_singleton_iff]
    have h := congrArg φ.symm hp'
    simpa [map_mul] using h
  · rw [← Subgroup.map_commutator, hPperf]
  · rw [Subgroup.card_map_of_injective φ.symm.injective]
    exact hP5

theorem lFiveFieldNOneLiftInput_holds : LFiveFieldNOneLiftInput :=
  lFiveFieldNOneLiftInput_of_model lFourFourCentralizerOrderThreeInput_holds

end Consequences

end CFSG.SeitzReduction.LinearPilot
