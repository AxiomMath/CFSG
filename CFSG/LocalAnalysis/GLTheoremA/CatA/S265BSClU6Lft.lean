module

public import CFSG.RankThree.PartOne.KC.UnitaryGoodModel
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.PsuBadAux.SixTwoCount
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BU8Supp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.BSCl

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryModel

variable {K : Type} [Field K]

private theorem units_pow_three_of_card (hK : Nat.card K = 4) (u : Kˣ) : u ^ 3 = 1 := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have hc : Nat.card Kˣ = 3 := by
    have := Nat.card_units K
    rw [hK] at this
    simpa using this
  rw [← hc]
  exact pow_card_eq_one'

private theorem units_pow_three (h : UnitaryFieldData 2 1 K) (u : Kˣ) : u ^ 3 = 1 :=
  units_pow_three_of_card (h.card.trans (by norm_num)) u

private theorem pow_three_of_ne_zero (hK : Nat.card K = 4) {x : K} (hx : x ≠ 0) : x ^ 3 = 1 := by
  have := congrArg Units.val (units_pow_three_of_card hK (Units.mk0 x hx))
  rwa [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one] at this

private theorem eq_one_of_scalar_eq_one {z : Kˣ} (hz : GeneralLinearGroup.scalar (Fin 6) z = 1) :
    z = 1 := by
  have e := congrArg (fun g : GL (Fin 6) K => (g : Matrix (Fin 6) (Fin 6) K) 0 0) hz
  simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
    Units.val_one, Matrix.one_apply_eq] at e
  exact Units.ext e

private theorem exists_scalar_of_conjHom_commute (h : UnitaryFieldData 2 1 K)
    {X Y : primeFormUnitary h (idGram K 6)}
    (hXY : primeFormConjHom h (idGram K 6) X * primeFormConjHom h (idGram K 6) Y =
      primeFormConjHom h (idGram K 6) Y * primeFormConjHom h (idGram K 6) X) :
    ∃ z : Kˣ, ((X * Y * X⁻¹ : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) =
      GeneralLinearGroup.scalar (Fin 6) z * (Y : GL (Fin 6) K) := by
  have h1 : primeFormConjHom h (idGram K 6) (X * Y * X⁻¹ * Y⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hXY, mul_inv_cancel_right, mul_inv_cancel]
  obtain ⟨z, -, hz⟩ := (primeFormConjHom_eq_one_iff_of_ne (by norm_num) (by norm_num) _).1 h1
  refine ⟨z, ?_⟩
  rw [← hz]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right]

theorem commute_of_conjHom_commute_of_pow_eleven (h : UnitaryFieldData 2 1 K)
    {X Y : primeFormUnitary h (idGram K 6)}
    (hXY : primeFormConjHom h (idGram K 6) X * primeFormConjHom h (idGram K 6) Y =
      primeFormConjHom h (idGram K 6) Y * primeFormConjHom h (idGram K 6) X)
    (hY : Y ^ 11 = 1) : X * Y = Y * X := by
  obtain ⟨z, hz⟩ := exists_scalar_of_conjHom_commute h hXY
  have hc : Commute (GeneralLinearGroup.scalar (Fin 6) z) (Y : GL (Fin 6) K) :=
    GeneralLinearGroup.scalar_commute z _
  have h11 := congrArg (· ^ 11) hz
  rw [← Subgroup.coe_pow, conj_pow, hY, mul_one, mul_inv_cancel, Subgroup.coe_one, hc.mul_pow,
    ← Subgroup.coe_pow, hY, Subgroup.coe_one, mul_one, ← map_pow] at h11
  have hz11 : z ^ 11 = 1 := eq_one_of_scalar_eq_one h11.symm
  have hz1 : z = 1 := by
    calc z = (z ^ 3) ^ 4 * (z ^ 11)⁻¹ := by group
      _ = 1 := by rw [units_pow_three h z, hz11]; group
  rw [hz1, map_one, one_mul] at hz
  exact mul_inv_eq_iff_eq_mul.1 (Subtype.ext hz)

theorem commute_of_conjHom_commute_of_trace (h : UnitaryFieldData 2 1 K)
    {X Y : primeFormUnitary h (idGram K 6)}
    (hXY : primeFormConjHom h (idGram K 6) X * primeFormConjHom h (idGram K 6) Y =
      primeFormConjHom h (idGram K 6) Y * primeFormConjHom h (idGram K 6) X)
    (hY : trace ((Y : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) ≠ 0) : X * Y = Y * X := by
  obtain ⟨z, hz⟩ := exists_scalar_of_conjHom_commute h hXY
  have htr := congrArg (fun g : GL (Fin 6) K => trace (g : Matrix (Fin 6) (Fin 6) K)) hz
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply, ← smul_eq_diagonal_mul, trace_smul, smul_eq_mul] at htr
  rw [trace_mul_cycle, Units.inv_mul, Matrix.one_mul] at htr
  have hz1 : z = 1 := Units.ext (by
    rw [Units.val_one]
    exact (mul_eq_right₀ hY).1 htr.symm)
  rw [hz1, map_one, one_mul] at hz
  exact mul_inv_eq_iff_eq_mul.1 (Subtype.ext hz)

theorem exists_lift_pow_eleven_six (h : UnitaryFieldData 2 1 K)
    {y : MulAut (primeFormP h (idGram K 6))} (hyD : y ∈ primeFormD h (idGram K 6))
    (hy : y ^ 11 = 1) :
    ∃ Y : primeFormUnitary h (idGram K 6), primeFormConjHom h (idGram K 6) Y = y ∧ Y ^ 11 = 1 := by
  obtain ⟨Y₀, rfl⟩ := hyD
  refine ⟨Y₀ ^ 12, by rw [map_pow, pow_succ, hy, one_mul], ?_⟩
  have h1 : primeFormConjHom h (idGram K 6) (Y₀ ^ 11) = 1 := by rw [map_pow, hy]
  obtain ⟨z, -, hz⟩ := (primeFormConjHom_eq_one_iff_of_ne (by norm_num) (by norm_num) _).1 h1
  apply Subtype.ext
  rw [← pow_mul, show 12 * 11 = 11 * 12 by norm_num, pow_mul, Subgroup.coe_pow, hz, ← map_pow,
    show 12 = 3 * 4 by norm_num, pow_mul, units_pow_three h z, one_pow, map_one, Subgroup.coe_one]

private theorem mulVec_single_eq_of_commute_diagonal (hK : Nat.card K = 4)
    {Y : Matrix (Fin 6) (Fin 6) K} (hY : Y ^ 11 = 1) {a : Fin 6 → K}
    (hYa : Y * diagonal a = diagonal a * Y) {k : Fin 6} (hk : ∀ i, i ≠ k → a i ≠ a k) :
    Y *ᵥ Pi.single k 1 = Pi.single k 1 := by
  have hcol : Y *ᵥ Pi.single k 1 = Y k k • Pi.single k 1 := by
    rw [mulVec_single_one]
    funext i
    by_cases hi : i = k
    · subst hi
      simp
    · rw [col_apply, Pi.smul_apply, Pi.single_eq_of_ne hi, smul_zero]
      by_contra hne
      exact hk i hi (CFSG.LocalAnalysis.GLTheoremA.S265BU8.eq_of_mul_diagonal_eq hYa hne)
  have hpow : ∀ m : ℕ, (Y ^ m) *ᵥ Pi.single k 1 = Y k k ^ m • Pi.single k 1 := by
    intro m
    induction m with
    | zero => rw [pow_zero, one_mulVec, pow_zero, one_smul]
    | succ m ih =>
      rw [pow_succ, ← mulVec_mulVec, hcol, mulVec_smul, ih, smul_smul, pow_succ, mul_comm]
  have h11 : Y k k ^ 11 = 1 := by
    have e := congrFun (hpow 11) k
    rw [hY, one_mulVec] at e
    simpa using e.symm
  have hne : Y k k ≠ 0 := fun h0 => by
    rw [h0] at h11
    norm_num at h11
  have h1 : Y k k = 1 := by
    calc Y k k = (Y k k ^ 3) ^ 4 * (Y k k ^ 11)⁻¹ := by field_simp
      _ = 1 := by rw [pow_three_of_ne_zero hK hne, h11]; norm_num
  rw [hcol, h1, one_smul]

theorem eq_one_of_commute_diagonal_pair_six (hK : Nat.card K = 4) {Y : Matrix (Fin 6) (Fin 6) K}
    (hY : Y ^ 11 = 1) {a b : Fin 6 → K} (hYa : Y * diagonal a = diagonal a * Y)
    (hYb : Y * diagonal b = diagonal b * Y) {k k' : Fin 6} (hkk' : k ≠ k')
    (ha : ∀ i, i ≠ k → a i ≠ a k) (hb : ∀ i, i ≠ k' → b i ≠ b k') : Y = 1 := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  by_contra hne
  obtain ⟨F, hF, h1⟩ := CFSG.HardMathSupport.Dickson.Sec6.I923.finrank_fixed_eq_one hK Y hY hne
  have hkF : (Pi.single k 1 : Fin 6 → K) ∈ F :=
    (hF _).2 (mulVec_single_eq_of_commute_diagonal hK hY hYa ha)
  have hk'F : (Pi.single k' 1 : Fin 6 → K) ∈ F :=
    (hF _).2 (mulVec_single_eq_of_commute_diagonal hK hY hYb hb)
  have hnz : (⟨Pi.single k 1, hkF⟩ : F) ≠ 0 := fun h0 => by
    have e := congrArg (fun v : F => (v : Fin 6 → K) k) h0
    simp at e
  obtain ⟨t, ht⟩ := (finrank_eq_one_iff_of_nonzero' _ hnz).1 h1 ⟨_, hk'F⟩
  have e := congrArg (fun v : F => (v : Fin 6 → K) k') ht
  simp [Pi.single_apply, hkk'.symm] at e

end CFSG.LocalAnalysis.GLTheoremA.S265.BSCl

end
