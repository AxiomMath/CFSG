module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SemisimpleCentralizers.HeldUnitaryComponents
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419

open CFSG.Open CFSG.Open.StatedAPI Matrix
open CFSG.LieType.SemisimpleCentralizers.Held (heldSU mem_heldGU)

private theorem scalar_injective_of_ne_zero {E : Type} [Field E] {n : ℕ} (hn : n ≠ 0)
    (x y : Eˣ) (h : Matrix.GeneralLinearGroup.scalar (Fin n) x =
      Matrix.GeneralLinearGroup.scalar (Fin n) y) : x = y := by
  haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
  apply Units.ext
  exact Matrix.scalar_inj.mp (by
    simpa only [Matrix.GeneralLinearGroup.coe_scalar] using
      congrArg (fun g : GL (Fin n) E => (g : Matrix (Fin n) (Fin n) E)) h)

theorem k1419ClsUniCentreSU {E : Type} [Field E] [Finite E] {q a : ℕ} (hq : ∃ j : ℕ, q = 2 ^ j)
    (τ' : E ≃+* E) (hτ' : ∀ x, τ' (τ' x) = x) (hτ'q : ∀ x, τ' x = x ^ q)
    (hE : Nat.card E = q ^ 2) (ha2 : 2 ≤ a) (ha : 3 ∣ a) (hq3 : 3 ∣ q + 1) :
    ∃ z : GL (Fin a) E, z ∈ heldSU a E τ' hτ' ∧ z ≠ 1 ∧ z ^ 3 = 1 ∧
      ∀ y ∈ heldSU a E τ' hτ', z * y = y * z := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq2 : 2 ≤ q := CFSG.Open.StatedCenterThree.two_le_of_card_eq_sq hE
  have h3units : 3 ∣ Nat.card Eˣ := by
    rw [Nat.card_units, hE, CFSG.Open.StatedCenterThree.sq_sub_one_eq (by omega : 1 ≤ q)]
    exact dvd_mul_of_dvd_right hq3 (q - 1)
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Eˣ) 3 h3units
  have hu3 : u ^ 3 = 1 := by
    rw [← hu]
    exact pow_orderOf_eq_one u
  have hu_ne : u ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hu
    omega
  have hω3 : (u : E) ^ 3 = 1 := by
    have := congrArg (fun x : Eˣ => (x : E)) hu3
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using this
  have hωq1 : (u : E) ^ (q + 1) = 1 := by
    obtain ⟨m, hm⟩ := hq3
    rw [hm, pow_mul, hω3, one_pow]
  have hscalarinj := scalar_injective_of_ne_zero (E := E) (n := a) (by omega)
  refine ⟨Matrix.GeneralLinearGroup.scalar (Fin a) u, ?_, ?_, ?_, ?_⟩
  · rw [heldSU]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [mem_heldGU]
      rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.diagonal_map (map_zero τ'), Matrix.diagonal_transpose,
        Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      rw [hτ'q, ← pow_succ, hωq1]
    · rw [mem_statedSL_iff]
      rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      obtain ⟨m, hm⟩ := ha
      rw [hm, pow_mul, hω3, one_pow]
  · intro hz1
    exact hu_ne (hscalarinj u 1 (by simpa using hz1))
  · rw [← map_pow, hu3, map_one]
  · intro y hy
    exact Matrix.GeneralLinearGroup.scalar_commute u y

theorem k1419ClsUniCentreSL {E : Type} [Field E] [Finite E] {b : ℕ} (hb2 : 2 ≤ b) (hb : 3 ∣ b)
    (hE : 3 ∣ Nat.card E - 1) :
    ∃ z : GL (Fin b) E, z ∈ StatedSL b E ∧ z ≠ 1 ∧ z ^ 3 = 1 ∧
      ∀ y ∈ StatedSL b E, z * y = y * z := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3units : 3 ∣ Nat.card Eˣ := by rwa [Nat.card_units]
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Eˣ) 3 h3units
  have hu3 : u ^ 3 = 1 := by
    rw [← hu]
    exact pow_orderOf_eq_one u
  have hu_ne : u ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hu
    omega
  have hω3 : (u : E) ^ 3 = 1 := by
    have := congrArg (fun x : Eˣ => (x : E)) hu3
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using this
  have hscalarinj := scalar_injective_of_ne_zero (E := E) (n := b) (by omega)
  refine ⟨Matrix.GeneralLinearGroup.scalar (Fin b) u, ?_, ?_, ?_, ?_⟩
  · rw [mem_statedSL_iff]
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    obtain ⟨m, hm⟩ := hb
    rw [hm, pow_mul, hω3, one_pow]
  · intro hz1
    exact hu_ne (hscalarinj u 1 (by simpa using hz1))
  · rw [← map_pow, hu3, map_one]
  · intro y hy
    exact Matrix.GeneralLinearGroup.scalar_commute u y

end CFSG.LocalAnalysis.GLTheoremA.K1419
