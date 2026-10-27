module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.LinearAlgebra.PrimitiveRootEigenspaces
import TauCeti.GroupTheory.Commutator
import Mathlib.Data.Nat.Choose.Dvd

public section

namespace CFSG.LinearAlgebra

open Module Polynomial Matrix
open scoped commutatorElement

variable {F : Type*} [Field F] {n : ℕ}

theorem X_pow_sub_C_irreducible_of_prime_of_units {p : ℕ} (hp : p.Prime) {c : Fˣ}
    (hc : ∀ d : Fˣ, d ^ p ≠ c) : Irreducible (X ^ p - C (c : F)) := by
  refine X_pow_sub_C_irreducible_of_prime hp fun b hb => ?_
  rcases eq_or_ne b 0 with rfl | hb0
  · rw [zero_pow hp.ne_zero] at hb
    exact c.ne_zero hb.symm
  · refine hc (Units.mk0 b hb0) ?_
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0]
    exact hb

theorem eq_or_exists_pow_mul_eq {p : ℕ} (hp : p.Prime) {dA dB : Fin n → F}
    (hA : ∀ l, dA l ^ p = 1) (hB : ∀ l, dB l ^ p = 1) (i j : Fin n) :
    dA i = dA j ∨ ∃ k : ℕ, dA i ^ k * dB i = dA j ^ k * dB j := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  by_cases h : dA i = dA j
  · exact Or.inl h
  right
  have hne : ∀ l, dA l ≠ 0 := fun l => (IsUnit.of_pow_eq_one (hA l) hp.ne_zero).ne_zero
  have hBne : ∀ l, dB l ≠ 0 := fun l => (IsUnit.of_pow_eq_one (hB l) hp.ne_zero).ne_zero
  set α : F := dA i / dA j with hαdef
  have hα1 : α ≠ 1 := fun h1 => h ((div_eq_one_iff_eq (hne j)).1 h1)
  have hαp : α ^ p = 1 := by rw [hαdef, div_pow, hA i, hA j, div_one]
  have hprim : IsPrimitiveRoot α p :=
    IsPrimitiveRoot.iff_orderOf.2 (orderOf_eq_prime hαp hα1)
  have hβp : (dB j / dB i) ^ p = 1 := by rw [div_pow, hB j, hB i, div_one]
  obtain ⟨k, -, hk⟩ := hprim.eq_pow_of_pow_eq_one hβp
  refine ⟨k, ?_⟩
  have h1 : dB j / dB i = dA i ^ k / dA j ^ k := by rw [← hk, hαdef, div_pow]
  rw [div_eq_div_iff (hBne i) (pow_ne_zero k (hne j))] at h1
  rw [← h1, mul_comm]

variable {X Y : GL (Fin n) F} {z : Fˣ}

theorem mul_eq_smul_mul_of_conj_eq_scalar
    (hXY : Y * X * Y⁻¹ = GeneralLinearGroup.scalar (Fin n) z * X) :
    ((X : Matrix (Fin n) (Fin n) F) * (Y : Matrix (Fin n) (Fin n) F)) =
      ((z : F))⁻¹ • ((Y : Matrix (Fin n) (Fin n) F) * (X : Matrix (Fin n) (Fin n) F)) := by
  have hYX : Y * X = GeneralLinearGroup.scalar (Fin n) z * X * Y := by
    rw [← hXY]; group
  have hscalar : (Matrix.scalar (Fin n) (z : F)) * (X : Matrix (Fin n) (Fin n) F) =
      (z : F) • (X : Matrix (Fin n) (Fin n) F) := by
    rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
  have hmat : (Y : Matrix (Fin n) (Fin n) F) * (X : Matrix (Fin n) (Fin n) F) =
      (z : F) • ((X : Matrix (Fin n) (Fin n) F) * (Y : Matrix (Fin n) (Fin n) F)) := by
    have h := congrArg (fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F)) hYX
    simp only [Units.val_mul] at h
    rw [h, GeneralLinearGroup.coe_scalar, hscalar, Matrix.smul_mul]
  rw [hmat, smul_smul, inv_mul_cancel₀ z.ne_zero, one_smul]

theorem conj_inv_eq_scalar_inv (hXY : Y * X * Y⁻¹ = GeneralLinearGroup.scalar (Fin n) z * X) :
    Y⁻¹ * X * (Y⁻¹)⁻¹ = GeneralLinearGroup.scalar (Fin n) z⁻¹ * X := by
  have hY : Y⁻¹ * (GeneralLinearGroup.scalar (Fin n) z * X) * Y = X := by
    rw [← hXY]; group
  have hM : GeneralLinearGroup.scalar (Fin n) z⁻¹ *
      (GeneralLinearGroup.scalar (Fin n) z * X) = X := by
    rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  rw [inv_inv]
  calc Y⁻¹ * X * Y
      = Y⁻¹ * (GeneralLinearGroup.scalar (Fin n) z⁻¹ *
          (GeneralLinearGroup.scalar (Fin n) z * X)) * Y := by rw [hM]
    _ = (Y⁻¹ * GeneralLinearGroup.scalar (Fin n) z⁻¹) *
          (GeneralLinearGroup.scalar (Fin n) z * X) * Y := by group
    _ = (GeneralLinearGroup.scalar (Fin n) z⁻¹ * Y⁻¹) *
          (GeneralLinearGroup.scalar (Fin n) z * X) * Y := by
          rw [← GeneralLinearGroup.scalar_commute z⁻¹ Y⁻¹]
    _ = GeneralLinearGroup.scalar (Fin n) z⁻¹ *
          (Y⁻¹ * (GeneralLinearGroup.scalar (Fin n) z * X) * Y) := by group
    _ = GeneralLinearGroup.scalar (Fin n) z⁻¹ * X := by rw [hY]

theorem mul_inv_eq_smul_inv_mul
    (hXY : Y * X * Y⁻¹ = GeneralLinearGroup.scalar (Fin n) z * X) :
    ((X : Matrix (Fin n) (Fin n) F) * ((Y⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) =
      (z : F) • (((Y⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
        (X : Matrix (Fin n) (Fin n) F)) := by
  have h := mul_eq_smul_mul_of_conj_eq_scalar (X := X) (Y := Y⁻¹) (z := z⁻¹)
    (conj_inv_eq_scalar_inv hXY)
  rwa [Units.val_inv_eq_inv_val, inv_inv] at h

theorem map_eigenspace_le (hXY : Y * X * Y⁻¹ = GeneralLinearGroup.scalar (Fin n) z * X) (ζ : F) :
    (Module.End.eigenspace (Matrix.toLin' (X : Matrix (Fin n) (Fin n) F)) ζ).map
        (Matrix.toLin' (Y : Matrix (Fin n) (Fin n) F)) ≤
      Module.End.eigenspace (Matrix.toLin' (X : Matrix (Fin n) (Fin n) F)) (((z : F))⁻¹ * ζ) := by
  rintro _ ⟨v, hv, rfl⟩
  have hv' : (Matrix.toLin' (X : Matrix (Fin n) (Fin n) F)) v = ζ • v :=
    Module.End.mem_eigenspace_iff.mp hv
  refine Module.End.mem_eigenspace_iff.mpr ?_
  simp only [Matrix.toLin'_apply] at *
  rw [Matrix.mulVec_mulVec, mul_eq_smul_mul_of_conj_eq_scalar hXY, Matrix.smul_mulVec,
    ← Matrix.mulVec_mulVec, hv', Matrix.mulVec_smul, smul_smul, mul_comm ((z : F))⁻¹ ζ]

theorem map_eigenspace_eq (hXY : Y * X * Y⁻¹ = GeneralLinearGroup.scalar (Fin n) z * X) (ζ : F) :
    (Module.End.eigenspace (Matrix.toLin' (X : Matrix (Fin n) (Fin n) F)) ζ).map
        (Matrix.toLin' (Y : Matrix (Fin n) (Fin n) F)) =
      Module.End.eigenspace (Matrix.toLin' (X : Matrix (Fin n) (Fin n) F)) (((z : F))⁻¹ * ζ) := by
  refine le_antisymm (map_eigenspace_le hXY ζ) ?_
  rintro w hw
  have hw' : (Matrix.toLin' (X : Matrix (Fin n) (Fin n) F)) w = (((z : F))⁻¹ * ζ) • w :=
    Module.End.mem_eigenspace_iff.mp hw
  rw [Matrix.toLin'_apply] at hw'
  refine ⟨Matrix.toLin' ((Y⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) w, ?_, ?_⟩
  · refine Module.End.mem_eigenspace_iff.mpr ?_
    simp only [Matrix.toLin'_apply]
    rw [Matrix.mulVec_mulVec,
      mul_inv_eq_smul_inv_mul hXY, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hw',
      Matrix.mulVec_smul, smul_smul, ← mul_assoc, mul_inv_cancel₀ z.ne_zero, one_mul]
  · show Matrix.toLin' (Y : Matrix (Fin n) (Fin n) F)
        (Matrix.toLin' ((Y⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) w) = w
    simp only [Matrix.toLin'_apply]
    rw [Matrix.mulVec_mulVec, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem finrank_eigenspace_eq_of_conj
    (hXY : Y * X * Y⁻¹ = GeneralLinearGroup.scalar (Fin n) z * X) (ζ : F) :
    Module.finrank F (Module.End.eigenspace (Matrix.toLin' (X : Matrix (Fin n) (Fin n) F))
        (((z : F))⁻¹ * ζ)) =
      Module.finrank F
        (Module.End.eigenspace (Matrix.toLin' (X : Matrix (Fin n) (Fin n) F)) ζ) := by
  refine le_antisymm ?_ ?_
  · rw [← map_eigenspace_eq hXY ζ]
    exact Submodule.finrank_map_le _ _
  · have h := map_eigenspace_eq (conj_inv_eq_scalar_inv hXY) (((z : F))⁻¹ * ζ)
    rw [show ((z⁻¹ : Fˣ) : F)⁻¹ * (((z : F))⁻¹ * ζ) = ζ from by
      rw [Units.val_inv_eq_inv_val, inv_inv, ← mul_assoc, mul_inv_cancel₀ z.ne_zero, one_mul]] at h
    rw [← h]
    exact Submodule.finrank_map_le _ _

theorem pow_conj_eq_scalar (hXY : Y * X * Y⁻¹ = GeneralLinearGroup.scalar (Fin n) z * X)
    (k : ℕ) :
    Y ^ k * X * (Y ^ k)⁻¹ = GeneralLinearGroup.scalar (Fin n) (z ^ k) * X := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc Y ^ (k + 1) * X * (Y ^ (k + 1))⁻¹
          = Y * (Y ^ k * X * (Y ^ k)⁻¹) * Y⁻¹ := by rw [pow_succ']; group
        _ = Y * (GeneralLinearGroup.scalar (Fin n) (z ^ k) * X) * Y⁻¹ := by rw [ih]
        _ = GeneralLinearGroup.scalar (Fin n) (z ^ k) * (Y * X * Y⁻¹) := by
              rw [← mul_assoc, ← mul_assoc, ← GeneralLinearGroup.scalar_commute (z ^ k) Y]; group
        _ = GeneralLinearGroup.scalar (Fin n) (z ^ k) *
              (GeneralLinearGroup.scalar (Fin n) z * X) := by rw [hXY]
        _ = GeneralLinearGroup.scalar (Fin n) (z ^ (k + 1)) * X := by
              rw [← mul_assoc, ← map_mul, pow_succ]

theorem generalLinearGroup_scalar_injective {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] [Semiring R] :
    Function.Injective (GeneralLinearGroup.scalar ι : Rˣ →* GL ι R) :=
  fun _ _ h => Units.ext (Matrix.scalar_inj.1 (congrArg Units.val h))

theorem zpow_conj_eq_scalar (hXY : Y * X * Y⁻¹ = GeneralLinearGroup.scalar (Fin n) z * X)
    (k : ℤ) :
    Y ^ k * X * (Y ^ k)⁻¹ = GeneralLinearGroup.scalar (Fin n) (z ^ k) * X := by
  cases k with
  | ofNat n => simpa using pow_conj_eq_scalar hXY n
  | negSucc n =>
      have h1 := conj_inv_eq_scalar_inv (pow_conj_eq_scalar hXY (n + 1))
      simpa [zpow_negSucc, inv_inv] using h1

theorem scalar_pow_eq_one_of_conj_eq_scalar {X Y : GL (Fin n) F} {z b : Fˣ} {k : ℕ}
    (hXY : Y * X * Y⁻¹ = GeneralLinearGroup.scalar (Fin n) z * X)
    (hX : X ^ k = GeneralLinearGroup.scalar (Fin n) b) (hn : 0 < n) : z ^ k = 1 := by
  have h1 : GeneralLinearGroup.scalar (Fin n) b =
      GeneralLinearGroup.scalar (Fin n) (z ^ k) * GeneralLinearGroup.scalar (Fin n) b := by
    calc GeneralLinearGroup.scalar (Fin n) b = Y * X ^ k * Y⁻¹ := by
          rw [hX, ← GeneralLinearGroup.scalar_commute b Y]; group
      _ = (Y * X * Y⁻¹) ^ k := (conj_pow).symm
      _ = (GeneralLinearGroup.scalar (Fin n) z * X) ^ k := by rw [hXY]
      _ = GeneralLinearGroup.scalar (Fin n) (z ^ k) * X ^ k := by
          rw [((commute_iff_eq _ _).mpr (GeneralLinearGroup.scalar_commute z X)).mul_pow,
            map_pow]
      _ = GeneralLinearGroup.scalar (Fin n) (z ^ k) *
            GeneralLinearGroup.scalar (Fin n) b := by rw [hX]
  rw [← map_mul] at h1
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have h2 : b = z ^ k * b := generalLinearGroup_scalar_injective h1
  exact mul_right_cancel (by rw [← h2, one_mul])

theorem mul_zpow_pow_eq_scalar {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hXY : Y * X * Y⁻¹ = GeneralLinearGroup.scalar (Fin n) z * X) (hz : z ^ p = 1)
    {a b : Fˣ} (hX : X ^ p = GeneralLinearGroup.scalar (Fin n) b)
    (hY : Y ^ p = GeneralLinearGroup.scalar (Fin n) a) (m : ℤ) :
    (X * Y ^ m) ^ p = GeneralLinearGroup.scalar (Fin n) (b * a ^ m) := by
  have hcomm : ⁅Y ^ m, X⁆ = GeneralLinearGroup.scalar (Fin n) (z ^ m) := by
    rw [commutatorElement_def]
    rw [zpow_conj_eq_scalar hXY m]
    rw [mul_assoc]
    rw [mul_inv_cancel, mul_one]
  have hca : Commute X ⁅Y ^ m, X⁆ := by
    rw [hcomm]
    exact (GeneralLinearGroup.scalar_commute (z ^ m) X).symm
  have hcb : Commute (Y ^ m) ⁅Y ^ m, X⁆ := by
    rw [hcomm]
    exact (GeneralLinearGroup.scalar_commute (z ^ m) (Y ^ m)).symm
  have hYpow : (Y ^ m) ^ p = GeneralLinearGroup.scalar (Fin n) (a ^ m) := by
    rw [← _root_.zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul,
      _root_.zpow_natCast, hY, ← map_zpow]
  have hdz : (z ^ m) ^ (p.choose 2) = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one]
    exact (orderOf_dvd_of_mem_zpowers (Subgroup.zpow_mem_zpowers z m)).trans
      ((orderOf_dvd_of_pow_eq_one hz).trans
        (Nat.Prime.dvd_choose_self hp (k := 2) (by norm_num) (by
          have := hp.two_le; omega)))
  have hpow := Commute.mul_pow_eq_pow_mul_pow_mul_commutatorElement_pow_choose_two
    (a := X) (b := Y ^ m) hca hcb p
  rw [hpow, hX, hYpow, hcomm, ← map_mul, ← map_pow, hdz, map_one, mul_one]

theorem scalar_inv_mul_mul_zpow_neg_pow_eq_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hXY : Y * X * Y⁻¹ = GeneralLinearGroup.scalar (Fin n) z * X) (hz : z ^ p = 1)
    {a b d : Fˣ} (hX : X ^ p = GeneralLinearGroup.scalar (Fin n) b)
    (hY : Y ^ p = GeneralLinearGroup.scalar (Fin n) a) {m : ℤ} (hb : b = a ^ m * d ^ p) :
    (GeneralLinearGroup.scalar (Fin n) d⁻¹ * X * Y ^ (-m)) ^ p = 1 := by
  have h1 : (GeneralLinearGroup.scalar (Fin n) d⁻¹ * X * Y ^ (-m)) ^ p =
      GeneralLinearGroup.scalar (Fin n) ((d⁻¹) ^ p) * (X * Y ^ (-m)) ^ p := by
    rw [mul_assoc, ((commute_iff_eq _ _).mpr
      (GeneralLinearGroup.scalar_commute d⁻¹ (X * Y ^ (-m)))).mul_pow, map_pow]
  rw [h1]
  rw [mul_zpow_pow_eq_scalar hp hp2 hXY hz hX hY (-m)]
  have h2 : (d⁻¹) ^ p * (b * a ^ (-m)) = 1 := by
    rw [hb, inv_pow]
    rw [show a ^ (-m) = (a ^ m)⁻¹ from _root_.zpow_neg a m]
    calc (d ^ p)⁻¹ * (a ^ m * d ^ p * (a ^ m)⁻¹)
        = (d ^ p)⁻¹ * ((d ^ p * a ^ m) * (a ^ m)⁻¹) := by
            rw [mul_comm (a ^ m) (d ^ p)]
      _ = (d ^ p)⁻¹ * (d ^ p * (a ^ m * (a ^ m)⁻¹)) := by rw [mul_assoc]
      _ = (d ^ p)⁻¹ * (d ^ p * 1) := by rw [mul_inv_cancel]
      _ = (d ^ p)⁻¹ * d ^ p := by rw [mul_one]
      _ = 1 := by rw [inv_mul_cancel]
  rw [← map_mul, h2, map_one]

theorem finrank_eigenspace_eq_of_pow (hXY : Y * X * Y⁻¹ = GeneralLinearGroup.scalar (Fin n) z * X)
    (k : ℕ) (ζ : F) :
    Module.finrank F (Module.End.eigenspace (Matrix.toLin' (X : Matrix (Fin n) (Fin n) F))
        ((((z ^ k : Fˣ)) : F)⁻¹ * ζ)) =
      Module.finrank F (Module.End.eigenspace (Matrix.toLin' (X : Matrix (Fin n) (Fin n) F)) ζ) :=
  finrank_eigenspace_eq_of_conj (pow_conj_eq_scalar hXY k) ζ

theorem card_eq_mul_finrank_eigenspace_one {p : ℕ} (hp : p.Prime)
    (hz : IsPrimitiveRoot (z : F) p) (hX : X ^ p = 1)
    (hXY : Y * X * Y⁻¹ = GeneralLinearGroup.scalar (Fin n) z * X) :
    n = p * Module.finrank F
      (Module.End.eigenspace (Matrix.toLin' (X : Matrix (Fin n) (Fin n) F)) 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set g : (Fin n → F) ≃ₗ[F] (Fin n → F) :=
    LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin n → F)
      (Matrix.GeneralLinearGroup.toLin X) with hg
  have hgL : g.toLinearMap = Matrix.toLin' (X : Matrix (Fin n) (Fin n) F) := by
    rw [hg, LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap,
      Matrix.GeneralLinearGroup.coe_toLin, ← Matrix.toLin'_apply']
  have hgp : g ^ p = 1 := by
    rw [hg, ← map_pow, ← map_pow, hX]
    simp
  have hdir : DirectSum.IsInternal (fun i : Fin p =>
      Module.End.eigenspace (Matrix.toLin' (X : Matrix (Fin n) (Fin n) F))
        ((z : F) ^ (i : ℤ))) := by
    have h := CFSG.proposition_2_4_a (g := g) hgp hp.two_le (ε := (z : F)) hz
    simpa only [hgL] using h
  have hfin : Module.finrank F (Fin n → F) =
      ∑ i : Fin p,
        Module.finrank F (Module.End.eigenspace (Matrix.toLin' (X : Matrix (Fin n) (Fin n) F))
          ((z : F) ^ (i : ℤ))) := by
    rw [← LinearEquiv.finrank_eq (LinearEquiv.ofBijective (DirectSum.coeLinearMap _) hdir),
      Module.finrank_directSum]
  have hD : ∀ i : Fin p,
      Module.finrank F (Module.End.eigenspace (Matrix.toLin' (X : Matrix (Fin n) (Fin n) F))
        ((z : F) ^ (i : ℤ))) =
      Module.finrank F
        (Module.End.eigenspace (Matrix.toLin' (X : Matrix (Fin n) (Fin n) F)) 1) := by
    intro i
    have h1 : ((z : F) ^ (i : ℤ)) = (((z ^ i.val : Fˣ)) : F) := by
      rw [Units.val_pow_eq_pow_val, zpow_natCast]
    have h2 := finrank_eigenspace_eq_of_pow (X := X) (Y := Y) hXY i.val (((z ^ i.val : Fˣ)) : F)
    rw [h1, ← h2, inv_mul_cancel₀ (z ^ i.val : Fˣ).ne_zero]
  have hsum : Module.finrank F (Fin n → F) =
      p * Module.finrank F
        (Module.End.eigenspace (Matrix.toLin' (X : Matrix (Fin n) (Fin n) F)) 1) := by
    rw [hfin, Finset.sum_congr rfl (fun i _ => hD i), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
  rw [Module.finrank_fin_fun] at hsum
  exact hsum

theorem dvd_of_conj_eq_scalar {p : ℕ} (hp : p.Prime) (hz : IsPrimitiveRoot (z : F) p)
    (hX : X ^ p = 1)
    (hXY : Y * X * Y⁻¹ = GeneralLinearGroup.scalar (Fin n) z * X) : p ∣ n :=
  ⟨_, card_eq_mul_finrank_eigenspace_one hp hz hX hXY⟩

theorem conj_eq_scalar_inv (hXY : Y * X * Y⁻¹ = GeneralLinearGroup.scalar (Fin n) z * X) :
    X * Y * X⁻¹ = GeneralLinearGroup.scalar (Fin n) z⁻¹ * Y := by
  have hYX : Y * X = GeneralLinearGroup.scalar (Fin n) z * X * Y := by rw [← hXY]; group
  have hXY' : X * Y = GeneralLinearGroup.scalar (Fin n) z⁻¹ * (Y * X) := by
    rw [hYX, ← mul_assoc, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  rw [hXY', mul_assoc, mul_assoc, mul_inv_cancel, mul_one]

theorem exists_basis_eq_pow_mulVec {p : ℕ} (hp : p.Prime) (hz : IsPrimitiveRoot (z : F) p)
    (hX : X ^ p = 1) (hXY : Y * X * Y⁻¹ = GeneralLinearGroup.scalar (Fin n) z * X) (hn : n = p)
    {v : Fin n → F}
    (hv : v ∈ Module.End.eigenspace (Matrix.toLin' (X : Matrix (Fin n) (Fin n) F)) 1)
    (hv0 : v ≠ 0) :
    ∃ b : Basis (Fin p) F (Fin n → F), ∀ i : Fin p,
      b i = (Matrix.toLin' ((Y ^ i.val : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) v := by
  haveI : Nonempty (Fin p) := ⟨⟨0, hp.pos⟩⟩
  set w : Fin p → (Fin n → F) := fun i =>
    (Matrix.toLin' ((Y ^ i.val : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) v with hw
  have hwmem : ∀ i : Fin p,
      w i ∈ Module.End.eigenspace (Matrix.toLin' (X : Matrix (Fin n) (Fin n) F))
        ((((z ^ i.val : Fˣ)) : F)⁻¹ * 1) := by
    intro i
    have h := map_eigenspace_le (X := X) (Y := Y ^ i.val) (z := z ^ i.val)
      (pow_conj_eq_scalar hXY i.val) 1
    exact h ⟨v, hv, rfl⟩
  have hwne : ∀ i : Fin p, w i ≠ 0 := by
    intro i h0
    have h0' : ((Y ^ i.val : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ v = 0 := by
      have h1 := h0
      simp only [hw, Matrix.toLin'_apply] at h1
      exact h1
    have hinj : Function.Injective
        (fun w' => ((Y ^ i.val : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ w') :=
      (Matrix.mulVec_injective_iff_isUnit
        (A := ((Y ^ i.val : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))).mpr
        (Units.isUnit (Y ^ i.val))
    exact hv0 (hinj (by simp only [h0', Matrix.mulVec_zero]))
  set μ : Fin p → F := fun i => (((z ^ i.val : Fˣ)) : F)⁻¹ * 1 with hμ
  have hμinj : Function.Injective μ := by
    intro i j hij
    simp only [hμ, mul_one] at hij
    have h2 : (((z : F) ^ i.val))⁻¹ = (((z : F) ^ j.val))⁻¹ := by
      simpa only [Units.val_pow_eq_pow_val] using hij
    exact Fin.ext (hz.pow_inj i.isLt j.isLt (inv_inj.1 h2))
  have hli : LinearIndependent F w :=
    Module.End.eigenvectors_linearIndependent'
      (Matrix.toLin' (X : Matrix (Fin n) (Fin n) F)) μ hμinj w
      (fun i => Module.End.hasEigenvector_iff.mpr ⟨hwmem i, hwne i⟩)
  have hcard : Fintype.card (Fin p) = Module.finrank F (Fin n → F) := by
    rw [Fintype.card_fin, ← hn, Module.finrank_fin_fun]
  exact ⟨basisOfLinearIndependentOfCardEqFinrank hli hcard,
    fun i => congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hli hcard) i⟩

theorem exists_eq_scalar_of_commute_of_conj_eq_scalar {p : ℕ} (hp : p.Prime)
    (hz : IsPrimitiveRoot (z : F) p) (hX : X ^ p = 1)
    (hXY : Y * X * Y⁻¹ = GeneralLinearGroup.scalar (Fin n) z * X) (hn : n = p)
    {G : GL (Fin n) F} (hGX : Commute G X) (hGY : Commute G Y) :
    ∃ c : Fˣ, G = GeneralLinearGroup.scalar (Fin n) c := by
  have hD := card_eq_mul_finrank_eigenspace_one (X := X) (Y := Y) hp hz hX hXY
  have hD1 : Module.finrank F
      (Module.End.eigenspace (Matrix.toLin' (X : Matrix (Fin n) (Fin n) F)) 1) = 1 := by
    have h1 : p * Module.finrank F
        (Module.End.eigenspace (Matrix.toLin' (X : Matrix (Fin n) (Fin n) F)) 1) = p * 1 := by
      rw [mul_one, ← hD, hn]
    exact Nat.eq_of_mul_eq_mul_left hp.pos h1
  have hU0 : Module.End.eigenspace (Matrix.toLin' (X : Matrix (Fin n) (Fin n) F)) 1 ≠ ⊥ := by
    intro hbot
    rw [hbot] at hD1
    simpa using hD1
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
  have hmatGX : (G : Matrix (Fin n) (Fin n) F) * (X : Matrix (Fin n) (Fin n) F) =
      (X : Matrix (Fin n) (Fin n) F) * (G : Matrix (Fin n) (Fin n) F) := by
    rw [← Units.val_mul, ← Units.val_mul, hGX.eq]
  have hGv : (G : Matrix (Fin n) (Fin n) F) *ᵥ v ∈
      Module.End.eigenspace (Matrix.toLin' (X : Matrix (Fin n) (Fin n) F)) 1 := by
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hv
    rw [Matrix.mulVec_mulVec, ← hmatGX, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul,
      one_smul]
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero'
    (K := F) (V := ↥(Module.End.eigenspace (Matrix.toLin' (X : Matrix (Fin n) (Fin n) F)) 1))
    ⟨v, hv⟩ (by simpa using hv0)).1 hD1 ⟨(G : Matrix (Fin n) (Fin n) F) *ᵥ v, hGv⟩
  have hcv : c • v = (G : Matrix (Fin n) (Fin n) F) *ᵥ v := by
    simpa using congrArg Subtype.val hc
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hcv
    exact hv0 ((Matrix.mulVec_injective_iff_isUnit
      (A := (G : Matrix (Fin n) (Fin n) F))).mpr (Units.isUnit G)
      (by rw [hcv.symm, Matrix.mulVec_zero]))
  obtain ⟨b, hb⟩ := exists_basis_eq_pow_mulVec hp hz hX hXY hn hv hv0
  have hGb : ∀ i : Fin p, (G : Matrix (Fin n) (Fin n) F) *ᵥ (b i) = c • (b i) := by
    intro i
    rw [hb i, Matrix.toLin'_apply]
    have hcomm : (G : Matrix (Fin n) (Fin n) F) *
        ((Y ^ i.val : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        ((Y ^ i.val : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
          (G : Matrix (Fin n) (Fin n) F) := by
      rw [← Units.val_mul, ← Units.val_mul, (hGY.pow_right i.val).eq]
    rw [Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec, ← hcv, Matrix.mulVec_smul]
  have hEq : Matrix.toLin' (G : Matrix (Fin n) (Fin n) F) = c • (1 : Module.End F (Fin n → F)) := by
    refine b.ext fun i => ?_
    rw [Matrix.toLin'_apply, LinearMap.smul_apply, Module.End.one_apply]
    exact hGb i
  have hsc : ((GeneralLinearGroup.scalar (Fin n) (Units.mk0 c hc0) : GL (Fin n) F) :
      Matrix (Fin n) (Fin n) F) = c • (1 : Matrix (Fin n) (Fin n) F) := by
    rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Units.val_mk0,
      ← Matrix.mul_one (Matrix.diagonal (fun _ : Fin n => (c : F))),
      ← Matrix.smul_eq_diagonal_mul]
  have hGmat : (G : Matrix (Fin n) (Fin n) F) =
      ((GeneralLinearGroup.scalar (Fin n) (Units.mk0 c hc0) : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) F) := by
    apply Matrix.toLin'.injective
    rw [hEq, hsc]
    refine LinearMap.ext fun w => ?_
    rw [LinearMap.smul_apply, Module.End.one_apply, Matrix.toLin'_apply, Matrix.smul_mulVec,
      Matrix.one_mulVec]
  exact ⟨Units.mk0 c hc0, Units.ext hGmat⟩

theorem conj_scalar_mul_conj (u : Fˣ) (M N : GL (Fin n) F) :
    N * (GeneralLinearGroup.scalar (Fin n) u * M) * N⁻¹ =
      GeneralLinearGroup.scalar (Fin n) u * (N * M * N⁻¹) := by
  rw [show N * (GeneralLinearGroup.scalar (Fin n) u * M) * N⁻¹ =
    (N * GeneralLinearGroup.scalar (Fin n) u) * M * N⁻¹ from by group]
  rw [← GeneralLinearGroup.scalar_commute u N]
  group

theorem exists_eq_scalar_mul_pow_mul_pow {p : ℕ} (hp : p.Prime)
    (hz : IsPrimitiveRoot (z : F) p) (hX : X ^ p = 1)
    (hXY : Y * X * Y⁻¹ = GeneralLinearGroup.scalar (Fin n) z * X) (hn : n = p)
    {G : GL (Fin n) F} {α α' : Fˣ}
    (hGX : G * X * G⁻¹ = GeneralLinearGroup.scalar (Fin n) α * X)
    (hGY : G * Y * G⁻¹ = GeneralLinearGroup.scalar (Fin n) α' * Y) :
    ∃ (c : Fˣ) (i j : ℕ), G = GeneralLinearGroup.scalar (Fin n) c * X ^ i * Y ^ j := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hn0 : 0 < n := by rw [hn]; exact hp.pos
  haveI : Nonempty (Fin n) := ⟨⟨0, hn0⟩⟩
  have hsc1 : ∀ u : Fˣ, GeneralLinearGroup.scalar (Fin n) u = 1 → u = 1 :=
    fun _ hu => generalLinearGroup_scalar_injective (hu.trans (map_one _).symm)
  have hαp : α ^ p = 1 := by
    have h1 : (G * X * G⁻¹) ^ p = 1 := by rw [conj_pow, hX, mul_one, mul_inv_cancel]
    rw [hGX, (show Commute (GeneralLinearGroup.scalar (Fin n) α) X from
      GeneralLinearGroup.scalar_commute α X).mul_pow, ← map_pow, hX, mul_one] at h1
    exact hsc1 (α ^ p) h1
  have hzp : z ^ p = 1 := by
    ext
    rw [Units.val_pow_eq_pow_val, hz.pow_eq_one, Units.val_one]
  have hYX : Y ^ p * X = X * Y ^ p := by
    have h := pow_conj_eq_scalar hXY p
    rw [hzp, map_one, one_mul] at h
    calc Y ^ p * X = (Y ^ p * X * (Y ^ p)⁻¹) * Y ^ p := by group
      _ = X * Y ^ p := by rw [h]
  obtain ⟨β, hβ⟩ := exists_eq_scalar_of_commute_of_conj_eq_scalar hp hz hX hXY hn
    (show Commute (Y ^ p) X from hYX)
    (show Commute (Y ^ p) Y from (Commute.refl Y).pow_left p)
  have hα'p : α' ^ p = 1 := by
    have h1 : (G * Y * G⁻¹) ^ p = GeneralLinearGroup.scalar (Fin n) β := by
      rw [conj_pow, hβ, ← GeneralLinearGroup.scalar_commute β G, mul_assoc, mul_inv_cancel,
        mul_one]
    rw [hGY, (show Commute (GeneralLinearGroup.scalar (Fin n) α') Y from
      GeneralLinearGroup.scalar_commute α' Y).mul_pow, ← map_pow, hβ] at h1
    have h2 : GeneralLinearGroup.scalar (Fin n) (α' ^ p) = 1 := by
      have h3 : GeneralLinearGroup.scalar (Fin n) (α' ^ p) *
          GeneralLinearGroup.scalar (Fin n) β = 1 * GeneralLinearGroup.scalar (Fin n) β := by
        rw [one_mul]; exact h1
      exact mul_right_cancel h3
    exact hsc1 (α' ^ p) h2
  have hαp' : ((α : F)) ^ p = 1 := by rw [← Units.val_pow_eq_pow_val, hαp, Units.val_one]
  have hα'p' : ((α' : F)) ^ p = 1 := by rw [← Units.val_pow_eq_pow_val, hα'p, Units.val_one]
  obtain ⟨a, -, ha⟩ := hz.eq_pow_of_pow_eq_one hαp'
  obtain ⟨b, hb_lt, hb⟩ := hz.eq_pow_of_pow_eq_one hα'p'
  have hαeq : α = z ^ a := (Units.ext (by rw [Units.val_pow_eq_pow_val, ha])).symm
  have hα'eq : α' = z ^ b := (Units.ext (by rw [Units.val_pow_eq_pow_val, hb])).symm
  set i : ℕ := p - b with hi
  set j : ℕ := a with hj
  have hconjX : (X ^ i * Y ^ j)⁻¹ * X * (X ^ i * Y ^ j) =
      GeneralLinearGroup.scalar (Fin n) ((z ^ j)⁻¹) * X := by
    have h := conj_inv_eq_scalar_inv (pow_conj_eq_scalar hXY j)
    rw [inv_inv] at h
    calc (X ^ i * Y ^ j)⁻¹ * X * (X ^ i * Y ^ j)
        = (Y ^ j)⁻¹ * ((X ^ i)⁻¹ * X * X ^ i) * Y ^ j := by group
      _ = (Y ^ j)⁻¹ * X * Y ^ j := by group
      _ = GeneralLinearGroup.scalar (Fin n) ((z ^ j)⁻¹) * X := h
  have hconjY : (X ^ i * Y ^ j)⁻¹ * Y * (X ^ i * Y ^ j) =
      GeneralLinearGroup.scalar (Fin n) (z ^ i) * Y := by
    have h := conj_inv_eq_scalar_inv (pow_conj_eq_scalar (conj_eq_scalar_inv hXY) i)
    rw [inv_inv] at h
    have hz' : (((z⁻¹) ^ i : Fˣ))⁻¹ = z ^ i := by rw [inv_pow, inv_inv]
    rw [hz'] at h
    calc (X ^ i * Y ^ j)⁻¹ * Y * (X ^ i * Y ^ j)
        = (Y ^ j)⁻¹ * ((X ^ i)⁻¹ * Y * X ^ i) * Y ^ j := by group
      _ = (Y ^ j)⁻¹ * (GeneralLinearGroup.scalar (Fin n) (z ^ i) * Y) * Y ^ j := by rw [h]
      _ = GeneralLinearGroup.scalar (Fin n) (z ^ i) * Y := by
            have h2 := conj_scalar_mul_conj (z ^ i) Y ((Y ^ j)⁻¹)
            rw [inv_inv] at h2
            rw [h2]
            group
  set G₂ : GL (Fin n) F := (X ^ i * Y ^ j)⁻¹ * G with hG₂
  have hG₂X : G₂ * X * G₂⁻¹ = X := by
    rw [hG₂]
    calc ((X ^ i * Y ^ j)⁻¹ * G) * X * ((X ^ i * Y ^ j)⁻¹ * G)⁻¹
        = (X ^ i * Y ^ j)⁻¹ * (G * X * G⁻¹) * (X ^ i * Y ^ j) := by group
      _ = (X ^ i * Y ^ j)⁻¹ * (GeneralLinearGroup.scalar (Fin n) α * X) *
            (X ^ i * Y ^ j) := by rw [hGX]
      _ = GeneralLinearGroup.scalar (Fin n) α * ((X ^ i * Y ^ j)⁻¹ * X * (X ^ i * Y ^ j)) := by
            have h2 := conj_scalar_mul_conj α X ((X ^ i * Y ^ j)⁻¹)
            rw [inv_inv] at h2
            rw [h2]
      _ = GeneralLinearGroup.scalar (Fin n) α *
            (GeneralLinearGroup.scalar (Fin n) ((z ^ j)⁻¹) * X) := by rw [hconjX]
      _ = X := by
            rw [hαeq, hj, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  have hG₂Y : G₂ * Y * G₂⁻¹ = Y := by
    rw [hG₂]
    calc ((X ^ i * Y ^ j)⁻¹ * G) * Y * ((X ^ i * Y ^ j)⁻¹ * G)⁻¹
        = (X ^ i * Y ^ j)⁻¹ * (G * Y * G⁻¹) * (X ^ i * Y ^ j) := by group
      _ = (X ^ i * Y ^ j)⁻¹ * (GeneralLinearGroup.scalar (Fin n) α' * Y) *
            (X ^ i * Y ^ j) := by rw [hGY]
      _ = GeneralLinearGroup.scalar (Fin n) α' * ((X ^ i * Y ^ j)⁻¹ * Y * (X ^ i * Y ^ j)) := by
            have h2 := conj_scalar_mul_conj α' Y ((X ^ i * Y ^ j)⁻¹)
            rw [inv_inv] at h2
            rw [h2]
      _ = GeneralLinearGroup.scalar (Fin n) α' *
            (GeneralLinearGroup.scalar (Fin n) (z ^ i) * Y) := by rw [hconjY]
      _ = Y := by
            rw [hα'eq, hi, ← mul_assoc, ← map_mul, ← pow_add,
              show b + (p - b) = p from by omega, hzp, map_one, one_mul]
  have hcG₂X : G₂ * X = X * G₂ := by
    have h := congrArg (fun g : GL (Fin n) F => g * G₂) hG₂X
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using h
  have hcG₂Y : G₂ * Y = Y * G₂ := by
    have h := congrArg (fun g : GL (Fin n) F => g * G₂) hG₂Y
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using h
  obtain ⟨c, hc⟩ := exists_eq_scalar_of_commute_of_conj_eq_scalar hp hz hX hXY hn
    (show Commute G₂ X from hcG₂X) (show Commute G₂ Y from hcG₂Y)
  refine ⟨c, i, j, ?_⟩
  have hG : G = X ^ i * Y ^ j * G₂ := by rw [hG₂]; group
  calc G = X ^ i * Y ^ j * G₂ := hG
    _ = X ^ i * Y ^ j * GeneralLinearGroup.scalar (Fin n) c := by rw [hc]
    _ = GeneralLinearGroup.scalar (Fin n) c * (X ^ i * Y ^ j) :=
          (GeneralLinearGroup.scalar_commute c (X ^ i * Y ^ j)).symm
    _ = GeneralLinearGroup.scalar (Fin n) c * X ^ i * Y ^ j := by group

end CFSG.LinearAlgebra
