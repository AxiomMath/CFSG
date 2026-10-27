module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Unitary45Mono
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryBalNonsplit

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Polynomial Module Matrix CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.HardMathSupport.Timmesfeld.Balance

variable {ℓ f n p : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

section Scalar

theorem unit_pow_three_eq_one (h : UnitaryFieldData ℓ f K) (hq : ℓ ^ f = 2) (c : Kˣ) :
    c ^ 3 = 1 := by
  have h1 := pow_three_eq_one h hq c.ne_zero
  exact Units.ext (by simpa using h1)

theorem norm_eq_one_of_unit (h : UnitaryFieldData ℓ f K) (hq : ℓ ^ f = 2) (c : Kˣ) :
    h.norm (c : K) = 1 := by
  rw [norm_eq_cube h hq]
  exact pow_three_eq_one h hq c.ne_zero

end Scalar

section Coprime

theorem pow_mul_comm_central {G : Type*} [Group G] {a b s : G} (hs : ∀ g : G, s * g = g * s)
    (hab : a * b = b * a * s) (k : ℕ) : a ^ k * b = b * a ^ k * s ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc a ^ (k + 1) * b = a * (a ^ k * b) := by rw [pow_succ', mul_assoc]
      _ = a * (b * a ^ k * s ^ k) := by rw [ih]
      _ = (a * b) * a ^ k * s ^ k := by simp only [mul_assoc]
      _ = b * a * s * a ^ k * s ^ k := by rw [hab]
      _ = b * a * (s * a ^ k) * s ^ k := by simp only [mul_assoc]
      _ = b * a * (a ^ k * s) * s ^ k := by rw [hs]
      _ = b * (a * a ^ k) * (s * s ^ k) := by simp only [mul_assoc]
      _ = b * a ^ (k + 1) * s ^ (k + 1) := by rw [← pow_succ' a k, ← pow_succ' s k]

theorem commute_of_commute_psi_coprime (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2))
    (hq : ℓ ^ f = 2) {M x : primeFormUnitary h (idGram K n)}
    (hcop : Nat.Coprime 3 (orderOf (primeFormConjHom h (idGram K n) M)))
    (hρ : primeFormConjHom h (idGram K n) M * primeFormConjHom h (idGram K n) x =
      primeFormConjHom h (idGram K n) x * primeFormConjHom h (idGram K n) M) :
    M * x = x * M := by
  classical
  have hn0 : 0 < n := by omega
  obtain ⟨d, hd⟩ := exists_scalar_of_conj_commute hn hne hρ
  set m := orderOf (primeFormConjHom h (idGram K n) M) with hm
  have hMm : M ^ m ∈ idScalarKernel h n := by
    rw [← primeFormConjHom_eq_one_iff_of_ne hn hne, map_pow, hm]
    exact pow_orderOf_eq_one _
  obtain ⟨s, -, hs⟩ := hMm
  have hrel := pow_mul_comm_central (a := (M : GL (Fin n) K)) (b := (x : GL (Fin n) K))
    (s := GeneralLinearGroup.scalar (Fin n) d)
    (fun g => GeneralLinearGroup.scalar_commute d g) hd m
  have hMmGL : (M : GL (Fin n) K) ^ m = GeneralLinearGroup.scalar (Fin n) s := by
    have := hs
    simpa using this
  rw [hMmGL, ← map_pow] at hrel
  have h2 : (x : GL (Fin n) K) * GeneralLinearGroup.scalar (Fin n) s =
      ((x : GL (Fin n) K) * GeneralLinearGroup.scalar (Fin n) s) *
        GeneralLinearGroup.scalar (Fin n) (d ^ m) := by
    have := hrel
    rwa [GeneralLinearGroup.scalar_commute s (x : GL (Fin n) K)] at this
  have h3 : GeneralLinearGroup.scalar (Fin n) (d ^ m) = 1 := by
    have := mul_left_cancel (a := (x : GL (Fin n) K) * GeneralLinearGroup.scalar (Fin n) s)
      (b := 1) (c := GeneralLinearGroup.scalar (Fin n) (d ^ m)) (by rw [mul_one]; exact h2)
    exact this.symm
  have h4 : d ^ m = 1 := glScalar_injective hn0 (by rw [h3, map_one])
  have h5 : d = 1 := by
    have := pow_gcd_eq_one.2 ⟨unit_pow_three_eq_one h hq d, h4⟩
    rwa [hcop, pow_one] at this
  apply Subtype.ext
  rw [h5, map_one, mul_one] at hd
  exact hd

end Coprime

end CFSG.HardMathSupport.Timmesfeld.CrossChar
