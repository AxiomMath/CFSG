module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.CGT.Timmesfeld75

section Involutions

variable {Y : Type*} [Group Y]

private theorem involution_conj_pow {a w : Y} (ha : a * a = 1) (hinv : a * w * a = w⁻¹) (k : ℕ) :
    a * w ^ k * a = (w ^ k)⁻¹ := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have h : (a * w * a⁻¹) ^ k = a * w ^ k * a⁻¹ := conj_pow
  rw [hai, hinv, inv_pow] at h
  exact h.symm

private theorem pow_val_add {w : Y} {n : ℕ} [NeZero n] (hw : w ^ n = 1) (i j : ZMod n) :
    w ^ (i + j).val = w ^ i.val * w ^ j.val := by
  rw [ZMod.val_add, ← pow_add, ← pow_eq_pow_mod _ hw]

private theorem pow_val_zero {w : Y} {n : ℕ} : w ^ (0 : ZMod n).val = 1 := by
  rw [ZMod.val_zero, pow_zero]

private theorem pow_val_neg {w : Y} {n : ℕ} [NeZero n] (hw : w ^ n = 1) (i : ZMod n) :
    w ^ (-i).val = (w ^ i.val)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← pow_val_add hw, neg_add_cancel, pow_val_zero]

private theorem pow_val_sub {w : Y} {n : ℕ} [NeZero n] (hw : w ^ n = 1) (i j : ZMod n) :
    w ^ (j - i).val = w ^ (-i).val * w ^ j.val := by
  rw [← pow_val_add hw, neg_add_eq_sub]

private theorem pow_val_natCast {w : Y} {n : ℕ} (hw : w ^ n = 1) (k : ℕ) :
    w ^ (k : ZMod n).val = w ^ k := by
  rw [ZMod.val_natCast, ← pow_eq_pow_mod _ hw]

private def dihedralLift (a w : Y) {n : ℕ} : DihedralGroup n → Y
  | .r i => w ^ i.val
  | .sr i => a * w ^ i.val

private theorem dihedralLift_mul {a w : Y} {n : ℕ} [NeZero n] (ha : a * a = 1) (hw : w ^ n = 1)
    (hinv : a * w * a = w⁻¹) (x y : DihedralGroup n) :
    dihedralLift a w (x * y) = dihedralLift a w x * dihedralLift a w y := by
  have hcomm : ∀ i : ZMod n, w ^ i.val * a = a * w ^ (-i).val := by
    intro i
    rw [pow_val_neg hw]
    calc w ^ i.val * a = a * (a * w ^ i.val * a) := by rw [← mul_assoc, ← mul_assoc, ha, one_mul]
      _ = a * (w ^ i.val)⁻¹ := by rw [involution_conj_pow ha hinv]
  rcases x with i | i <;> rcases y with j | j
  · simp only [DihedralGroup.r_mul_r, dihedralLift]
    exact pow_val_add hw i j
  · simp only [DihedralGroup.r_mul_sr, dihedralLift]
    rw [pow_val_sub hw, ← mul_assoc (w ^ i.val), hcomm, mul_assoc]
  · simp only [DihedralGroup.sr_mul_r, dihedralLift]
    rw [pow_val_add hw, mul_assoc]
  · simp only [DihedralGroup.sr_mul_sr, dihedralLift]
    rw [pow_val_sub hw, pow_val_neg hw, ← mul_assoc, involution_conj_pow ha hinv]

end Involutions

theorem dihedral_mulEquiv_of_involutions {Y : Type*} [Group Y] {a b : Y} {n : ℕ} (hn : Odd n)
    (ha : a * a = 1) (ha1 : a ≠ 1) (hb : b * b = 1) (hab : orderOf (a * b) = n)
    (hgen : Subgroup.closure ({a, b} : Set Y) = ⊤) : Nonempty (DihedralGroup n ≃* Y) := by
  have : NeZero n := ⟨hn.pos.ne'⟩
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hwn : (a * b) ^ n = 1 := by rw [← hab]; exact pow_orderOf_eq_one _
  have hinv : a * (a * b) * a = (a * b)⁻¹ := by
    rw [mul_inv_rev, hai, hbi, ← mul_assoc, ha, one_mul]
  let φ : DihedralGroup n →* Y := MonoidHom.mk' (dihedralLift a (a * b))
    (dihedralLift_mul ha hwn hinv)
  have hφr : ∀ i : ZMod n, φ (DihedralGroup.r i) = (a * b) ^ i.val := fun i => rfl
  have hφsr : ∀ i : ZMod n, φ (DihedralGroup.sr i) = a * (a * b) ^ i.val := fun i => rfl
  have hsurj : Function.Surjective φ := by
    refine MonoidHom.range_eq_top.mp (top_unique ?_)
    rw [← hgen, Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    refine ⟨⟨DihedralGroup.sr 0, ?_⟩, ⟨DihedralGroup.sr 1, ?_⟩⟩
    · rw [hφsr, ZMod.val_zero, pow_zero, mul_one]
    · have h1 : (a * b) ^ (1 : ZMod n).val = a * b := by
        simpa using pow_val_natCast hwn 1
      rw [hφsr, h1, ← mul_assoc, ha, one_mul]
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro (i | i) hx
    · have h1 : (a * b) ^ i.val = 1 := by rw [← hφr]; exact hx
      have h2 : orderOf (a * b) ∣ i.val := orderOf_dvd_of_pow_eq_one h1
      rw [hab] at h2
      have h3 : i.val = 0 := Nat.eq_zero_of_dvd_of_lt h2 (ZMod.val_lt i)
      rw [ZMod.val_eq_zero] at h3
      rw [h3]
      rfl
    · exfalso
      have h1 : a * (a * b) ^ i.val = 1 := by rw [← hφsr]; exact hx
      have h2 : a ^ n = 1 := by
        have h3 : a = ((a * b) ^ i.val)⁻¹ := eq_inv_of_mul_eq_one_left h1
        rw [h3, inv_pow, ← pow_mul, mul_comm, pow_mul, hwn, one_pow, inv_one]
      apply ha1
      obtain ⟨m, hm⟩ := hn
      rw [hm, pow_succ, pow_mul, sq, ha, one_pow, one_mul] at h2
      exact h2
  exact ⟨MulEquiv.ofBijective φ ⟨hinj, hsurj⟩⟩

theorem dihedral_pCore_trivial {n : ℕ} (hn : Odd n) (h3 : 3 ≤ n)
    (N : Subgroup (DihedralGroup n)) (hN : N.Normal) (h2 : IsPGroup 2 N) : N = ⊥ := by
  have : NeZero n := ⟨hn.pos.ne'⟩
  have hrot : ∀ i : ZMod n, DihedralGroup.r i ∈ N → DihedralGroup.r i = 1 := by
    intro i hi
    obtain ⟨k, hk⟩ := h2 ⟨DihedralGroup.r i, hi⟩
    have hk' : DihedralGroup.r i ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hn' : DihedralGroup.r i ^ n = 1 := by simp
    exact (pow_eq_one_iff_of_coprime
      (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hn))).mp ⟨hn', hk'⟩
  have hsr : ∀ i : ZMod n, DihedralGroup.sr i ∉ N := by
    intro i hi
    obtain ⟨m, hm⟩ := hn
    have hhalf : (2 : ZMod n) * ((m : ZMod n) + 1) = 1 := by
      have h0 : ((2 * m + 1 : ℕ) : ZMod n) = 0 := by rw [← hm]; exact ZMod.natCast_self n
      push_cast at h0
      linear_combination h0
    set h : ZMod n := (m : ZMod n) + 1 with hh
    have hc := hN.conj_mem _ hi (DihedralGroup.sr (i + h))
    have hprod := N.mul_mem hi hc
    have hr1 : DihedralGroup.sr i * (DihedralGroup.sr (i + h) * DihedralGroup.sr i *
        (DihedralGroup.sr (i + h))⁻¹) = DihedralGroup.r 1 := by
      simp only [DihedralGroup.inv_sr, DihedralGroup.sr_mul_sr, DihedralGroup.r_mul_sr]
      exact congrArg DihedralGroup.r (by linear_combination hhalf)
    rw [hr1] at hprod
    have h4 : orderOf (DihedralGroup.r (1 : ZMod n)) = 1 := by
      rw [hrot 1 hprod]
      exact orderOf_one
    rw [DihedralGroup.orderOf_r_one] at h4
    omega
  rw [Subgroup.eq_bot_iff_forall]
  rintro (i | i) hx
  · exact hrot i hx
  · exact absurd hx (hsr i)

end CFSG.CGT.Timmesfeld75
