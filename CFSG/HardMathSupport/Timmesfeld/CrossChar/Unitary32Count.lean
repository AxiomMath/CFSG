module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Basify
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
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Classical

variable {G : Type*} [Group G] {K : Type*} [Field K]

theorem index_ker_le_three [Finite G] (ψ : G →* Kˣ) (hψ : ∀ x, ψ x ^ 3 = 1) :
    ψ.ker.index ≤ 3 := by
  rw [Subgroup.index_ker]
  have h1 : ψ.range ≤ rootsOfUnity 3 K := by
    rintro _ ⟨x, rfl⟩
    exact (mem_rootsOfUnity _ _).2 (hψ x)
  have : Finite (rootsOfUnity 3 K) := inferInstance
  exact (Subgroup.card_le_of_le h1).trans (card_rootsOfUnity K 3)

theorem three_mul_card_inf_ge [Finite G] (hG : Nat.card G = 27) (ψ φ : G →* Kˣ)
    (hψ : ∀ x, ψ x ^ 3 = 1) (hφ : ∀ x, φ x ^ 3 = 1) :
    Nat.card ψ.ker ≤ 3 * Nat.card (ψ.ker ⊓ φ.ker : Subgroup G) := by
  have h1 := index_ker_le_three ψ hψ
  have h2 := index_ker_le_three φ hφ
  have h3 : (ψ.ker ⊓ φ.ker).index ≤ ψ.ker.index * φ.ker.index := Subgroup.index_inf_le
  have e1 := Subgroup.card_mul_index ψ.ker
  have e2 := Subgroup.card_mul_index φ.ker
  have e3 := Subgroup.card_mul_index (ψ.ker ⊓ φ.ker)
  rw [hG] at e1 e2 e3
  set a := Nat.card ψ.ker
  set b := Nat.card φ.ker
  set d := Nat.card (ψ.ker ⊓ φ.ker : Subgroup G)
  set ia := ψ.ker.index
  set ib := φ.ker.index
  set id := (ψ.ker ⊓ φ.ker).index
  have h4 : 27 ≤ d * (ia * ib) := by
    calc 27 = d * id := e3.symm
      _ ≤ d * (ia * ib) := Nat.mul_le_mul_left _ h3
  have h5 : a * ia = 27 := e1
  have h6 : 27 * a ≤ 27 * (d * ib) := by
    calc 27 * a ≤ (d * (ia * ib)) * a := Nat.mul_le_mul_right _ h4
      _ = d * ib * (a * ia) := by ring
      _ = 27 * (d * ib) := by rw [h5]; ring
  have h7 : a ≤ d * ib := Nat.le_of_mul_le_mul_left h6 (by norm_num)
  calc a ≤ d * ib := h7
    _ ≤ d * 3 := Nat.mul_le_mul_left _ h2
    _ = 3 * d := by ring

theorem exists_four_of_chars [Fintype G] (hG : Nat.card G = 27) {n : ℕ} (hn : 7 ≤ n)
    (c : Fin n → G →* Kˣ) (hc : ∀ k x, c k x ^ 3 = 1) (i j : Fin n) (hij : i ≠ j) :
    ∃ x : G, x ≠ 1 ∧ c i x = c j x ∧ 4 ≤ (Finset.univ.filter fun k => c k x = c i x).card := by
  by_contra hcon
  push Not at hcon
  have : Finite G := Nat.finite_of_card_ne_zero (by rw [hG]; norm_num)
  set A : Subgroup G := (c i * (c j)⁻¹).ker with hA
  set B : Fin n → Subgroup G := fun k => (c k * (c i)⁻¹).ker with hB
  have hmemA : ∀ x, x ∈ A ↔ c i x = c j x := fun x => by
    rw [hA, MonoidHom.mem_ker, MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_eq_one]
  have hmemB : ∀ k x, x ∈ B k ↔ c k x = c i x := fun k x => by
    rw [hB, MonoidHom.mem_ker, MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_eq_one]
  have hcA : ∀ x, (c i * (c j)⁻¹) x ^ 3 = 1 := fun x => by
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_pow, inv_pow, hc, hc, inv_one, mul_one]
  have hcB : ∀ k x, (c k * (c i)⁻¹) x ^ 3 = 1 := fun k x => by
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_pow, inv_pow, hc, hc, inv_one, mul_one]
  set a := Nat.card A with ha
  have hindA : A.index ≤ 3 := index_ker_le_three _ hcA
  have ha9 : 9 ≤ a := by
    have e : a * A.index = 27 := by rw [ha, Subgroup.card_mul_index, hG]
    have hpos : 0 < A.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    by_contra hlt
    have : a * A.index ≤ 8 * 3 := Nat.mul_le_mul (by omega) hindA
    omega
  have ha27 : a ≤ 27 := hG ▸ Subgroup.card_le_card_group A
  set f : Fin n → ℕ := fun k => Nat.card ↥(A ⊓ B k) with hf
  have hf3 : ∀ k, a ≤ 3 * f k := fun k =>
    three_mul_card_inf_ge hG _ _ hcA (hcB k)
  have hfi : f i = a := by
    have : A ⊓ B i = A := by
      refine le_antisymm inf_le_left (le_inf le_rfl fun x _ => (hmemB i x).2 rfl)
    simp only [hf, this, ha]
  have hfj : f j = a := by
    have : A ⊓ B j = A := by
      refine le_antisymm inf_le_left (le_inf le_rfl fun x hx => (hmemB j x).2 ?_)
      exact ((hmemA x).1 hx).symm
    simp only [hf, this, ha]
  set Af : Finset G := Finset.univ.filter (· ∈ A) with hAf
  have hAfcard : Af.card = a := by
    rw [hAf, ha, Nat.card_eq_fintype_card, Fintype.card_subtype]
  set N : G → ℕ := fun x => (Finset.univ.filter fun k => c k x = c i x).card with hN
  have hsum : ∑ x ∈ Af, N x = ∑ k, f k := by
    have h1 : ∀ x, N x = ∑ k, if c k x = c i x then 1 else 0 := fun x => by
      simp only [hN, Finset.card_filter]
    simp_rw [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hf]
    rw [Finset.sum_boole, Nat.cast_id, Nat.card_eq_fintype_card, Fintype.card_subtype,
      hAf, Finset.filter_filter]
    congr 1
    ext x
    simp [hmemB]
  have h1A : (1 : G) ∈ Af := by simp [hAf, hmemA]
  have hN1 : N 1 = n := by
    simp [hN]
  have hup : ∑ x ∈ Af, N x ≤ n + 3 * (a - 1) := by
    rw [← Finset.add_sum_erase Af N h1A, hN1]
    refine Nat.add_le_add_left ?_ _
    calc ∑ x ∈ Af.erase 1, N x ≤ ∑ x ∈ Af.erase 1, 3 := by
          refine Finset.sum_le_sum fun x hx => ?_
          obtain ⟨hx1, hxA⟩ := Finset.mem_erase.1 hx
          have hxA' : x ∈ A := by simpa [hAf] using hxA
          have := hcon x hx1 ((hmemA x).1 hxA')
          exact Nat.lt_succ_iff.1 this
      _ = 3 * (a - 1) := by
          rw [Finset.sum_const, Finset.card_erase_of_mem h1A, hAfcard, smul_eq_mul, mul_comm]
  have hlow : ∑ k, (a + if k ∈ ({i, j} : Finset (Fin n)) then 2 * a else 0) ≤ ∑ k, 3 * f k := by
    refine Finset.sum_le_sum fun k _ => ?_
    by_cases hk : k ∈ ({i, j} : Finset (Fin n))
    · simp only [hk, ↓reduceIte]
      rcases Finset.mem_insert.1 hk with rfl | hk'
      · rw [hfi]; omega
      · rw [Finset.mem_singleton.1 hk', hfj]; omega
    · simp only [hk, ↓reduceIte]
      have := hf3 k
      omega
  have hsplit : ∑ k : Fin n, (a + if k ∈ ({i, j} : Finset (Fin n)) then 2 * a else 0) =
      n * a + 4 * a := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
      Finset.card_pair hij, smul_eq_mul]
    ring
  rw [← Finset.mul_sum, ← hsum] at hlow
  rw [hsplit] at hlow
  have h3 := Nat.mul_le_mul_left 3 hup
  obtain ⟨b, hb⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  have hb' : a - 1 = b := by omega
  rw [hb'] at h3
  rw [hb] at hlow ha9
  nlinarith [Nat.mul_le_mul hn ha9]

end CFSG.HardMathSupport.Timmesfeld.CrossChar
