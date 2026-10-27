module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Wong77.GolayBasic
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
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.EvenSporadicStandard.Wong77.Module.Masks

@[expose] def bitCount (x : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => bitCount x n + if x.testBit n then 1 else 0

theorem bitCount_eq_sum (x n : ℕ) :
    bitCount x n = ∑ i ∈ Finset.range n, if x.testBit i then 1 else 0 := by
  induction n with
  | zero => simp [bitCount]
  | succ n ih => rw [bitCount, ih, Finset.sum_range_succ]

theorem hammingNorm_wordOfNat' (x : ℕ) : hammingNorm (wordOfNat x) = bitCount x 23 := by
  rw [bitCount_eq_sum, hammingNorm, Finset.card_filter,
    ← Fin.sum_univ_eq_sum_range (fun i => if x.testBit i then 1 else 0)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [wordOfNat]

theorem wordOfNat_xor' (x y : ℕ) : wordOfNat (Nat.xor x y) = wordOfNat x + wordOfNat y :=
  wordOfNat_xor x y

@[expose] def spanList : (n : ℕ) → (Fin n → ℕ) → ℕ → List ℕ
  | 0, _, acc => [acc]
  | n + 1, r, acc =>
      spanList n (fun i => r i.succ) acc ++ spanList n (fun i => r i.succ) (Nat.xor acc (r 0))

theorem length_spanList : ∀ (n : ℕ) (r : Fin n → ℕ) (acc : ℕ),
    (spanList n r acc).length = 2 ^ n := by
  intro n
  induction n with
  | zero => intro r acc; simp [spanList]
  | succ n ih =>
    intro r acc
    simp only [spanList, List.length_append, ih, pow_succ]
    omega

theorem exists_mem_spanList : ∀ (n : ℕ) (r : Fin n → ℕ) (acc : ℕ) (m : Fin n → ZMod 2),
    ∃ x ∈ spanList n r acc, wordOfNat x = wordOfNat acc + ∑ k, m k • wordOfNat (r k) := by
  intro n
  induction n with
  | zero => intro r acc m; exact ⟨acc, by simp [spanList], by simp⟩
  | succ n ih =>
    intro r acc m
    rw [Fin.sum_univ_succ]
    have hm : m 0 = 0 ∨ m 0 = 1 := by
      generalize m 0 = t
      revert t
      decide
    rcases hm with hm | hm
    · obtain ⟨x, hx, hxe⟩ := ih (fun i => r i.succ) acc (fun i => m i.succ)
      exact ⟨x, by rw [spanList]; exact List.mem_append_left _ hx, by rw [hxe, hm]; simp⟩
    · obtain ⟨x, hx, hxe⟩ := ih (fun i => r i.succ) (Nat.xor acc (r 0)) (fun i => m i.succ)
      refine ⟨x, by rw [spanList]; exact List.mem_append_right _ hx, ?_⟩
      rw [hxe, hm, wordOfNat_xor' acc (r 0)]
      simp only [one_smul]
      abel

theorem mem_spanList : ∀ (n : ℕ) (r : Fin n → ℕ) (acc x : ℕ), x ∈ spanList n r acc →
    ∃ m : Fin n → ZMod 2, wordOfNat x = wordOfNat acc + ∑ k, m k • wordOfNat (r k) := by
  intro n
  induction n with
  | zero =>
    intro r acc x hx
    simp only [spanList, List.mem_singleton] at hx
    exact ⟨fun _ => 0, by simp [hx]⟩
  | succ n ih =>
    intro r acc x hx
    simp only [spanList, List.mem_append] at hx
    rcases hx with hx | hx
    · obtain ⟨m, hm⟩ := ih _ _ _ hx
      refine ⟨Fin.cons 0 m, ?_⟩
      rw [Fin.sum_univ_succ, hm]
      simp
    · obtain ⟨m, hm⟩ := ih _ _ _ hx
      refine ⟨Fin.cons 1 m, ?_⟩
      rw [Fin.sum_univ_succ, hm]
      change _ = wordOfNat acc + (1 • wordOfNat (r 0) + _)
      rw [one_smul, wordOfNat_xor']
      simp only [Fin.cons_succ]
      abel

@[expose] def golayMaskList : List ℕ :=
  [7684609, 3817986, 3113476, 6062600, 5742608, 2580512, 3252800, 5137024, 4440832, 6988800,
    5859328, 3993600]

@[expose] def golayMaskFast (k : Fin 12) : ℕ := golayMaskList.getD k.val 0

theorem golayMaskFast_eq : golayMaskFast = golayMask :=
  funext fun k => by
    revert k
    decide

@[expose] def codeList : List ℕ := spanList 12 golayMaskFast 0

theorem mem_codeList_iff (v : Word) : v ∈ golayCode ↔ ∃ x ∈ codeList, wordOfNat x = v := by
  constructor
  · intro hv
    obtain ⟨m, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).1 hv
    obtain ⟨x, hx, hxe⟩ := exists_mem_spanList 12 golayMaskFast 0 m
    exact ⟨x, hx, by rw [hxe, wordOfNat_zero, zero_add, golayMaskFast_eq]; rfl⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨m, hm⟩ := mem_spanList 12 golayMaskFast 0 x hx
    rw [hm, wordOfNat_zero, zero_add, golayMaskFast_eq]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem nodup_map_codeList : (codeList.map wordOfNat).Nodup := by
  classical
  set l := codeList.map wordOfNat with hl
  have hlen : l.length = 2 ^ 12 := by simp [hl, codeList, length_spanList]
  have hsub : (golayCode : Set Word) ⊆ (l.toFinset : Set Word) := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := (mem_codeList_iff v).1 hv
    exact Finset.mem_coe.2 (List.mem_toFinset.2 (List.mem_map.2 ⟨x, hx, rfl⟩))
  have hge : (golayCode : Set Word).ncard = 2 ^ 12 := by
    rw [← Nat.card_coe_set_eq]
    exact natCard_golayCode
  have hcard : 2 ^ 12 ≤ l.toFinset.card := by
    have := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    rwa [hge, Set.ncard_coe_finset] at this
  have heq : l.toFinset.card = l.length := le_antisymm (List.toFinset_card_le l) (hlen ▸ hcard)
  have hnd := (Multiset.toFinset_card_eq_card_iff_nodup (m := (l : Multiset Word))).1
    (by simpa using heq)
  exact Multiset.coe_nodup.1 hnd

end CFSG.EvenSporadicStandard.Wong77.Module.Masks
