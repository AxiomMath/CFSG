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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.GH74.Uniqueness.SU.K.R4

open Subgroup

theorem five_contradiction {Y : Type} [Group Y] {ι : Type} (X : Finset Y) (hX : X.card = 5)
    (Λ : ι → Type) [∀ i, Group (Λ i)] [∀ i, Finite (Λ i)] (f : ∀ i, Y →* Λ i)
    (N : ι → Subgroup Y) (Ω : ∀ i, Subgroup (Λ i))
    (hΩ2 : ∀ i, ∃ m : ℕ, Nat.card (Ω i) = 2 ^ m) (hΩ4 : ∀ i, 4 ≤ Nat.card (Ω i))
    (htrans : ∀ i, ∀ u ∈ Ω i, ∀ v ∈ Ω i, u ≠ 1 → v ≠ 1 →
      ∃ n ∈ N i, f i n * u * (f i n)⁻¹ = v)
    (hinv : ∀ i, ∀ n ∈ N i, ∀ x ∈ X, n * x * n⁻¹ ∈ X)
    (hcross : ∀ i j, i ≠ j → ∀ n ∈ N i, f j n = 1)
    (hmem : ∀ i, ∀ x ∈ X, f i x ∈ Ω i)
    (hnontriv : ∀ x ∈ X, ∃ i, f i x ≠ 1) : False := by
  classical
  have : ∀ i, Fintype (Λ i) := fun i => Fintype.ofFinite _
  let Ωs : ∀ i, Finset (Λ i) := fun i => (Finset.univ.filter fun u => u ∈ Ω i).erase 1
  have hΩs_mem : ∀ i u, u ∈ Ωs i ↔ u ∈ Ω i ∧ u ≠ 1 := by
    intro i u
    simp only [Ωs, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have hΩs_card : ∀ i, (Ωs i).card + 1 = Nat.card (Ω i) := by
    intro i
    have h1 : (1 : Λ i) ∈ (Finset.univ.filter fun u => u ∈ Ω i) := by
      simp [Finset.mem_filter]
    have h2 : Nat.card (Ω i) = (Finset.univ.filter fun u => u ∈ Ω i).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have h3 := Finset.card_erase_add_one h1
    simp only [Ωs]
    omega
  have hΩs3 : ∀ i, 3 ≤ (Ωs i).card := fun i => by have := hΩ4 i; have := hΩs_card i; omega
  have hreach : ∀ i, ∀ x ∈ X, f i x ≠ 1 → ∀ y ∈ Ωs i, ∃ n ∈ N i, f i (n * x * n⁻¹) = y := by
    intro i x hx hfx y hy
    obtain ⟨hyΩ, hy1⟩ := (hΩs_mem i y).mp hy
    obtain ⟨n, hn, hnxy⟩ := htrans i (f i x) (hmem i x hx) y hyΩ hfx hy1
    refine ⟨n, hn, ?_⟩
    rw [map_mul, map_mul, map_inv, hnxy]
  have hconj : ∀ i j, i ≠ j → ∀ n ∈ N i, ∀ x, f j (n * x * n⁻¹) = f j x := by
    intro i j hij n hn x
    rw [map_mul, map_mul, map_inv, hcross i j hij n hn]
    simp
  let A : ι → Finset Y := fun i => X.filter fun x => f i x ≠ 1
  have hA_mem : ∀ i x, x ∈ A i ↔ x ∈ X ∧ f i x ≠ 1 := by
    intro i x; simp [A]
  have hA3 : ∀ i x, x ∈ A i → 3 ≤ (A i).card := by
    intro i x hx
    obtain ⟨hxX, hfx⟩ := (hA_mem i x).mp hx
    have hsub : Ωs i ⊆ (A i).image (f i) := by
      intro y hy
      obtain ⟨n, hn, hny⟩ := hreach i x hxX hfx y hy
      refine Finset.mem_image.mpr ⟨n * x * n⁻¹, (hA_mem i _).mpr ⟨hinv i n hn x hxX, ?_⟩, hny⟩
      rw [hny]; exact ((hΩs_mem i y).mp hy).2
    exact (hΩs3 i).trans ((Finset.card_le_card hsub).trans Finset.card_image_le)
  have hdisj : ∀ i j, i ≠ j → ∀ x, x ∈ A i → x ∉ A j := by
    intro i j hij x hxi hxj
    obtain ⟨hxX, hfxi⟩ := (hA_mem i x).mp hxi
    obtain ⟨-, hfxj⟩ := (hA_mem j x).mp hxj
    have hsub : Ωs i ×ˢ Ωs j ⊆ X.image (fun x' => (f i x', f j x')) := by
      intro yz hyz
      obtain ⟨hy, hz⟩ := Finset.mem_product.mp hyz
      obtain ⟨n, hn, hny⟩ := hreach i x hxX hfxi yz.1 hy
      have hx1X : n * x * n⁻¹ ∈ X := hinv i n hn x hxX
      have hfx1j : f j (n * x * n⁻¹) ≠ 1 := by rw [hconj i j hij n hn]; exact hfxj
      obtain ⟨n', hn', hn'z⟩ := hreach j _ hx1X hfx1j yz.2 hz
      refine Finset.mem_image.mpr ⟨n' * (n * x * n⁻¹) * n'⁻¹, hinv j n' hn' _ hx1X, ?_⟩
      refine Prod.ext ?_ hn'z
      show f i (n' * (n * x * n⁻¹) * n'⁻¹) = yz.1
      rw [hconj j i (Ne.symm hij) n' hn', hny]
    have hcardsub := (Finset.card_le_card hsub).trans Finset.card_image_le
    rw [Finset.card_product, hX] at hcardsub
    have h1 := hΩs3 i
    have h2 := hΩs3 j
    nlinarith
  have hXne : X.Nonempty := by
    rw [← Finset.card_pos, hX]; norm_num
  obtain ⟨x₀, hx₀⟩ := hXne
  obtain ⟨i₀, hi₀⟩ := hnontriv x₀ hx₀
  have hAX : ∀ x ∈ X, f i₀ x ≠ 1 := by
    intro x hx hfx
    obtain ⟨j, hj⟩ := hnontriv x hx
    have hji : j ≠ i₀ := by rintro rfl; exact hj hfx
    have hx0 : x₀ ∈ A i₀ := (hA_mem i₀ x₀).mpr ⟨hx₀, hi₀⟩
    have hxj : x ∈ A j := (hA_mem j x).mpr ⟨hx, hj⟩
    have hdis : Disjoint (A i₀) (A j) :=
      Finset.disjoint_left.mpr fun a ha haj => hdisj i₀ j (Ne.symm hji) a ha haj
    have hsub : A i₀ ∪ A j ⊆ X := by
      intro a ha
      rcases Finset.mem_union.mp ha with h | h
      · exact ((hA_mem _ _).mp h).1
      · exact ((hA_mem _ _).mp h).1
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdis, hX] at h1
    have := hA3 i₀ x₀ hx0
    have := hA3 j x hxj
    omega
  let fib : Λ i₀ → Finset Y := fun u => X.filter fun x => f i₀ x = u
  have hfib_le : ∀ u ∈ Ωs i₀, ∀ v ∈ Ωs i₀, (fib u).card ≤ (fib v).card := by
    intro u hu v hv
    obtain ⟨hu', hu1⟩ := (hΩs_mem i₀ u).mp hu
    obtain ⟨hv', hv1⟩ := (hΩs_mem i₀ v).mp hv
    obtain ⟨n, hn, hnuv⟩ := htrans i₀ u hu' v hv' hu1 hv1
    apply Finset.card_le_card_of_injOn (fun x => n * x * n⁻¹)
    · intro x hx
      have hx' := Finset.mem_filter.mp (Finset.mem_coe.mp hx)
      refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hinv i₀ n hn x hx'.1, ?_⟩)
      rw [map_mul, map_mul, map_inv, hx'.2, hnuv]
    · intro x _ y _ hxy
      simpa using hxy
  have hfib_eq : ∀ u ∈ Ωs i₀, ∀ v ∈ Ωs i₀, (fib u).card = (fib v).card :=
    fun u hu v hv => le_antisymm (hfib_le u hu v hv) (hfib_le v hv u hu)
  have hsum : X.card = ∑ u ∈ Ωs i₀, (fib u).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro x hx
    exact (hΩs_mem i₀ _).mpr ⟨hmem i₀ x hx, hAX x hx⟩
  have hne : (Ωs i₀).Nonempty := by
    rw [← Finset.card_pos]; have := hΩs3 i₀; omega
  obtain ⟨u₀, hu₀⟩ := hne
  have hsum' : ∑ u ∈ Ωs i₀, (fib u).card = (Ωs i₀).card * (fib u₀).card := by
    rw [Finset.sum_congr rfl (fun u hu => hfib_eq u hu u₀ hu₀)]
    simp
  rw [hX] at hsum
  have hdvd : (Ωs i₀).card ∣ 5 := ⟨(fib u₀).card, by rw [hsum, hsum']⟩
  have hc3 := hΩs3 i₀
  have hc5 : (Ωs i₀).card = 5 := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hdvd with h | h
    · omega
    · exact h
  obtain ⟨m, hm⟩ := hΩ2 i₀
  have h6 : Nat.card (Ω i₀) = 6 := by have := hΩs_card i₀; omega
  rw [hm] at h6
  have : m ≤ 2 ∨ 3 ≤ m := by omega
  rcases this with hm2 | hm3
  · have : 2 ^ m ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hm2
    omega
  · have : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm3
    omega

end CFSG.GH74.Uniqueness.SU.K.R4
