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
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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

public section

namespace CFSG.Certificates

open Subgroup

variable {G J : Type*} [Group G] [Group J]

theorem ker_le_and_card_le [Finite J] (φ : G →* J) (hφ : Function.Surjective φ) (T : Subgroup G)
    [T.FiniteIndex] [Finite T] {I M c : ℕ} (hM : 0 < M) (hTidx : T.index ≤ I)
    (hTJ : Nat.card (T.map φ) ≤ M) (hJ : I * M ≤ Nat.card J) (hT : Nat.card T ≤ c * M) :
    φ.ker ≤ T ∧ Nat.card φ.ker ≤ c ∧ M ≤ Nat.card (T.map φ) := by
  have hrange : φ.range = ⊤ := MonoidHom.range_eq_top.mpr hφ
  have hidxmap : (T.map φ).index = (T ⊔ φ.ker).index := by
    rw [Subgroup.index_map, hrange, Subgroup.index_top, mul_one]
  have hcardJ : (T.map φ).index * Nat.card (T.map φ) = Nat.card J := Subgroup.index_mul_card _
  have hTpos : 0 < T.index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  have hIa : I ≤ (T.map φ).index := by
    by_contra hlt
    push Not at hlt
    have : (T.map φ).index * Nat.card (T.map φ) < I * M :=
      lt_of_le_of_lt (Nat.mul_le_mul_left _ hTJ) (Nat.mul_lt_mul_of_pos_right hlt hM)
    omega
  have hdvd : (T ⊔ φ.ker).index ∣ T.index := Subgroup.index_dvd_of_le le_sup_left
  have hle : (T ⊔ φ.ker).index ≤ T.index := Nat.le_of_dvd hTpos hdvd
  have heq : T.index = (T ⊔ φ.ker).index := by omega
  have hrel : T.relIndex (T ⊔ φ.ker) = 1 := by
    have := Subgroup.relIndex_mul_index (le_sup_left : T ≤ T ⊔ φ.ker)
    have hpos : 0 < (T ⊔ φ.ker).index := by omega
    rw [← heq] at this
    have h1 : T.relIndex (T ⊔ φ.ker) * T.index = 1 * T.index := by rw [this, one_mul]
    exact Nat.eq_of_mul_eq_mul_right hTpos h1
  have hker : φ.ker ≤ T := by
    have := Subgroup.relIndex_eq_one.mp hrel
    exact le_trans le_sup_right this
  refine ⟨hker, ?_, ?_⟩
  swap
  ·
    by_contra hlt
    push Not at hlt
    have : (T.map φ).index * Nat.card (T.map φ) < I * M := by
      calc (T.map φ).index * Nat.card (T.map φ) ≤ I * Nat.card (T.map φ) :=
            Nat.mul_le_mul_right _ (by omega)
        _ < I * M := Nat.mul_lt_mul_of_pos_left hlt (by omega)
    omega
  have hcard := Subgroup.card_ker_mul_card_range (φ.domRestrict T)
  rw [MonoidHom.domRestrict_range] at hcard
  have hkercard : Nat.card (φ.domRestrict T).ker = Nat.card φ.ker := by
    rw [MonoidHom.ker_domRestrict]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker).toEquiv
  rw [hkercard] at hcard
  have hMb : M ≤ Nat.card (T.map φ) := by
    by_contra hlt
    push Not at hlt
    have : (T.map φ).index * Nat.card (T.map φ) < I * M := by
      calc (T.map φ).index * Nat.card (T.map φ) ≤ I * Nat.card (T.map φ) :=
            Nat.mul_le_mul_right _ (by omega)
        _ < I * M := Nat.mul_lt_mul_of_pos_left hlt (by omega)
    omega
  have h1 : Nat.card φ.ker * M ≤ c * M := by
    calc Nat.card φ.ker * M ≤ Nat.card φ.ker * Nat.card (T.map φ) := Nat.mul_le_mul_left _ hMb
      _ = Nat.card T := hcard
      _ ≤ c * M := hT
  exact Nat.le_of_mul_le_mul_right h1 hM

theorem finite_map (f : G →* J) (H : Subgroup G) [Finite H] : Finite (H.map f) :=
  Finite.of_surjective (fun x : H => (⟨f x, Subgroup.mem_map_of_mem f x.2⟩ : H.map f)) (by
    rintro ⟨_, y, hy, rfl⟩; exact ⟨⟨y, hy⟩, rfl⟩)

theorem card_range_le_index_mul (f : G →* J) [Finite f.range] (K : Subgroup G) [K.FiniteIndex]
    {k : ℕ} (hK : K.index ≤ k) : Nat.card f.range ≤ k * Nat.card (K.map f) := by
  have hq : Function.Surjective f.rangeRestrict := f.rangeRestrict_surjective
  have hdvd := Subgroup.index_map_dvd K hq
  have hKpos : 0 < K.index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  have hle : (K.map f.rangeRestrict).index ≤ k :=
    le_trans (Nat.le_of_dvd hKpos hdvd) hK
  have hcard : (K.map f.rangeRestrict).index * Nat.card (K.map f.rangeRestrict) =
      Nat.card f.range := Subgroup.index_mul_card _
  have hmap : K.map f = (K.map f.rangeRestrict).map f.range.subtype := by
    rw [Subgroup.map_map]
    rfl
  have hc : Nat.card (K.map f) = Nat.card (K.map f.rangeRestrict) := by
    rw [hmap]
    exact Subgroup.card_map_of_injective f.range.subtype_injective
  rw [hc, ← hcard]
  exact Nat.mul_le_mul_right _ hle

theorem eq_one_of_card_map_ge (f : G →* J) (H : Subgroup G) [Finite H] {k : ℕ}
    (h1 : Nat.card H ≤ k) (h2 : k ≤ Nat.card (H.map f)) {x : G} (hx : x ∈ H) (hfx : f x = 1) :
    x = 1 := by
  have hcard := Subgroup.card_ker_mul_card_range (f.domRestrict H)
  rw [MonoidHom.domRestrict_range] at hcard
  have := finite_map f H
  have hpos : 0 < Nat.card (H.map f) := Nat.card_pos
  have hker : Nat.card (f.domRestrict H).ker ≤ 1 := by
    by_contra hlt
    push Not at hlt
    have : 2 * Nat.card (H.map f) ≤ Nat.card H := by
      rw [← hcard]; exact Nat.mul_le_mul_right _ hlt
    omega
  have hsub : Subsingleton (f.domRestrict H).ker := by
    rw [← Finite.card_le_one_iff_subsingleton]; exact hker
  have : (⟨x, hx⟩ : H) ∈ (f.domRestrict H).ker := by
    rw [MonoidHom.mem_ker]; exact hfx
  have h1' := Subsingleton.elim (⟨⟨x, hx⟩, this⟩ : (f.domRestrict H).ker) 1
  have h3 := congrArg (fun y : (f.domRestrict H).ker => ((y : H) : G)) h1'
  simpa using h3

end CFSG.Certificates
