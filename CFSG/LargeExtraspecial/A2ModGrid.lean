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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.LargeExtraspecial.A2Mod

open Module Submodule

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

namespace Grid

theorem add_self (x : V) : x + x = 0 := by
  rw [← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem eq_iff_add_eq_zero {x y : V} : x = y ↔ x + y = 0 := by
  refine ⟨fun h => h ▸ add_self x, fun h => ?_⟩
  linear_combination (norm := (match_scalars <;> decide)) (1 : ZMod 2) • h

theorem mem_span_pair {x y z : V} :
    z ∈ span (ZMod 2) {x, y} ↔ z = 0 ∨ z = x ∨ z = y ∨ z = x + y := by
  rw [Submodule.mem_span_pair]
  constructor
  · rintro ⟨a, b, rfl⟩
    have hab : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases hab a with rfl | rfl <;> rcases hab b with rfl | rfl <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, 0, by simp⟩
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
    · exact ⟨1, 1, by simp⟩

theorem linearIndependent_pair_iff {x y : V} :
    LinearIndependent (ZMod 2) ![x, y] ↔ x ≠ 0 ∧ y ≠ 0 ∧ x ≠ y := by
  rw [LinearIndependent.pair_iff]
  have hab : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  constructor
  · intro h
    refine ⟨fun hx => ?_, fun hy => ?_, fun hxy => ?_⟩
    · exact one_ne_zero (h 1 0 (by simp [hx])).1
    · exact one_ne_zero (h 0 1 (by simp [hy])).2
    · exact one_ne_zero (h 1 1 (by rw [one_smul, one_smul, hxy, add_self])).1
  · rintro ⟨hx, hy, hxy⟩ s t hst
    rcases hab s with rfl | rfl <;> rcases hab t with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · exact absurd (by simpa using hst) hy
    · exact absurd (by simpa using hst) hx
    · exact absurd (eq_iff_add_eq_zero.mpr (by simpa using hst)) hxy

theorem exists_of_inf_span_ne_bot {ℓ : Submodule (ZMod 2) V} {x y : V}
    (h : ℓ ⊓ span (ZMod 2) {x, y} ≠ ⊥) :
    ∃ z ∈ ℓ, z ≠ 0 ∧ (z = x ∨ z = y ∨ z = x + y) := by
  obtain ⟨z, hz, hz0⟩ := (Submodule.ne_bot_iff _).mp h
  rw [Submodule.mem_inf] at hz
  rcases mem_span_pair.mp hz.2 with h0 | h1 | h2 | h3
  · exact absurd h0 hz0
  · exact ⟨z, hz.1, hz0, Or.inl h1⟩
  · exact ⟨z, hz.1, hz0, Or.inr (Or.inl h2)⟩
  · exact ⟨z, hz.1, hz0, Or.inr (Or.inr h3)⟩

theorem eq_of_mem_line {ℓ : Submodule (ZMod 2) V} (hℓ : finrank (ZMod 2) ℓ = 2) {x y z : V}
    (hx : x ∈ ℓ) (hy : y ∈ ℓ) (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hxy : x ≠ y) (hz : z ∈ ℓ) :
    z = 0 ∨ z = x ∨ z = y ∨ z = x + y := by
  have : FiniteDimensional (ZMod 2) ℓ := Module.finite_of_finrank_pos (by omega)
  have hli : LinearIndependent (ZMod 2) ![x, y] := linearIndependent_pair_iff.mpr ⟨hx0, hy0, hxy⟩
  have hle : span (ZMod 2) {x, y} ≤ ℓ := by
    rw [Submodule.span_le]
    rintro w (rfl | rfl)
    exacts [hx, hy]
  have h2 : finrank (ZMod 2) (span (ZMod 2) ({x, y} : Set V)) = 2 := by
    have h' := finrank_span_eq_card hli
    rw [Fintype.card_fin, Matrix.range_cons, Matrix.range_cons, Matrix.range_empty,
      Set.union_empty, Set.singleton_union] at h'
    exact h'
  have heq : span (ZMod 2) {x, y} = ℓ := Submodule.eq_of_le_of_finrank_eq hle (by rw [h2, hℓ])
  rw [← heq] at hz
  exact mem_span_pair.mp hz

theorem eq_span_of_mem {ℓ : Submodule (ZMod 2) V} (hℓ : finrank (ZMod 2) ℓ = 2) {x y : V}
    (hx : x ∈ ℓ) (hy : y ∈ ℓ) (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hxy : x ≠ y) :
    ℓ = span (ZMod 2) {x, y} := by
  refine le_antisymm (fun z hz => ?_) ?_
  · rw [mem_span_pair]
    exact eq_of_mem_line hℓ hx hy hx0 hy0 hxy hz
  · rw [Submodule.span_le]
    rintro w (rfl | rfl)
    exacts [hx, hy]

theorem eq_zero_of_mem_of_mem {U₁ U₂ : Submodule (ZMod 2) V} (hU : U₁ ⊓ U₂ = ⊥) {x : V}
    (h₁ : x ∈ U₁) (h₂ : x ∈ U₂) : x = 0 := by
  have hx : x ∈ U₁ ⊓ U₂ := Submodule.mem_inf.mpr ⟨h₁, h₂⟩
  rwa [hU, Submodule.mem_bot] at hx

theorem eq_of_add_eq_add {U₁ U₂ : Submodule (ZMod 2) V} (hU : U₁ ⊓ U₂ = ⊥) {a a' b b' : V}
    (ha : a ∈ U₁) (ha' : a' ∈ U₁) (hb : b ∈ U₂) (hb' : b' ∈ U₂) (h : a + b = a' + b') :
    a = a' := by
  have h2 : a - a' = b' - b := by rw [sub_eq_sub_iff_add_eq_add, h, add_comm]
  refine sub_eq_zero.mp (eq_zero_of_mem_of_mem hU (U₁.sub_mem ha ha') ?_)
  rw [h2]
  exact U₂.sub_mem hb' hb

theorem false_of_meet_three {U₁ U₂ ℓ : Submodule (ZMod 2) V} (hU : U₁ ⊓ U₂ = ⊥)
    (hℓ : finrank (ZMod 2) ℓ = 2) {p p' s s' : V} (hp : p ∈ U₁) (hp' : p' ∈ U₁) (hs : s ∈ U₂)
    (hs' : s' ∈ U₂) (hp0 : p ≠ 0) (hpp : p ≠ p') (hss : s ≠ s') (hp'ℓ : p' ∉ ℓ) (hs'ℓ : s' ∉ ℓ)
    (h₁ : ℓ ⊓ span (ZMod 2) {p', s'} ≠ ⊥) (h₂ : ℓ ⊓ span (ZMod 2) {p', s} ≠ ⊥)
    (h₃ : ℓ ⊓ span (ZMod 2) {p, s'} ≠ ⊥) : False := by
  have h01 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  obtain ⟨x, hx, -, hx'⟩ := exists_of_inf_span_ne_bot h₁
  rcases hx' with h | h | rfl
  · exact hp'ℓ (h ▸ hx)
  · exact hs'ℓ (h ▸ hx)
  obtain ⟨y, hy, hy0, hy'⟩ := exists_of_inf_span_ne_bot h₂
  obtain ⟨ε, rfl⟩ : ∃ ε : ZMod 2, y = ε • p' + s := by
    rcases hy' with h | h | h
    · exact absurd (h ▸ hy) hp'ℓ
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by simp [h]⟩
  obtain ⟨z, hz, hz0, hz'⟩ := exists_of_inf_span_ne_bot h₃
  obtain ⟨δ, rfl⟩ : ∃ δ : ZMod 2, z = p + δ • s' := by
    rcases hz' with h | h | h
    · exact ⟨0, by simp [h]⟩
    · exact absurd (h ▸ hz) hs'ℓ
    · exact ⟨1, by simp [h]⟩
  have hx0 : p' + s' ≠ 0 := by
    intro h
    refine hp'ℓ ?_
    rw [eq_of_add_eq_add hU hp' U₁.zero_mem hs' U₂.zero_mem (h.trans (add_zero 0).symm)]
    exact ℓ.zero_mem
  have hxy : p' + s' ≠ ε • p' + s := by
    intro h
    rcases h01 ε with rfl | rfl
    · refine hp'ℓ ?_
      rw [zero_smul] at h
      rw [eq_of_add_eq_add hU hp' U₁.zero_mem hs' hs h]
      exact ℓ.zero_mem
    · rw [one_smul] at h
      exact hss (add_left_cancel h).symm
  have hδ : δ • s' ∈ U₂ := U₂.smul_mem δ hs'
  rcases eq_of_mem_line hℓ hx hy hx0 hy0 hxy hz with h | h | h | h
  · exact hz0 h
  · exact hpp (eq_of_add_eq_add hU hp hp' hδ hs' h)
  · have := eq_of_add_eq_add hU hp (U₁.smul_mem ε hp') hδ hs h
    rcases h01 ε with rfl | rfl
    · exact hp0 (by simpa using this)
    · exact hpp (by simpa using this)
  · have h' : p + δ • s' = (p' + ε • p') + (s' + s) := by rw [h]; abel
    have := eq_of_add_eq_add hU hp (U₁.add_mem hp' (U₁.smul_mem ε hp')) hδ (U₂.add_mem hs' hs) h'
    rcases h01 ε with rfl | rfl
    · exact hpp (by simpa using this)
    · exact hp0 (by rw [this, one_smul, add_self])

end Grid

open Grid

theorem mem_of_forall_inf_span_ne_bot {U₁ U₂ ℓ : Submodule (ZMod 2) V} (hU : U₁ ⊓ U₂ = ⊥)
    (hℓ : finrank (ZMod 2) ℓ = 2) {p : V} (hp : p ∈ U₁) {q : Fin 4 → V} (hq : ∀ i, q i ∈ U₂)
    (hqi : Function.Injective q) (hmeet : ∀ i, ℓ ⊓ span (ZMod 2) {p, q i} ≠ ⊥) : p ∈ ℓ := by
  by_contra hpℓ
  have hp0 : p ≠ 0 := fun h => hpℓ (h ▸ ℓ.zero_mem)
  have key : ∀ i, ∃ z ∈ ℓ, z ≠ 0 ∧ (z = q i ∨ z = p + q i) := by
    intro i
    obtain ⟨z, hz, hz0, hzp | hzq | hzpq⟩ := exists_of_inf_span_ne_bot (hmeet i)
    · exact absurd (hzp ▸ hz) hpℓ
    · exact ⟨z, hz, hz0, Or.inl hzq⟩
    · exact ⟨z, hz, hz0, Or.inr hzpq⟩
  choose z hz hz0 hzq using key
  have hpq : ∀ i j, p ≠ q i + q j := fun i j h =>
    hp0 (eq_zero_of_mem_of_mem hU hp (h ▸ U₂.add_mem (hq i) (hq j)))
  have hzi : Function.Injective z := by
    intro i j hij
    rcases hzq i with hi | hi <;> rcases hzq j with hj | hj
    · exact hqi (hi.symm.trans (hij.trans hj))
    · refine absurd ?_ (hpq i j)
      linear_combination (norm := (match_scalars <;> decide))
        (1 : ZMod 2) • hi - (1 : ZMod 2) • hij + (1 : ZMod 2) • hj
    · refine absurd ?_ (hpq i j)
      linear_combination (norm := (match_scalars <;> decide))
        (1 : ZMod 2) • hi - (1 : ZMod 2) • hij + (1 : ZMod 2) • hj
    · refine hqi ?_
      linear_combination (norm := (match_scalars <;> decide))
        (1 : ZMod 2) • hi - (1 : ZMod 2) • hij + (1 : ZMod 2) • hj
  have hne : ∀ i j, i ≠ j → z i ≠ z j := fun i j h e => h (hzi e)
  have h2 := eq_of_mem_line hℓ (hz 0) (hz 1) (hz0 0) (hz0 1) (hne 0 1 (by decide)) (hz 2)
  have h3 := eq_of_mem_line hℓ (hz 0) (hz 1) (hz0 0) (hz0 1) (hne 0 1 (by decide)) (hz 3)
  rcases h2 with h2 | h2 | h2 | h2
  · exact hz0 2 h2
  · exact hne 2 0 (by decide) h2
  · exact hne 2 1 (by decide) h2
  rcases h3 with h3 | h3 | h3 | h3
  · exact hz0 3 h3
  · exact hne 3 0 (by decide) h3
  · exact hne 3 1 (by decide) h3
  · exact hne 2 3 (by decide) (h2.trans h3.symm)

theorem Grid.injective_four {N : Type*} [AddCommGroup N] [Module (ZMod 2) N] {x y : N}
    (hxy : LinearIndependent (ZMod 2) ![x, y]) :
    Function.Injective (![0, x, y, x + y] : Fin 4 → N) := by
  obtain ⟨hx, hy, hne⟩ := linearIndependent_pair_iff.mp hxy
  have h1 : x + y ≠ 0 := fun h => hne (eq_iff_add_eq_zero.mpr h)
  intro i j h
  fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> first
    | exact hx h.symm | exact hy h.symm | exact h1 h.symm | exact hne h | exact hx h
    | exact hy h | exact h1 h | exact hne h.symm

section GridLines

variable {N₁ N₂ : Type*} [AddCommGroup N₁] [Module (ZMod 2) N₁] [AddCommGroup N₂]
  [Module (ZMod 2) N₂] {P₁ : N₁ →ₗ[ZMod 2] V} {P₂ : N₂ →ₗ[ZMod 2] V} {ℓ : Submodule (ZMod 2) V}

theorem mem_of_forall_meet_grid_left (h₂ : Function.Injective P₂)
    (h₁₂ : LinearMap.range P₁ ⊓ LinearMap.range P₂ = ⊥) (hℓ : finrank (ZMod 2) ℓ = 2)
    {W₂ : Submodule (ZMod 2) N₂}
    (hW₂ : ∃ ψ₁ ∈ W₂, ∃ ψ₂ ∈ W₂, LinearIndependent (ZMod 2) ![ψ₁, ψ₂]) (v : N₁) (φ₀ : N₂)
    (hmeet : ∀ ψ ∈ W₂, ℓ ⊓ span (ZMod 2) {P₁ v, P₂ (φ₀ + ψ)} ≠ ⊥) : P₁ v ∈ ℓ := by
  obtain ⟨ψ₁, hψ₁, ψ₂, hψ₂, hψ⟩ := hW₂
  have hmem : ∀ i, (![0, ψ₁, ψ₂, ψ₁ + ψ₂] : Fin 4 → N₂) i ∈ W₂ := by
    intro i
    fin_cases i
    exacts [W₂.zero_mem, hψ₁, hψ₂, W₂.add_mem hψ₁ hψ₂]
  refine mem_of_forall_inf_span_ne_bot h₁₂ hℓ (LinearMap.mem_range_self P₁ v)
    (q := fun i => P₂ (φ₀ + (![0, ψ₁, ψ₂, ψ₁ + ψ₂] : Fin 4 → N₂) i))
    (fun i => LinearMap.mem_range_self P₂ _) (fun i j h => injective_four hψ ?_)
    (fun i => hmeet _ (hmem i))
  exact add_left_cancel (h₂ h)

theorem mem_of_forall_meet_grid_right (h₁ : Function.Injective P₁)
    (h₁₂ : LinearMap.range P₁ ⊓ LinearMap.range P₂ = ⊥) (hℓ : finrank (ZMod 2) ℓ = 2)
    {W₁ : Submodule (ZMod 2) N₁}
    (hW₁ : ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₁, LinearIndependent (ZMod 2) ![w₁, w₂]) (φ : N₂) (v₀ : N₁)
    (hmeet : ∀ w ∈ W₁, ℓ ⊓ span (ZMod 2) {P₁ (v₀ + w), P₂ φ} ≠ ⊥) : P₂ φ ∈ ℓ := by
  refine mem_of_forall_meet_grid_left (P₁ := P₂) (P₂ := P₁) h₁ (by rwa [inf_comm]) hℓ hW₁ φ v₀
    fun w hw => ?_
  rw [Set.pair_comm]
  exact hmeet w hw

theorem Grid.map_ne_zero_of_injective {N : Type*} [AddCommGroup N] [Module (ZMod 2) N]
    {P : N →ₗ[ZMod 2] V} (hP : Function.Injective P) {x : N} (hx : x ≠ 0) : P x ≠ 0 :=
  fun h => hx (hP (h.trans (map_zero _).symm))

theorem Grid.map_add_add_map {N : Type*} [AddCommGroup N] [Module (ZMod 2) N]
    (P : N →ₗ[ZMod 2] V) (v w : N) : P (v + w) + P v = P w := by
  rw [map_add, add_comm (P v), add_assoc, add_self, add_zero]

theorem false_of_forall_meet_grid (h₁ : Function.Injective P₁) (h₂ : Function.Injective P₂)
    (h₁₂ : LinearMap.range P₁ ⊓ LinearMap.range P₂ = ⊥) (hℓ : finrank (ZMod 2) ℓ = 2)
    {W₁ : Submodule (ZMod 2) N₁} {W₂ : Submodule (ZMod 2) N₂}
    (hW₁ : ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₁, LinearIndependent (ZMod 2) ![w₁, w₂])
    (hW₂ : ∃ ψ₁ ∈ W₂, ∃ ψ₂ ∈ W₂, LinearIndependent (ZMod 2) ![ψ₁, ψ₂]) (v₀ : N₁) (φ₀ : N₂)
    (hmeet : ∀ w ∈ W₁, ∀ ψ ∈ W₂, ℓ ⊓ span (ZMod 2) {P₁ (v₀ + w), P₂ (φ₀ + ψ)} ≠ ⊥) : False := by
  obtain ⟨w₁, hw₁, w₂, hw₂, hw⟩ := id hW₁
  obtain ⟨ψ₁, hψ₁, ψ₂, -, hψ⟩ := id hW₂
  obtain ⟨hw₁0, hw₂0, hw₁₂⟩ := linearIndependent_pair_iff.mp hw
  obtain ⟨hψ₁0, -, -⟩ := linearIndependent_pair_iff.mp hψ
  have hA : ∀ w ∈ W₁, P₁ (v₀ + w) ∈ ℓ := fun w hw =>
    mem_of_forall_meet_grid_left h₂ h₁₂ hℓ hW₂ (v₀ + w) φ₀ (hmeet w hw)
  have hB : ∀ ψ ∈ W₂, P₂ (φ₀ + ψ) ∈ ℓ := fun ψ hψ =>
    mem_of_forall_meet_grid_right h₁ h₁₂ hℓ hW₁ (φ₀ + ψ) v₀ fun w hw => hmeet w hw ψ hψ
  have hP₁ : ∀ w ∈ W₁, P₁ w ∈ ℓ := fun w hw => by
    rw [← map_add_add_map P₁ v₀ w]
    exact ℓ.add_mem (hA w hw) (by simpa using hA 0 W₁.zero_mem)
  have hc : P₂ ψ₁ ∈ ℓ := by
    rw [← map_add_add_map P₂ φ₀ ψ₁]
    exact ℓ.add_mem (hB ψ₁ hψ₁) (by simpa using hB 0 W₂.zero_mem)
  have hc0 : P₂ ψ₁ ≠ 0 := map_ne_zero_of_injective h₂ hψ₁0
  have hcP₁ : ∀ x ∈ LinearMap.range P₁, P₂ ψ₁ ≠ x := fun x hx h =>
    hc0 (eq_zero_of_mem_of_mem h₁₂ (h ▸ hx) (LinearMap.mem_range_self P₂ ψ₁))
  rcases eq_of_mem_line hℓ (hP₁ w₁ hw₁) (hP₁ w₂ hw₂) (map_ne_zero_of_injective h₁ hw₁0)
    (map_ne_zero_of_injective h₁ hw₂0)
    (fun h => hw₁₂ (h₁ h)) hc with h | h | h | h
  · exact hc0 h
  · exact hcP₁ _ (LinearMap.mem_range_self P₁ w₁) h
  · exact hcP₁ _ (LinearMap.mem_range_self P₁ w₂) h
  · exact hcP₁ _ (Submodule.add_mem _ (LinearMap.mem_range_self P₁ w₁)
      (LinearMap.mem_range_self P₁ w₂)) h

theorem eq_span_of_forall_meet_grid_left (h₁ : Function.Injective P₁)
    (h₂ : Function.Injective P₂) (h₁₂ : LinearMap.range P₁ ⊓ LinearMap.range P₂ = ⊥)
    (hℓ : finrank (ZMod 2) ℓ = 2) {v₀ w₁ : N₁} (hv : LinearIndependent (ZMod 2) ![v₀, w₁])
    {W₂ : Submodule (ZMod 2) N₂}
    (hW₂ : ∃ ψ₁ ∈ W₂, ∃ ψ₂ ∈ W₂, LinearIndependent (ZMod 2) ![ψ₁, ψ₂]) (φ₀ : N₂)
    (hmeet : ∀ w ∈ (ZMod 2) ∙ w₁, ∀ ψ ∈ W₂,
      ℓ ⊓ span (ZMod 2) {P₁ (v₀ + w), P₂ (φ₀ + ψ)} ≠ ⊥) :
    ℓ = span (ZMod 2) {P₁ v₀, P₁ w₁} := by
  obtain ⟨hv0, hw0, hvw⟩ := linearIndependent_pair_iff.mp hv
  have hA : ∀ w ∈ (ZMod 2) ∙ w₁, P₁ (v₀ + w) ∈ ℓ := fun w hw =>
    mem_of_forall_meet_grid_left h₂ h₁₂ hℓ hW₂ (v₀ + w) φ₀ (hmeet w hw)
  have h0 : P₁ v₀ ∈ ℓ := by simpa using hA 0 (Submodule.zero_mem _)
  have h1 : P₁ w₁ ∈ ℓ := by
    rw [← map_add_add_map P₁ v₀ w₁]
    exact ℓ.add_mem (hA w₁ (Submodule.mem_span_singleton_self w₁)) h0
  refine eq_span_of_mem hℓ h0 h1 (fun h => hv0 (h₁ (h.trans (map_zero _).symm)))
    (fun h => hw0 (h₁ (h.trans (map_zero _).symm))) fun h => hvw (h₁ h)

theorem eq_span_of_forall_meet_grid_right (h₁ : Function.Injective P₁)
    (h₂ : Function.Injective P₂) (h₁₂ : LinearMap.range P₁ ⊓ LinearMap.range P₂ = ⊥)
    (hℓ : finrank (ZMod 2) ℓ = 2) {φ₀ ψ₁ : N₂} (hφ : LinearIndependent (ZMod 2) ![φ₀, ψ₁])
    {W₁ : Submodule (ZMod 2) N₁}
    (hW₁ : ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₁, LinearIndependent (ZMod 2) ![w₁, w₂]) (v₀ : N₁)
    (hmeet : ∀ w ∈ W₁, ∀ ψ ∈ (ZMod 2) ∙ ψ₁,
      ℓ ⊓ span (ZMod 2) {P₁ (v₀ + w), P₂ (φ₀ + ψ)} ≠ ⊥) :
    ℓ = span (ZMod 2) {P₂ φ₀, P₂ ψ₁} := by
  refine eq_span_of_forall_meet_grid_left (P₁ := P₂) (P₂ := P₁) h₂ h₁ (by rwa [inf_comm]) hℓ hφ
    hW₁ v₀ fun ψ hψ w hw => ?_
  rw [Set.pair_comm]
  exact hmeet w hw ψ hψ

theorem eq_span_or_eq_span_of_forall_meet_grid (h₁ : Function.Injective P₁)
    (h₂ : Function.Injective P₂) (h₁₂ : LinearMap.range P₁ ⊓ LinearMap.range P₂ = ⊥)
    (hℓ : finrank (ZMod 2) ℓ = 2) {v₀ w₁ : N₁} (hv : LinearIndependent (ZMod 2) ![v₀, w₁])
    {φ₀ ψ₁ : N₂} (hφ : LinearIndependent (ZMod 2) ![φ₀, ψ₁])
    (hmeet : ∀ w ∈ (ZMod 2) ∙ w₁, ∀ ψ ∈ (ZMod 2) ∙ ψ₁,
      ℓ ⊓ span (ZMod 2) {P₁ (v₀ + w), P₂ (φ₀ + ψ)} ≠ ⊥) :
    ℓ = span (ZMod 2) {P₁ v₀, P₁ w₁} ∨ ℓ = span (ZMod 2) {P₂ φ₀, P₂ ψ₁} := by
  obtain ⟨hv0, hw0, hvw⟩ := linearIndependent_pair_iff.mp hv
  obtain ⟨hφ0, hψ0, hφψ⟩ := linearIndependent_pair_iff.mp hφ
  have hvw' : v₀ + w₁ ≠ 0 := fun h => hvw (eq_iff_add_eq_zero.mpr h)
  have hφψ' : φ₀ + ψ₁ ≠ 0 := fun h => hφψ (eq_iff_add_eq_zero.mpr h)
  have hne₁ : P₁ v₀ ≠ P₁ (v₀ + w₁) := fun h => hw0 (by simpa using h₁ h)
  have hne₂ : P₂ φ₀ ≠ P₂ (φ₀ + ψ₁) := fun h => hψ0 (by simpa using h₂ h)
  have hw : w₁ ∈ (ZMod 2) ∙ w₁ := Submodule.mem_span_singleton_self w₁
  have hψ : ψ₁ ∈ (ZMod 2) ∙ ψ₁ := Submodule.mem_span_singleton_self ψ₁
  have m00 := hmeet 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _)
  have m01 := hmeet 0 (Submodule.zero_mem _) ψ₁ hψ
  have m10 := hmeet w₁ hw 0 (Submodule.zero_mem _)
  have m11 := hmeet w₁ hw ψ₁ hψ
  simp only [add_zero] at m00 m01 m10 m11
  have r₁ := LinearMap.mem_range_self P₁
  have r₂ := LinearMap.mem_range_self P₂
  have n₁ : ∀ {x : N₁}, x ≠ 0 → P₁ x ≠ 0 := map_ne_zero_of_injective h₁
  have n₂ : ∀ {x : N₂}, x ≠ 0 → P₂ x ≠ 0 := map_ne_zero_of_injective h₂
  by_cases ha : P₁ v₀ ∈ ℓ ∧ P₁ (v₀ + w₁) ∈ ℓ
  · left
    have h1 : P₁ w₁ ∈ ℓ := by
      rw [← map_add_add_map P₁ v₀ w₁]
      exact ℓ.add_mem ha.2 ha.1
    exact eq_span_of_mem hℓ ha.1 h1 (n₁ hv0) (n₁ hw0) fun h => hvw (h₁ h)
  by_cases hb : P₂ φ₀ ∈ ℓ ∧ P₂ (φ₀ + ψ₁) ∈ ℓ
  · right
    have h1 : P₂ ψ₁ ∈ ℓ := by
      rw [← map_add_add_map P₂ φ₀ ψ₁]
      exact ℓ.add_mem hb.2 hb.1
    exact eq_span_of_mem hℓ hb.1 h1 (n₂ hφ0) (n₂ hψ0) fun h => hφψ (h₂ h)
  exfalso
  rw [not_and_or] at ha hb
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact false_of_meet_three h₁₂ hℓ (r₁ _) (r₁ v₀) (r₂ _) (r₂ φ₀) (n₁ hvw') hne₁.symm
      hne₂.symm ha hb m00 m01 m10
  · exact false_of_meet_three h₁₂ hℓ (r₁ _) (r₁ v₀) (r₂ φ₀) (r₂ _) (n₁ hvw') hne₁.symm hne₂
      ha hb m01 m00 m11
  · exact false_of_meet_three h₁₂ hℓ (r₁ v₀) (r₁ _) (r₂ _) (r₂ φ₀) (n₁ hv0) hne₁ hne₂.symm
      ha hb m10 m11 m00
  · exact false_of_meet_three h₁₂ hℓ (r₁ v₀) (r₁ _) (r₂ φ₀) (r₂ _) (n₁ hv0) hne₁ hne₂ ha hb
      m11 m10 m01

theorem le_sup_range_of_forall_meet_grid (h₁ : Function.Injective P₁)
    (h₂ : Function.Injective P₂) (h₁₂ : LinearMap.range P₁ ⊓ LinearMap.range P₂ = ⊥)
    (hℓ : finrank (ZMod 2) ℓ = 2) {v₀ w₁ : N₁} (hv : LinearIndependent (ZMod 2) ![v₀, w₁])
    {φ₀ ψ₁ : N₂} (hφ : LinearIndependent (ZMod 2) ![φ₀, ψ₁])
    (hmeet : ∀ w ∈ (ZMod 2) ∙ w₁, ∀ ψ ∈ (ZMod 2) ∙ ψ₁,
      ℓ ⊓ span (ZMod 2) {P₁ (v₀ + w), P₂ (φ₀ + ψ)} ≠ ⊥) :
    ℓ ≤ LinearMap.range P₁ ⊔ LinearMap.range P₂ := by
  rcases eq_span_or_eq_span_of_forall_meet_grid h₁ h₂ h₁₂ hℓ hv hφ hmeet with h | h <;>
    rw [h, Submodule.span_le] <;> rintro x (rfl | rfl)
  · exact Submodule.mem_sup_left (LinearMap.mem_range_self P₁ _)
  · exact Submodule.mem_sup_left (LinearMap.mem_range_self P₁ _)
  · exact Submodule.mem_sup_right (LinearMap.mem_range_self P₂ _)
  · exact Submodule.mem_sup_right (LinearMap.mem_range_self P₂ _)

end GridLines

end CFSG.LargeExtraspecial.A2Mod
