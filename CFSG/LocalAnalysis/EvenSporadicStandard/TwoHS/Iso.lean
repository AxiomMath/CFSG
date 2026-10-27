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

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup

section Index

variable {H : Type*} [Group H] {E : Subgroup H}

theorem mul_inv_mem_of_index_eq_two (hi : E.index = 2) {x a : H} (hx : x ∉ E) (ha : a ∉ E) :
    x * a⁻¹ ∈ E := by
  obtain ⟨b, hb⟩ := Subgroup.index_eq_two_iff.1 hi
  have hxb : x * b ∈ E := by
    rcases hb x with h | h
    · exact h.1
    · exact absurd h.1 hx
  have hab : a * b ∈ E := by
    rcases hb a with h | h
    · exact h.1
    · exact absurd h.1 ha
  have := E.mul_mem hxb (E.inv_mem hab)
  simpa [mul_assoc] using this

end Index

section Action

variable {H : Type*} [Group H] {E : Subgroup H} [E.Normal]

theorem ker_conjNormal : (MulAut.conjNormal : H →* MulAut E).ker = centralizer (E : Set H) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
  constructor
  · intro h x hx
    have := congrArg (fun α : MulAut E => (α ⟨x, hx⟩ : H)) h
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
    calc x * g = (g * x * g⁻¹) * g := by rw [this]
      _ = g * x := by group
  · intro h
    ext x
    simp only [MulAut.conjNormal_apply, MulAut.one_apply]
    calc g * x * g⁻¹ = (x * g) * g⁻¹ := by rw [h x x.2]
      _ = x := by group

theorem conjNormal_surjective_of_card_le [Finite H]
    (h : Nat.card (MulAut E) * Nat.card (centralizer (E : Set H)) ≤ Nat.card H) :
    Function.Surjective (MulAut.conjNormal : H →* MulAut E) := by
  have hfin : Finite E := inferInstance
  have hfa : Finite (MulAut E) := inferInstance
  have hcard := Subgroup.card_ker_mul_card_range (MulAut.conjNormal : H →* MulAut E)
  rw [ker_conjNormal] at hcard
  have hpos : 0 < Nat.card (centralizer (E : Set H)) := Nat.card_pos
  have hle : Nat.card (MulAut E) ≤ Nat.card (MulAut.conjNormal : H →* MulAut E).range := by
    refine Nat.le_of_mul_le_mul_left ?_ hpos
    rw [hcard, mul_comm]
    exact h
  have heq : (MulAut.conjNormal : H →* MulAut E).range = ⊤ :=
    Subgroup.eq_top_of_le_card _ hle
  exact MonoidHom.range_eq_top.1 heq

end Action

section Iso

variable {H₁ H₂ : Type*} [Group H₁] [Group H₂] {E₁ : Subgroup H₁} {E₂ : Subgroup H₂}
  [E₁.Normal] [E₂.Normal]

theorem exists_mulEquiv_of_outer_involution (hi₁ : E₁.index = 2) (hi₂ : E₂.index = 2)
    (hc₁ : centralizer (E₁ : Set H₁) ≤ E₁) (φ : E₁ ≃* E₂)
    (hsurj : Function.Surjective (MulAut.conjNormal : H₂ →* MulAut E₂))
    {v : H₁} (hv : v ∉ E₁) (hv2 : v ^ 2 = 1)
    (hsign : ∀ g : H₂, g ∉ E₂ → g ^ 2 ∈ centralizer (E₂ : Set H₂) → g ^ 2 = 1) :
    Nonempty (H₁ ≃* H₂) := by
  classical
  let c : MulAut E₁ := MulAut.conjNormal v
  let α : MulAut E₂ := φ.symm.trans (c.trans φ)
  obtain ⟨g, hg⟩ := hsurj α
  have hcv : ∀ x : E₁, ((c x : E₁) : H₁) = v * x * v⁻¹ := fun x => MulAut.conjNormal_apply v x
  have hgα : ∀ x : E₁, g * ((φ x : E₂) : H₂) * g⁻¹ = ((φ (c x) : E₂) : H₂) := by
    intro x
    have h1 := congrArg (fun β : MulAut E₂ => ((β (φ x) : E₂) : H₂)) hg
    simp only [MulAut.conjNormal_apply] at h1
    rw [h1]
    simp [α]
  have hcc : ∀ x : E₁, c (c x) = x := by
    intro x
    apply Subtype.ext
    rw [hcv, hcv]
    calc v * (v * (x : H₁) * v⁻¹) * v⁻¹ = (v * v) * x * (v * v)⁻¹ := by group
      _ = x := by rw [← pow_two, hv2]; group
  have hgE : g ∉ E₂ := by
    intro hgE
    set e : E₁ := φ.symm ⟨g, hgE⟩ with he_def
    have hφe : ((φ e : E₂) : H₂) = g := by rw [he_def, MulEquiv.apply_symm_apply]
    have he : ∀ x : E₁, v * (x : H₁) * v⁻¹ = (e : H₁) * x * (e : H₁)⁻¹ := by
      intro x
      have h2 : φ (c x) = φ (e * x * e⁻¹) := by
        apply Subtype.ext
        have h3 := hgα x
        rw [← h3]
        simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hφe]
      have h4 := φ.injective h2
      rw [← hcv x, h4]
      simp
    have hcent : (e : H₁)⁻¹ * v ∈ centralizer (E₁ : Set H₁) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h5 := he ⟨x, hx⟩
      calc x * ((e : H₁)⁻¹ * v) = (e : H₁)⁻¹ * ((e : H₁) * x * (e : H₁)⁻¹) * v := by group
        _ = (e : H₁)⁻¹ * (v * x * v⁻¹) * v := by rw [← h5]
        _ = (e : H₁)⁻¹ * v * x := by group
    have h6 : (e : H₁)⁻¹ * v ∈ E₁ := hc₁ hcent
    have h7 : (e : H₁) * ((e : H₁)⁻¹ * v) ∈ E₁ := E₁.mul_mem e.2 h6
    exact hv (by simpa using h7)
  have hg2c : g ^ 2 ∈ centralizer (E₂ : Set H₂) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨x, hx⟩ := φ.surjective ⟨y, hy⟩
    have hxy : ((φ x : E₂) : H₂) = y := congrArg Subtype.val hx
    have key : g * (g * y * g⁻¹) * g⁻¹ = y := by
      have h1 := hgα (c x)
      rw [hcc x, hxy] at h1
      have h2 := hgα x
      rw [hxy] at h2
      rw [h2, h1]
    calc y * g ^ 2 = (g * (g * y * g⁻¹) * g⁻¹) * g ^ 2 := by rw [key]
      _ = g ^ 2 * y := by rw [pow_two]; group
  have hg2 : g ^ 2 = 1 := hsign g hgE hg2c
  have hgg : g * g = 1 := by rw [← pow_two]; exact hg2
  let Φ : H₁ → H₂ := fun x => if hx : x ∈ E₁ then ((φ ⟨x, hx⟩ : E₂) : H₂) else 1
  have hΦ : ∀ x : E₁, Φ x = ((φ x : E₂) : H₂) := fun x => by simp [Φ]
  have hΦmul : ∀ a b : H₁, a ∈ E₁ → b ∈ E₁ → Φ (a * b) = Φ a * Φ b := by
    intro a b ha hb
    have := hΦ (⟨a, ha⟩ * ⟨b, hb⟩ : E₁)
    simp only [Subgroup.coe_mul] at this
    rw [this, map_mul, Subgroup.coe_mul, hΦ ⟨a, ha⟩, hΦ ⟨b, hb⟩]
  have hΦconj : ∀ y : H₁, y ∈ E₁ → Φ (v * y * v⁻¹) = g * Φ y * g⁻¹ := by
    intro y hy
    have h2 : v * y * v⁻¹ = ((c ⟨y, hy⟩ : E₁) : H₁) := (hcv ⟨y, hy⟩).symm
    rw [h2, hΦ (c ⟨y, hy⟩), ← hgα ⟨y, hy⟩, ← hΦ ⟨y, hy⟩]
  have hxv : ∀ {x : H₁}, x ∉ E₁ → x * v⁻¹ ∈ E₁ := fun hx => mul_inv_mem_of_index_eq_two hi₁ hx hv
  let ψ : H₁ → H₂ := fun x => if x ∈ E₁ then Φ x else Φ (x * v⁻¹) * g
  have hψin : ∀ {x : H₁}, x ∈ E₁ → ψ x = Φ x := fun hx => by simp [ψ, hx]
  have hψout : ∀ {x : H₁}, x ∉ E₁ → ψ x = Φ (x * v⁻¹) * g := fun hx => by simp [ψ, hx]
  have hmul : ∀ x y : H₁, ψ (x * y) = ψ x * ψ y := by
    intro x y
    by_cases hx : x ∈ E₁ <;> by_cases hy : y ∈ E₁
    · rw [hψin hx, hψin hy, hψin (E₁.mul_mem hx hy), hΦmul x y hx hy]
    · have hxy : x * y ∉ E₁ := fun h => hy (by simpa using E₁.mul_mem (E₁.inv_mem hx) h)
      rw [hψin hx, hψout hy, hψout hxy, mul_assoc x y v⁻¹, hΦmul x (y * v⁻¹) hx (hxv hy),
        mul_assoc]
    · have hxy : x * y ∉ E₁ := fun h => hx (by simpa using E₁.mul_mem h (E₁.inv_mem hy))
      have hdec : x * y * v⁻¹ = (x * v⁻¹) * (v * y * v⁻¹) := by group
      rw [hψout hx, hψin hy, hψout hxy, hdec, hΦmul _ _ (hxv hx)
        (Subgroup.Normal.conj_mem inferInstance y hy v), hΦconj y hy]
      exact (by group : Φ (x * v⁻¹) * (g * Φ y * g⁻¹) * g = Φ (x * v⁻¹) * g * Φ y)
    · have hxy : x * y ∈ E₁ := by
        have := mul_inv_mem_of_index_eq_two hi₁ hx (a := y⁻¹) (fun h => hy (by simpa using h))
        simpa using this
      have hdec : x * y = (x * v⁻¹) * (v * (y * v⁻¹) * v⁻¹) := by
        have hvv : v⁻¹ * v⁻¹ = 1 := by
          have : (v * v)⁻¹ = 1 := by rw [← pow_two, hv2, inv_one]
          simpa [mul_inv_rev] using this
        calc x * y = x * (v⁻¹ * v) * y := by group
          _ = (x * v⁻¹) * (v * (y * v⁻¹) * v⁻¹) * (v * v) := by group
          _ = (x * v⁻¹) * (v * (y * v⁻¹) * v⁻¹) := by rw [← pow_two, hv2, mul_one]
      rw [hψout hx, hψout hy, hψin hxy, hdec, hΦmul _ _ (hxv hx)
        (Subgroup.Normal.conj_mem inferInstance _ (hxv hy) v), hΦconj _ (hxv hy)]
      have hgi : g⁻¹ = g := inv_eq_of_mul_eq_one_right hgg
      rw [hgi]
      exact (by group : Φ (x * v⁻¹) * (g * Φ (y * v⁻¹) * g) = Φ (x * v⁻¹) * g * (Φ (y * v⁻¹) * g))
  have hψ1 : ψ 1 = 1 := by
    rw [hψin (one_mem E₁)]
    simpa using hΦ 1
  let ψ' : H₁ →* H₂ := MonoidHom.mk' ψ hmul
  have hinj : Function.Injective ψ' := by
    rw [injective_iff_map_eq_one]
    intro x hx1
    change ψ x = 1 at hx1
    by_cases hx : x ∈ E₁
    · rw [hψin hx, hΦ ⟨x, hx⟩] at hx1
      have h1 : φ ⟨x, hx⟩ = 1 := Subtype.ext hx1
      have h2 : (⟨x, hx⟩ : E₁) = 1 := φ.injective (h1.trans (map_one φ).symm)
      simpa using congrArg Subtype.val h2
    · exfalso
      rw [hψout hx] at hx1
      have hm : Φ (x * v⁻¹) ∈ E₂ := by
        rw [hΦ ⟨x * v⁻¹, hxv hx⟩]; exact (φ _).2
      have : g = (Φ (x * v⁻¹))⁻¹ := eq_inv_of_mul_eq_one_right hx1
      exact hgE (this ▸ E₂.inv_mem hm)
  have hsurj' : Function.Surjective ψ' := by
    intro z
    by_cases hz : z ∈ E₂
    · obtain ⟨w, hw⟩ := φ.surjective ⟨z, hz⟩
      refine ⟨w, ?_⟩
      change ψ w = z
      rw [hψin w.2, hΦ w, hw]
    · have hzg : z * g⁻¹ ∈ E₂ := mul_inv_mem_of_index_eq_two hi₂ hz hgE
      obtain ⟨w, hw⟩ := φ.surjective ⟨z * g⁻¹, hzg⟩
      have hwv : (w : H₁) * v ∉ E₁ := fun h => hv (by simpa using E₁.mul_mem (E₁.inv_mem w.2) h)
      refine ⟨(w : H₁) * v, ?_⟩
      change ψ ((w : H₁) * v) = z
      rw [hψout hwv, mul_inv_cancel_right, hΦ w, hw]
      simp
  exact ⟨MulEquiv.ofBijective ψ' ⟨hinj, hsurj'⟩⟩

end Iso

end CFSG.EvenSporadicStandard.TwoHS
