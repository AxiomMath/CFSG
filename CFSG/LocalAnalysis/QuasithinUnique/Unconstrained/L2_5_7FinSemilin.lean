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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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

namespace CFSG.QuasithinUnique.Fin257

namespace Semilin

variable {F : Type} [Field F]

@[expose] def FixSet (σ : F ≃+* F) : Set F := {x | σ x = x}

theorem mem_fixSet {σ : F ≃+* F} {x : F} : x ∈ FixSet σ ↔ σ x = x := Iff.rfl

theorem card_fixSet_sq_le [Finite F] (σ : F ≃+* F) (hσ : σ ≠ 1) :
    Nat.card (FixSet σ) ^ 2 ≤ Nat.card F := by
  obtain ⟨x₀, hx₀⟩ : ∃ x : F, σ x ≠ x := by
    by_contra h
    push Not at h
    exact hσ (RingEquiv.ext h)
  have hinj : Function.Injective (fun p : FixSet σ × FixSet σ => (p.1 : F) + (p.2 : F) * x₀) := by
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ h
    simp only at h
    have hb2 : b = b' := by
      by_contra hne
      have h1 : (b - b') * x₀ = a' - a := by linear_combination h
      have h2 : σ ((b - b') * x₀) = (b - b') * x₀ := by
        rw [h1, map_sub, ha, ha']
      rw [map_mul, map_sub, hb, hb'] at h2
      have h3 : (b - b') * (σ x₀ - x₀) = 0 := by linear_combination h2
      rcases mul_eq_zero.mp h3 with h4 | h4
      · exact hne (sub_eq_zero.mp h4)
      · exact hx₀ (sub_eq_zero.mp h4)
    subst hb2
    have : a = a' := by linear_combination h
    subst this
    rfl
  calc Nat.card (FixSet σ) ^ 2 = Nat.card (FixSet σ × FixSet σ) := by
        rw [Nat.card_prod, sq]
    _ ≤ Nat.card F := Nat.card_le_card_of_injective _ hinj

@[expose] def InS (σ : F ≃+* F) (m₁₁ m₁₂ m₂₁ m₂₂ : F) (v : F × F) : Prop :=
  σ v.1 = m₁₁ * v.1 + m₁₂ * v.2 ∧ σ v.2 = m₂₁ * v.1 + m₂₂ * v.2

theorem inS_relation {σ : F ≃+* F} {m₁₁ m₁₂ m₂₁ m₂₂ : F} {u₁ u₂ u₃ : F × F}
    (h₁ : InS σ m₁₁ m₁₂ m₂₁ m₂₂ u₁) (h₂ : InS σ m₁₁ m₁₂ m₂₁ m₂₂ u₂)
    (h₃ : InS σ m₁₁ m₁₂ m₂₁ m₂₂ u₃) {c₁ c₂ c₃ : F}
    (e1 : c₁ * u₁.1 + c₂ * u₂.1 + c₃ * u₃.1 = 0) (e2 : c₁ * u₁.2 + c₂ * u₂.2 + c₃ * u₃.2 = 0) :
    σ.symm c₁ * u₁.1 + σ.symm c₂ * u₂.1 + σ.symm c₃ * u₃.1 = 0 ∧
      σ.symm c₁ * u₁.2 + σ.symm c₂ * u₂.2 + σ.symm c₃ * u₃.2 = 0 := by
  obtain ⟨a₁, b₁⟩ := h₁
  obtain ⟨a₂, b₂⟩ := h₂
  obtain ⟨a₃, b₃⟩ := h₃
  have f1 : c₁ * σ u₁.1 + c₂ * σ u₂.1 + c₃ * σ u₃.1 = 0 := by
    rw [a₁, a₂, a₃]
    linear_combination m₁₁ * e1 + m₁₂ * e2
  have f2 : c₁ * σ u₁.2 + c₂ * σ u₂.2 + c₃ * σ u₃.2 = 0 := by
    rw [b₁, b₂, b₃]
    linear_combination m₂₁ * e1 + m₂₂ * e2
  constructor
  · have := congrArg σ.symm f1
    simpa using this
  · have := congrArg σ.symm f2
    simpa using this

theorem inS_zero (σ : F ≃+* F) (m₁₁ m₁₂ m₂₁ m₂₂ : F) : InS σ m₁₁ m₁₂ m₂₁ m₂₂ (0, 0) := by
  simp [InS]

theorem ne_zero_coord {v : F × F} (hv : v ≠ 0) : v.1 ≠ 0 ∨ v.2 ≠ 0 := by
  by_contra h
  push Not at h
  exact hv (Prod.ext h.1 h.2)

theorem inS_indep {σ : F ≃+* F} {m₁₁ m₁₂ m₂₁ m₂₂ : F} {v₁ v₂ : F × F}
    (h₁ : InS σ m₁₁ m₁₂ m₂₁ m₂₂ v₁) (h₂ : InS σ m₁₁ m₁₂ m₂₁ m₂₂ v₂) (hv₁ : v₁ ≠ 0)
    (hn : ∀ t ∈ FixSet σ, v₂ ≠ (t * v₁.1, t * v₁.2)) {d₁ d₂ : F}
    (e1 : d₁ * v₁.1 + d₂ * v₂.1 = 0) (e2 : d₁ * v₁.2 + d₂ * v₂.2 = 0) : d₁ = 0 ∧ d₂ = 0 := by
  have hd₂ : d₂ = 0 := by
    by_contra hd₂
    set c : F := -d₁ / d₂ with hc
    have hv₂1 : v₂.1 = c * v₁.1 := by
      rw [hc]; field_simp; linear_combination e1
    have hv₂2 : v₂.2 = c * v₁.2 := by
      rw [hc]; field_simp; linear_combination e2
    have hrel := inS_relation h₂ h₁ (inS_zero σ m₁₁ m₁₂ m₂₁ m₂₂) (c₁ := 1) (c₂ := -c) (c₃ := 0)
      (by simp [hv₂1]) (by simp [hv₂2])
    simp only [map_one, map_neg, one_mul, map_zero, zero_mul, add_zero] at hrel
    obtain ⟨r1, r2⟩ := hrel
    have hcc : σ.symm c = c := by
      rcases ne_zero_coord hv₁ with h | h
      · have : (c - σ.symm c) * v₁.1 = 0 := by linear_combination r1 - hv₂1
        have := (mul_eq_zero.mp this).resolve_right h
        linear_combination -this
      · have : (c - σ.symm c) * v₁.2 = 0 := by linear_combination r2 - hv₂2
        have := (mul_eq_zero.mp this).resolve_right h
        linear_combination -this
    refine hn c ?_ (Prod.ext hv₂1 hv₂2)
    rw [mem_fixSet]
    have h := congrArg σ hcc
    rw [RingEquiv.apply_symm_apply] at h
    exact h.symm
  subst hd₂
  refine ⟨?_, rfl⟩
  rcases ne_zero_coord hv₁ with h | h
  · simpa [h] using e1
  · simpa [h] using e2

theorem card_inS_le [Finite F] (σ : F ≃+* F) (m₁₁ m₁₂ m₂₁ m₂₂ : F) :
    Nat.card {v : F × F | InS σ m₁₁ m₁₂ m₂₁ m₂₂ v} ≤ Nat.card (FixSet σ) ^ 2 := by
  classical
  have hLpos : 0 < Nat.card (FixSet σ) := by
    have : Finite (FixSet σ) := inferInstance
    exact Nat.card_pos_iff.mpr ⟨⟨⟨0, by simp [FixSet]⟩⟩, inferInstance⟩
  set S : Set (F × F) := {v : F × F | InS σ m₁₁ m₁₂ m₂₁ m₂₂ v} with hS
  by_cases hS0 : ∀ v ∈ S, v = 0
  · have : S ⊆ {(0, 0)} := fun v hv => by
      rw [Set.mem_singleton_iff, hS0 v hv]
      rfl
    calc Nat.card S ≤ Nat.card ({(0, 0)} : Set (F × F)) := Nat.card_mono (Set.finite_singleton _) this
      _ = 1 := by simp
      _ ≤ Nat.card (FixSet σ) ^ 2 := Nat.one_le_pow _ _ hLpos
  · push Not at hS0
    obtain ⟨v₁, hv₁S, hv₁0⟩ := hS0
    have hv₁ : InS σ m₁₁ m₁₂ m₂₁ m₂₂ v₁ := hv₁S
    let T₁ : Set (F × F) := (fun t : FixSet σ => ((t : F) * v₁.1, (t : F) * v₁.2)) '' Set.univ
    have hT₁card : Nat.card T₁ ≤ Nat.card (FixSet σ) := by
      calc Nat.card T₁ ≤ Nat.card (Set.univ : Set (FixSet σ)) :=
            Nat.card_image_le Set.finite_univ
        _ = Nat.card (FixSet σ) := by simp
    by_cases hS1 : ∀ v ∈ S, ∃ t ∈ FixSet σ, v = ((t : F) * v₁.1, (t : F) * v₁.2)
    · have : S ⊆ T₁ := fun v hv => by
        obtain ⟨t, ht, rfl⟩ := hS1 v hv
        exact ⟨⟨t, ht⟩, Set.mem_univ _, rfl⟩
      calc Nat.card S ≤ Nat.card T₁ := Nat.card_mono (Set.toFinite _) this
        _ ≤ Nat.card (FixSet σ) := hT₁card
        _ ≤ Nat.card (FixSet σ) ^ 2 := by
          rw [sq]
          exact Nat.le_mul_of_pos_left _ hLpos
    · push Not at hS1
      obtain ⟨v₂, hv₂S, hv₂n⟩ := hS1
      have hv₂ : InS σ m₁₁ m₁₂ m₂₁ m₂₂ v₂ := hv₂S
      have hindep : ∀ d₁ d₂ : F, d₁ * v₁.1 + d₂ * v₂.1 = 0 → d₁ * v₁.2 + d₂ * v₂.2 = 0 →
          d₁ = 0 ∧ d₂ = 0 := fun d₁ d₂ e1 e2 =>
        inS_indep hv₁ hv₂ hv₁0 (fun t ht h => hv₂n t ht h) e1 e2
      have hdet : v₁.1 * v₂.2 - v₁.2 * v₂.1 ≠ 0 := by
        intro hd
        have h1 := hindep v₂.2 (-v₁.2) (by linear_combination hd) (by ring)
        have h2 := hindep v₂.1 (-v₁.1) (by ring) (by linear_combination -hd)
        exact hv₁0 (Prod.ext (neg_eq_zero.mp h2.2) (neg_eq_zero.mp h1.2))
      have hspan : ∀ v : F × F, ∃ x y : F, v.1 = x * v₁.1 + y * v₂.1 ∧ v.2 = x * v₁.2 + y * v₂.2 := by
        intro v
        have hdd : (v₁.1 * v₂.2 - v₁.2 * v₂.1) * (v₁.1 * v₂.2 - v₁.2 * v₂.1)⁻¹ = 1 :=
          mul_inv_cancel₀ hdet
        refine ⟨(v.1 * v₂.2 - v.2 * v₂.1) * (v₁.1 * v₂.2 - v₁.2 * v₂.1)⁻¹,
          (v₁.1 * v.2 - v₁.2 * v.1) * (v₁.1 * v₂.2 - v₁.2 * v₂.1)⁻¹, ?_, ?_⟩
        · linear_combination (-v.1) * hdd
        · linear_combination (-v.2) * hdd
      have hcoef : ∀ v ∈ S, ∃ x y : F, x ∈ FixSet σ ∧ y ∈ FixSet σ ∧
          v = (x * v₁.1 + y * v₂.1, x * v₁.2 + y * v₂.2) := by
        intro v hv
        have hvS : InS σ m₁₁ m₁₂ m₂₁ m₂₂ v := hv
        obtain ⟨x, y, hx, hy⟩ := hspan v
        have hrel := inS_relation hvS hv₁ hv₂ (c₁ := 1) (c₂ := -x) (c₃ := -y)
          (by linear_combination hx) (by linear_combination hy)
        simp only [map_one, map_neg, one_mul] at hrel
        obtain ⟨r1, r2⟩ := hrel
        have h0 := hindep (x - σ.symm x) (y - σ.symm y)
          (by linear_combination r1 - hx) (by linear_combination r2 - hy)
        refine ⟨x, y, ?_, ?_, Prod.ext hx hy⟩
        · rw [mem_fixSet]
          have h := congrArg σ (sub_eq_zero.mp h0.1)
          rw [RingEquiv.apply_symm_apply] at h
          exact h
        · rw [mem_fixSet]
          have h := congrArg σ (sub_eq_zero.mp h0.2)
          rw [RingEquiv.apply_symm_apply] at h
          exact h
      let T : Set (F × F) := (fun p : FixSet σ × FixSet σ =>
        ((p.1 : F) * v₁.1 + (p.2 : F) * v₂.1, (p.1 : F) * v₁.2 + (p.2 : F) * v₂.2)) '' Set.univ
      have hST : S ⊆ T := fun v hv => by
        obtain ⟨x, y, hx, hy, rfl⟩ := hcoef v hv
        exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), Set.mem_univ _, rfl⟩
      calc Nat.card S ≤ Nat.card T := Nat.card_mono (Set.toFinite _) hST
        _ ≤ Nat.card (Set.univ : Set (FixSet σ × FixSet σ)) := Nat.card_image_le Set.finite_univ
        _ = Nat.card (FixSet σ) ^ 2 := by simp [Nat.card_prod, sq]

theorem line_param {α β : F} (h : α ≠ 0 ∨ β ≠ 0) :
    ∃ v₀ : F × F, v₀ ≠ 0 ∧ ∀ v : F × F, v.1 * α + v.2 * β = 0 →
      ∃ t : F, v = (t * v₀.1, t * v₀.2) := by
  refine ⟨(β, -α), ?_, fun v hv => ?_⟩
  · rcases h with h | h
    · intro h0
      apply h
      have := congrArg Prod.snd h0
      simpa using this
    · intro h0
      apply h
      have := congrArg Prod.fst h0
      simpa using this
  · by_cases hβ : β = 0
    · have hα : α ≠ 0 := h.resolve_right (by simpa using hβ)
      refine ⟨-v.2 / α, ?_⟩
      have h1 : v.1 = 0 := by
        rw [hβ] at hv
        have : v.1 * α = 0 := by linear_combination hv
        exact (mul_eq_zero.mp this).resolve_right hα
      refine Prod.ext ?_ ?_
      · simp [hβ, h1]
      · simp only
        field_simp
    · refine ⟨v.1 / β, ?_⟩
      refine Prod.ext ?_ ?_
      · simp only
        field_simp
      · simp only
        field_simp
        linear_combination hv

theorem card_line_le [Finite F] {α β : F} (h : α ≠ 0 ∨ β ≠ 0) (Q : Set (F × F))
    (hQ : ∀ v ∈ Q, v.1 * α + v.2 * β = 0) : Nat.card Q ≤ Nat.card F := by
  obtain ⟨v₀, hv₀, hv⟩ := line_param h
  choose! t ht using fun v (hvQ : v ∈ Q) => hv v (hQ v hvQ)
  have hinj : Function.Injective (fun v : Q => t v.1) := by
    intro a b hab
    apply Subtype.ext
    rw [ht a.1 a.2, ht b.1 b.2]
    simp only at hab
    rw [hab]
  exact Nat.card_le_card_of_injective _ hinj

theorem card_inS_line_le [Finite F] (σ : F ≃+* F) (m₁₁ m₁₂ m₂₁ m₂₂ : F) {v₀ : F × F}
    (hv₀ : v₀ ≠ 0) :
    Nat.card {v : F × F | InS σ m₁₁ m₁₂ m₂₁ m₂₂ v ∧ ∃ t : F, v = (t * v₀.1, t * v₀.2)} ≤
      Nat.card (FixSet σ) := by
  classical
  have hLpos : 0 < Nat.card (FixSet σ) := by
    have : Finite (FixSet σ) := inferInstance
    exact Nat.card_pos_iff.mpr ⟨⟨⟨0, by simp [FixSet]⟩⟩, inferInstance⟩
  set Q : Set (F × F) := {v : F × F | InS σ m₁₁ m₁₂ m₂₁ m₂₂ v ∧ ∃ t : F, v = (t * v₀.1, t * v₀.2)}
    with hQ
  by_cases hQ0 : ∀ v ∈ Q, v = 0
  · have : Q ⊆ {(0, 0)} := fun v hv => by
      rw [Set.mem_singleton_iff, hQ0 v hv]
      rfl
    calc Nat.card Q ≤ Nat.card ({(0, 0)} : Set (F × F)) :=
          Nat.card_mono (Set.finite_singleton _) this
      _ = 1 := by simp
      _ ≤ Nat.card (FixSet σ) := hLpos
  · push Not at hQ0
    obtain ⟨u, ⟨hu, t₀, rfl⟩, hu0⟩ := hQ0
    have ht₀ : t₀ ≠ 0 := by
      rintro rfl
      exact hu0 (by simp)
    have hcoef : ∀ v ∈ Q, ∃ ℓ ∈ FixSet σ, v = ((ℓ * t₀) * v₀.1, (ℓ * t₀) * v₀.2) := by
      rintro v ⟨hv, t, rfl⟩
      have hrel := inS_relation hv hu (inS_zero σ m₁₁ m₁₂ m₂₁ m₂₂) (c₁ := t₀) (c₂ := -t) (c₃ := 0)
        (by simp only; ring) (by simp only; ring)
      simp only [map_neg, map_zero, zero_mul, add_zero] at hrel
      obtain ⟨r1, r2⟩ := hrel
      have key : σ.symm t₀ * t - σ.symm t * t₀ = 0 := by
        rcases ne_zero_coord hv₀ with h | h
        · have : (σ.symm t₀ * t - σ.symm t * t₀) * v₀.1 = 0 := by linear_combination r1
          exact (mul_eq_zero.mp this).resolve_right h
        · have : (σ.symm t₀ * t - σ.symm t * t₀) * v₀.2 = 0 := by linear_combination r2
          exact (mul_eq_zero.mp this).resolve_right h
      refine ⟨t / t₀, ?_, ?_⟩
      · rw [mem_fixSet]
        have h2 := congrArg σ key
        simp only [map_sub, map_mul, RingEquiv.apply_symm_apply, map_zero] at h2
        have hσt₀ : σ t₀ ≠ 0 := by simpa using ht₀
        rw [map_div₀]
        field_simp
        linear_combination h2
      · have : t / t₀ * t₀ = t := by field_simp
        rw [this]
    let T : Set (F × F) := (fun ℓ : FixSet σ =>
      (((ℓ : F) * t₀) * v₀.1, ((ℓ : F) * t₀) * v₀.2)) '' Set.univ
    have hQT : Q ⊆ T := fun v hv => by
      obtain ⟨ℓ, hℓ, rfl⟩ := hcoef v hv
      exact ⟨⟨ℓ, hℓ⟩, Set.mem_univ _, rfl⟩
    calc Nat.card Q ≤ Nat.card T := Nat.card_mono (Set.toFinite _) hQT
      _ ≤ Nat.card (Set.univ : Set (FixSet σ)) := Nat.card_image_le Set.finite_univ
      _ = Nat.card (FixSet σ) := by simp

end Semilin

end CFSG.QuasithinUnique.Fin257
