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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.OddStandard.Harada75

abbrev W₀ : Type := ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2

@[expose] def b₀ (w w' : W₀) : ZMod 2 :=
  w.1 * w'.2.2.1 + w.2.2.1 * w'.1 + w.2.1 * w'.2.2.2 + w.2.2.2 * w'.2.1

@[expose] def q₀ (w : W₀) : ZMod 2 := w.1 * w.2.2.1 + w.2.1 * w.2.2.2

theorem q₀_add : ∀ a b : W₀, q₀ (a + b) = q₀ a + q₀ b + b₀ a b := by decide

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

structure IsIsom (σ : W₀ → W₀) : Prop where
  add : ∀ a b, σ (a + b) = σ a + σ b
  q : ∀ w, q₀ (σ w) = q₀ w
  E : ∀ w, ((σ w).2.2.1 = 0 ∧ (σ w).2.2.2 = 0) ↔ (w.2.2.1 = 0 ∧ w.2.2.2 = 0)

@[expose] def Isom : Subgroup (Equiv.Perm W₀) where
  carrier := {σ | IsIsom σ}
  one_mem' := ⟨fun _ _ => rfl, fun _ => rfl, fun _ => Iff.rfl⟩
  mul_mem' := by
    intro σ τ hσ hτ
    refine ⟨fun a b => ?_, fun w => ?_, fun w => ?_⟩
    · show σ (τ (a + b)) = σ (τ a) + σ (τ b)
      rw [hτ.add, hσ.add]
    · show q₀ (σ (τ w)) = q₀ w
      rw [hσ.q, hτ.q]
    · show ((σ (τ w)).2.2.1 = 0 ∧ (σ (τ w)).2.2.2 = 0) ↔ _
      rw [hσ.E, hτ.E]
  inv_mem' := by
    intro σ hσ
    refine ⟨fun a b => ?_, fun w => ?_, fun w => ?_⟩
    · apply σ.injective
      show σ (σ⁻¹ (a + b)) = σ (σ⁻¹ a + σ⁻¹ b)
      rw [hσ.add]; simp
    · have := hσ.q (σ⁻¹ w)
      simp at this
      exact this.symm
    · have := hσ.E (σ⁻¹ w)
      simp at this
      exact this.symm

structure Cols where
  c1 : W₀
  c2 : W₀
  c3 : W₀
  c4 : W₀
  deriving DecidableEq

def L12 : List Cols := [
  ⟨(0, 1, 0, 0), (1, 0, 0, 0), (0, 0, 0, 1), (0, 0, 1, 0)⟩,
  ⟨(0, 1, 0, 0), (1, 0, 0, 0), (1, 0, 0, 1), (0, 1, 1, 0)⟩,
  ⟨(0, 1, 0, 0), (1, 1, 0, 0), (0, 0, 1, 1), (0, 0, 1, 0)⟩,
  ⟨(0, 1, 0, 0), (1, 1, 0, 0), (1, 1, 1, 1), (0, 1, 1, 0)⟩,
  ⟨(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)⟩,
  ⟨(1, 0, 0, 0), (0, 1, 0, 0), (0, 1, 1, 0), (1, 0, 0, 1)⟩,
  ⟨(1, 0, 0, 0), (1, 1, 0, 0), (0, 0, 1, 1), (0, 0, 0, 1)⟩,
  ⟨(1, 0, 0, 0), (1, 1, 0, 0), (1, 1, 1, 1), (1, 0, 0, 1)⟩,
  ⟨(1, 1, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 1, 1)⟩,
  ⟨(1, 1, 0, 0), (0, 1, 0, 0), (0, 1, 1, 0), (1, 1, 1, 1)⟩,
  ⟨(1, 1, 0, 0), (1, 0, 0, 0), (0, 0, 0, 1), (0, 0, 1, 1)⟩,
  ⟨(1, 1, 0, 0), (1, 0, 0, 0), (1, 0, 0, 1), (1, 1, 1, 1)⟩]

private def Step4 (c₁ c₂ c₃ : W₀) : Prop :=
  ∀ c₄ : W₀, q₀ c₄ = 0 → b₀ c₁ c₄ = 0 → b₀ c₂ c₄ = 1 → b₀ c₃ c₄ = 0 →
    (⟨c₁, c₂, c₃, c₄⟩ : Cols) ∈ L12

private instance (c₁ c₂ c₃ : W₀) : Decidable (Step4 c₁ c₂ c₃) := by unfold Step4; infer_instance

private def Step3 (c₁ c₂ : W₀) : Prop :=
  ∀ c₃ : W₀, q₀ c₃ = 0 → b₀ c₁ c₃ = 1 → b₀ c₂ c₃ = 0 → Step4 c₁ c₂ c₃

private instance (c₁ c₂ : W₀) : Decidable (Step3 c₁ c₂) := by unfold Step3; infer_instance

private def Step2 (c₁ : W₀) : Prop :=
  ∀ c₂ : W₀, c₂.2.2.1 = 0 → c₂.2.2.2 = 0 → Step3 c₁ c₂

private instance (c₁ : W₀) : Decidable (Step2 c₁) := by unfold Step2; infer_instance

private def Step1 : Prop := ∀ c₁ : W₀, c₁.2.2.1 = 0 → c₁.2.2.2 = 0 → Step2 c₁

private instance : Decidable Step1 := by unfold Step1; infer_instance

private theorem step1 : Step1 := by decide

theorem cols_classification :
    ∀ c₁ : W₀, c₁.2.2.1 = 0 → c₁.2.2.2 = 0 →
    ∀ c₂ : W₀, c₂.2.2.1 = 0 → c₂.2.2.2 = 0 →
    ∀ c₃ : W₀, q₀ c₃ = 0 → b₀ c₁ c₃ = 1 → b₀ c₂ c₃ = 0 →
    ∀ c₄ : W₀, q₀ c₄ = 0 → b₀ c₁ c₄ = 0 → b₀ c₂ c₄ = 1 → b₀ c₃ c₄ = 0 →
    (⟨c₁, c₂, c₃, c₄⟩ : Cols) ∈ L12 := step1

@[expose] def e1 : W₀ := (1, 0, 0, 0)
@[expose] def e2 : W₀ := (0, 1, 0, 0)
@[expose] def f1 : W₀ := (0, 0, 1, 0)
@[expose] def f2 : W₀ := (0, 0, 0, 1)

@[expose] def app (c : Cols) (w : W₀) : W₀ :=
  w.1 • c.c1 + w.2.1 • c.c2 + w.2.2.1 • c.c3 + w.2.2.2 • c.c4

@[expose] def cols (σ : W₀ → W₀) : Cols := ⟨σ e1, σ e2, σ f1, σ f2⟩

namespace IsIsom
variable {σ : W₀ → W₀} (h : IsIsom σ)
include h

theorem map_zero : σ 0 = 0 := by
  have := h.add 0 0
  simpa using this

theorem eq_app (w : W₀) : σ w = app (cols σ) w := by
  have hw : w = (w.1, 0, 0, 0) + (0, w.2.1, 0, 0) + (0, 0, w.2.2.1, 0) + (0, 0, 0, w.2.2.2) := by
    ext <;> simp
  have h1 : ∀ a : ZMod 2, σ (a, 0, 0, 0) = a • σ e1 := by
    intro a
    rcases zmod2_cases a with rfl | rfl
    · simp only [zero_smul]; exact h.map_zero
    · simp [e1]
  have h2 : ∀ a : ZMod 2, σ (0, a, 0, 0) = a • σ e2 := by
    intro a
    rcases zmod2_cases a with rfl | rfl
    · simp only [zero_smul]; exact h.map_zero
    · simp [e2]
  have h3 : ∀ a : ZMod 2, σ (0, 0, a, 0) = a • σ f1 := by
    intro a
    rcases zmod2_cases a with rfl | rfl
    · simp only [zero_smul]; exact h.map_zero
    · simp [f1]
  have h4 : ∀ a : ZMod 2, σ (0, 0, 0, a) = a • σ f2 := by
    intro a
    rcases zmod2_cases a with rfl | rfl
    · simp only [zero_smul]; exact h.map_zero
    · simp [f2]
  conv_lhs => rw [hw]
  rw [h.add, h.add, h.add, h1, h2, h3, h4]
  rfl

theorem b_eq (a b : W₀) : b₀ (σ a) (σ b) = b₀ a b := by
  have h1 := q₀_add a b
  have h2 := q₀_add (σ a) (σ b)
  rw [← h.add, h.q, h.q a, h.q b] at h2
  rw [h1] at h2
  have : q₀ a + q₀ b + b₀ a b = q₀ a + q₀ b + b₀ (σ a) (σ b) := h2
  exact (add_left_cancel this).symm

theorem cols_mem : cols σ ∈ L12 := by
  have hE1 := (h.E e1).2 (by simp [e1])
  have hE2 := (h.E e2).2 (by simp [e2])
  exact cols_classification (σ e1) hE1.1 hE1.2 (σ e2) hE2.1 hE2.2 (σ f1)
    (by rw [h.q]; decide) (by rw [h.b_eq]; decide) (by rw [h.b_eq]; decide) (σ f2)
    (by rw [h.q]; decide) (by rw [h.b_eq]; decide) (by rw [h.b_eq]; decide)
    (by rw [h.b_eq]; decide)

end IsIsom

theorem cols_injective : Function.Injective (fun σ : Isom => cols (σ : Equiv.Perm W₀)) := by
  intro σ τ h
  apply Subtype.ext
  apply Equiv.ext
  intro w
  rw [σ.2.eq_app, τ.2.eq_app]
  simp only at h
  rw [h]

theorem card_le_filter (Γ : Subgroup Isom) (P : Cols → Prop) [DecidablePred P]
    (hP : ∀ g ∈ Γ, P (cols (g : Equiv.Perm W₀))) :
    Nat.card Γ ≤ (L12.filter (fun c => decide (P c))).length := by
  let F : Γ → {x // x ∈ (L12.filter (fun c => decide (P c))).toFinset} := fun g =>
    ⟨cols ((g : Isom) : Equiv.Perm W₀), by
      simpa using ⟨(g.1.2).cols_mem, hP g.1 g.2⟩⟩
  have hF : Function.Injective F := by
    intro g g' hg
    apply Subtype.ext
    apply cols_injective
    simpa [F] using congrArg Subtype.val hg
  have := Nat.card_le_card_of_injective F hF
  rw [Nat.card_eq_fintype_card (α := {x // x ∈ (L12.filter (fun c => decide (P c))).toFinset}),
    Fintype.card_coe] at this
  exact this.trans (List.toFinset_card_le _)

theorem card_isom_le : Nat.card Isom ≤ 12 := by
  have := card_le_filter (⊤ : Subgroup Isom) (fun _ => True) (fun _ _ => trivial)
  have h12 : (L12.filter (fun c => decide True)).length = 12 := by decide
  rw [h12] at this
  have e : Nat.card (⊤ : Subgroup Isom) = Nat.card Isom :=
    Nat.card_congr (Subgroup.topEquiv).toEquiv
  omega

def c3 : Cols := ⟨(0, 1, 0, 0), (1, 1, 0, 0), (0, 0, 1, 1), (0, 0, 1, 0)⟩

theorem c3_bij : Function.Bijective (app c3) := by decide

noncomputable def g3 : Equiv.Perm W₀ := Equiv.ofBijective (app c3) c3_bij

theorem g3_isIsom : IsIsom g3 := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · decide
  · decide

theorem g3_cube : g3 ^ 3 = 1 := by
  refine Equiv.ext fun w => ?_
  have : ∀ w : W₀, g3 (g3 (g3 w)) = w := by decide
  simpa [pow_succ] using this w

theorem g3_ne_one : g3 ≠ 1 := by
  intro h
  have : g3 e1 = e1 := by rw [h]; rfl
  revert this
  decide

theorem three_dvd_card : 3 ∣ Nat.card Isom := by
  have h : orderOf (⟨g3, g3_isIsom⟩ : Isom) = 3 := by
    apply orderOf_eq_prime
    · apply Subtype.ext; exact g3_cube
    · intro h; apply g3_ne_one; exact congrArg Subtype.val h
  rw [← h]
  exact orderOf_dvd_natCard _

theorem card_le_four_of_isPGroup (Γ : Subgroup Isom) (hΓ : IsPGroup 2 Γ) : Nat.card Γ ≤ 4 := by
  obtain ⟨n, hn⟩ := hΓ.exists_card_eq
  have hdvd : Nat.card Γ ∣ Nat.card Isom := Subgroup.card_subgroup_dvd_card Γ
  have h12 := card_isom_le
  have h3 := three_dvd_card
  have hpos : 0 < Nat.card Isom := Nat.card_pos
  rw [hn] at hdvd ⊢
  by_contra hlt
  push Not at hlt
  have hn3 : 3 ≤ n := by
    by_contra h
    push Not at h
    interval_cases n <;> simp at hlt
  have : 8 ∣ Nat.card Isom := by
    have : 2 ^ 3 ∣ 2 ^ n := pow_dvd_pow 2 hn3
    exact dvd_trans this hdvd
  obtain ⟨k, hk⟩ := this
  obtain ⟨m, hm⟩ := h3
  omega

def idCols : Cols := ⟨(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)⟩

def uCols : Cols := ⟨(1, 0, 0, 0), (0, 1, 0, 0), (0, 1, 1, 0), (1, 0, 0, 1)⟩

private def Fix1 (c : Cols) : Prop := ∀ w : W₀, w.2.2.1 = 0 → w.2.2.2 = 0 → app c w = w

private instance (c : Cols) : Decidable (Fix1 c) := by unfold Fix1; infer_instance

theorem fix_E_cols : ∀ c ∈ L12, (∀ w : W₀, w.2.2.1 = 0 → w.2.2.2 = 0 → app c w = w) →
    c = idCols ∨ c = uCols := by
  intro c hc hfix
  have : Fix1 c := hfix
  revert c
  decide

theorem fixed_space_u : ∀ w : W₀, app uCols w = w → w.2.2.1 = 0 ∧ w.2.2.2 = 0 := by decide

theorem rank_ge_two : ∀ c ∈ L12, c ≠ idCols →
    4 ≤ (Finset.univ.image (fun w : W₀ => app c w + w)).card := by decide

private def PlanePre (u v : W₀) : Prop :=
  u ≠ 0 ∧ v ≠ 0 ∧ u ≠ v ∧ q₀ u = 0 ∧ q₀ v = 0 ∧ b₀ u v = 0

private instance (u v : W₀) : Decidable (PlanePre u v) := by unfold PlanePre; infer_instance

private def PlaneCond (u v : W₀) : Prop :=
  PlanePre u v → (L12.filter (fun c => decide (app c u = u ∧ app c v = v))).length ≤ 2

private instance (u v : W₀) : Decidable (PlaneCond u v) := by unfold PlaneCond; infer_instance

private theorem plane_fix_le : ∀ u v : W₀, PlaneCond u v := by decide

@[expose] def Indep (u v w : W₀) : Prop :=
  u ≠ 0 ∧ v ≠ 0 ∧ u ≠ v ∧ w ≠ 0 ∧ w ≠ u ∧ w ≠ v ∧ w ≠ u + v

instance (u v w : W₀) : Decidable (Indep u v w) := by unfold Indep; infer_instance

private def HyperCond (u v w : W₀) : Prop :=
  Indep u v w →
    (L12.filter (fun c => decide (app c u = u ∧ app c v = v ∧ app c w = w))).length ≤ 1

private instance (u v w : W₀) : Decidable (HyperCond u v w) := by unfold HyperCond; infer_instance

private theorem hyper_fix_le : ∀ u v w : W₀, HyperCond u v w := by decide

private def IsoCond (u v w : W₀) : Prop :=
  Indep u v w → ¬ (b₀ u v = 0 ∧ b₀ u w = 0 ∧ b₀ v w = 0)

private instance (u v w : W₀) : Decidable (IsoCond u v w) := by unfold IsoCond; infer_instance

theorem no_isotropic_three (u v w : W₀) (h : Indep u v w) :
    ¬ (b₀ u v = 0 ∧ b₀ u w = 0 ∧ b₀ v w = 0) := by
  have key : ∀ u v w : W₀, IsoCond u v w := by decide
  exact key u v w h

theorem card_fix_plane_le (Γ : Subgroup Isom) (u v : W₀) (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v)
    (hqu : q₀ u = 0) (hqv : q₀ v = 0) (hb : b₀ u v = 0)
    (hΓ : ∀ g ∈ Γ, (g : Equiv.Perm W₀) u = u ∧ (g : Equiv.Perm W₀) v = v) : Nat.card Γ ≤ 2 := by
  have h1 := card_le_filter Γ (fun c => app c u = u ∧ app c v = v) (by
    intro g hg
    rw [← (g.2).eq_app u, ← (g.2).eq_app v]
    exact hΓ g hg)
  have h2 : (L12.filter (fun c => decide (app c u = u ∧ app c v = v))).length ≤ 2 := by
    have key : ∀ u v : W₀, PlaneCond u v := plane_fix_le
    exact key u v ⟨hu, hv, huv, hqu, hqv, hb⟩
  omega

theorem card_fix_hyper_le (Γ : Subgroup Isom) (u v w : W₀) (h : Indep u v w)
    (hΓ : ∀ g ∈ Γ, (g : Equiv.Perm W₀) u = u ∧ (g : Equiv.Perm W₀) v = v ∧
      (g : Equiv.Perm W₀) w = w) : Nat.card Γ ≤ 1 := by
  have h1 := card_le_filter Γ (fun c => app c u = u ∧ app c v = v ∧ app c w = w) (by
    intro g hg
    rw [← (g.2).eq_app u, ← (g.2).eq_app v, ← (g.2).eq_app w]
    exact hΓ g hg)
  have h2 : (L12.filter (fun c => decide (app c u = u ∧ app c v = v ∧ app c w = w))).length ≤ 1 :=
    hyper_fix_le u v w h
  omega

theorem rank_image (g : Isom) (hg : g ≠ 1) :
    4 ≤ (Finset.univ.image (fun w : W₀ => (g : Equiv.Perm W₀) w + w)).card := by
  have hne : cols (g : Equiv.Perm W₀) ≠ idCols := by
    intro h
    apply hg
    apply Subtype.ext
    apply Equiv.ext
    intro w
    rw [g.2.eq_app, h]
    have : app idCols w = w := by revert w; decide
    exact this
  have := rank_ge_two _ g.2.cols_mem hne
  have e : (fun w : W₀ => (g : Equiv.Perm W₀) w + w) =
      fun w => app (cols (g : Equiv.Perm W₀)) w + w := by
    funext w; rw [g.2.eq_app]
  rw [e]
  exact this

theorem eq_one_of_cols_id (g : Isom) (h : cols (g : Equiv.Perm W₀) = idCols) : g = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro w
  rw [g.2.eq_app, h]
  have : app idCols w = w := by revert w; decide
  exact this

theorem card_le_two_of_cols (Γ : Subgroup Isom)
    (h : ∀ g ∈ Γ, cols (g : Equiv.Perm W₀) = idCols ∨ cols (g : Equiv.Perm W₀) = uCols) :
    Nat.card Γ ≤ 2 := by
  have h1 := card_le_filter Γ (fun c => c = idCols ∨ c = uCols) h
  have hf : (L12.filter (fun c => decide (c = idCols ∨ c = uCols))).length = 2 := by decide
  omega

theorem cols_of_fix_E (g : Isom)
    (h : ∀ w : W₀, w.2.2.1 = 0 → w.2.2.2 = 0 → (g : Equiv.Perm W₀) w = w) :
    cols (g : Equiv.Perm W₀) = idCols ∨ cols (g : Equiv.Perm W₀) = uCols :=
  fix_E_cols _ g.2.cols_mem (fun w h1 h2 => by rw [← g.2.eq_app]; exact h w h1 h2)

theorem mem_E_of_fixed (g : Isom) (hg : cols (g : Equiv.Perm W₀) = uCols) (w : W₀)
    (hw : (g : Equiv.Perm W₀) w = w) : w.2.2.1 = 0 ∧ w.2.2.2 = 0 := by
  apply fixed_space_u
  rw [← hg, ← g.2.eq_app]
  exact hw

end CFSG.OddStandard.Harada75
