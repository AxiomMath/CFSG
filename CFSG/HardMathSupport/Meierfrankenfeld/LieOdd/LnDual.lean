module

public import Mathlib.Algebra.Module.StablyFree.Basic
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
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Topology.Sheaves.Init

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open Matrix

section
variable {F K : Type} [Field F] [Finite F] [Field K] [Finite K] [Algebra F K] {m : ℕ}

@[expose] noncomputable def dualForm (τ : K →ₗ[F] F) : (Fin m → K) →ₗ[F] (Fin m → K) →ₗ[F] F :=
  LinearMap.mk₂ F (fun w c => τ (w ⬝ᵥ c))
    (fun w w' c => by simp [add_dotProduct])
    (fun a w c => by simp [smul_dotProduct])
    (fun w c c' => by simp [dotProduct_add])
    (fun a w c => by simp [dotProduct_smul])

theorem dualForm_apply (τ : K →ₗ[F] F) (w c : Fin m → K) : dualForm τ w c = τ (w ⬝ᵥ c) := rfl

theorem exists_dualForm_ne_zero {τ : K →ₗ[F] F} (hτ : τ ≠ 0) {w : Fin m → K} (hw : w ≠ 0) :
    ∃ c, dualForm τ w c ≠ 0 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra h
    push Not at h
    exact hw (funext h)
  obtain ⟨a, ha⟩ : ∃ a, τ a ≠ 0 := by
    by_contra h
    push Not at h
    exact hτ (LinearMap.ext h)
  refine ⟨Pi.single i (a / w i), ?_⟩
  rw [dualForm_apply, dotProduct_single, mul_div_cancel₀ _ hi]
  exact ha

theorem dualForm_symm (τ : K →ₗ[F] F) (w c : Fin m → K) : dualForm τ w c = dualForm τ c w := by
  simp [dualForm_apply, dotProduct_comm]

theorem dualForm_nondegenerate {τ : K →ₗ[F] F} (hτ : τ ≠ 0) :
    (dualForm (m := m) τ).Nondegenerate := by
  refine ⟨fun w hw => ?_, fun c hc => ?_⟩
  · by_contra hw0
    obtain ⟨c, hc⟩ := exists_dualForm_ne_zero hτ hw0
    exact hc (hw c)
  · by_contra hc0
    obtain ⟨w, hw⟩ := exists_dualForm_ne_zero hτ hc0
    exact hw (by rw [dualForm_symm]; exact hc w)

theorem exists_dualForm_eq {τ : K →ₗ[F] F} (hτ : τ ≠ 0) (f : Module.Dual F (Fin m → K)) :
    ∃ w : Fin m → K, ∀ c, dualForm τ w c = f c := by
  have : FiniteDimensional F (Fin m → K) := inferInstance
  obtain ⟨w, hw⟩ := (LinearMap.BilinForm.toDual (dualForm (m := m) τ)
    (dualForm_nondegenerate hτ)).surjective f
  exact ⟨w, fun c => by rw [← hw]; rfl⟩

theorem dualForm_left_eq_zero {τ : K →ₗ[F] F} (hτ : τ ≠ 0) {w : Fin m → K}
    (h : ∀ c, dualForm τ w c = 0) : w = 0 :=
  (dualForm_nondegenerate hτ).1 w h

theorem dualForm_sub_left (τ : K →ₗ[F] F) (w w' c : Fin m → K) :
    dualForm τ (w - w') c = dualForm τ w c - dualForm τ w' c := by
  simp [dualForm_apply]

theorem dualForm_smul_left (τ : K →ₗ[F] F) (a : F) (w c : Fin m → K) :
    dualForm τ (a • w) c = a * dualForm τ w c := by
  simp [dualForm_apply]

theorem dualForm_sub_right (τ : K →ₗ[F] F) (w c c' : Fin m → K) :
    dualForm τ w (c - c') = dualForm τ w c - dualForm τ w c' := by
  simp [dualForm_apply, dotProduct_sub]

theorem dualForm_smul_right (τ : K →ₗ[F] F) (a : F) (w c : Fin m → K) :
    dualForm τ w (a • c) = a * dualForm τ w c := by
  simp [dualForm_apply]

theorem exists_smul_of_ker_eq {τ : K →ₗ[F] F} (hτ : τ ≠ 0) {w w' : Fin m → K} (hw : w ≠ 0)
    (h : ∀ c, dualForm τ w c = 0 ↔ dualForm τ w' c = 0) :
    ∃ a : F, a ≠ 0 ∧ w' = a • w := by
  obtain ⟨c₀, hc₀⟩ := exists_dualForm_ne_zero hτ hw
  have hc₀' : dualForm τ w' c₀ ≠ 0 := fun h0 => hc₀ ((h c₀).2 h0)
  set a : F := dualForm τ w' c₀ / dualForm τ w c₀ with ha
  have hform : ∀ c, dualForm τ w' c = a * dualForm τ w c := by
    intro c
    set t : F := dualForm τ w c / dualForm τ w c₀ with ht
    have h1 : dualForm τ w (c - t • c₀) = 0 := by
      rw [dualForm_sub_right, dualForm_smul_right, ht, div_mul_cancel₀ _ hc₀, sub_self]
    have h2 := (h _).1 h1
    rw [dualForm_sub_right, dualForm_smul_right] at h2
    have h3 : dualForm τ w' c = t * dualForm τ w' c₀ := sub_eq_zero.1 h2
    rw [h3, ht, ha]
    field_simp
  refine ⟨a, ?_, ?_⟩
  · intro h0
    apply hc₀'
    rw [hform c₀, h0, zero_mul]
  · apply sub_eq_zero.1
    apply dualForm_left_eq_zero hτ
    intro c
    rw [dualForm_sub_left, dualForm_smul_left, hform c, sub_self]

theorem card_fiber_le [Fintype (Fin m → K)] [DecidableEq (Fin m → K)] {τ : K →ₗ[F] F}
    (hτ : τ ≠ 0) {w : Fin m → K} (hw : w ≠ 0) [DecidablePred (fun w' : Fin m → K =>
      w' ≠ 0 ∧ ∀ c, dualForm τ w c = 0 ↔ dualForm τ w' c = 0)] :
    (Finset.univ.filter (fun w' : Fin m → K =>
      w' ≠ 0 ∧ ∀ c, dualForm τ w c = 0 ↔ dualForm τ w' c = 0)).card ≤ Nat.card F - 1 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hsub : (Finset.univ.filter (fun w' : Fin m → K =>
      w' ≠ 0 ∧ ∀ c, dualForm τ w c = 0 ↔ dualForm τ w' c = 0)) ⊆
      (Finset.univ : Finset Fˣ).image (fun a : Fˣ => (a : F) • w) := by
    intro w' hw'
    obtain ⟨-, -, hker⟩ := Finset.mem_filter.1 hw'
    obtain ⟨a, ha, rfl⟩ := exists_smul_of_ker_eq hτ hw hker
    exact Finset.mem_image.2 ⟨Units.mk0 a ha, Finset.mem_univ _, rfl⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
  rw [Finset.card_univ, Fintype.card_units, ← Nat.card_eq_fintype_card]

end

section
variable {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime] [Algebra (ZMod p) K] {m : ℕ}

theorem exists_hyperplane_form {τ : K →ₗ[ZMod p] ZMod p} (hτ : τ ≠ 0)
    (D' : AddSubgroup (Fin m → K)) (hD : D'.index = p) :
    ∃ w : Fin m → K, w ≠ 0 ∧ ∀ c, c ∈ D' ↔ dualForm τ w c = 0 := by
  classical
  have hp1 : p ≠ 1 := (Fact.out : p.Prime).one_lt.ne'
  have hne : D' ≠ ⊤ := by
    intro h
    rw [h, AddSubgroup.index_top] at hD
    exact hp1 hD.symm
  obtain ⟨x, hx⟩ : ∃ x, x ∉ D' := by
    by_contra hcon
    push Not at hcon
    exact hne (eq_top_iff.2 fun y _ => hcon y)
  obtain ⟨f, hfx, hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem
    (p := (AddSubgroup.toZModSubmodule p D')) (x := x) hx inferInstance
  have hDker : ∀ d ∈ D', f d = 0 := by
    intro d hd
    have hmem : f d ∈ Submodule.map f (AddSubgroup.toZModSubmodule p D') :=
      Submodule.mem_map_of_mem (show d ∈ AddSubgroup.toZModSubmodule p D' from hd)
    rw [hf] at hmem
    exact (Submodule.mem_bot (ZMod p)).1 hmem
  let Kf : AddSubgroup (Fin m → K) := f.toAddMonoidHom.ker
  have hDK : D' ≤ Kf := fun d hd => hDker d hd
  have hrange : f.toAddMonoidHom.range = ⊤ := by
    rw [eq_top_iff]
    intro a _
    refine ⟨(a / f x) • x, ?_⟩
    show f ((a / f x) • x) = a
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hfx]
  have hKfidx : Kf.index = p := by
    rw [AddSubgroup.index_ker, hrange, Nat.card_congr AddSubgroup.topEquiv.toEquiv]
    simp
  have hcardD := AddSubgroup.card_mul_index D'
  have hcardK := AddSubgroup.card_mul_index Kf
  have hpos : 0 < p := (Fact.out : p.Prime).pos
  have hcard : Nat.card Kf = Nat.card D' := by
    rw [hD] at hcardD
    rw [hKfidx] at hcardK
    exact Nat.eq_of_mul_eq_mul_right hpos (hcardK.trans hcardD.symm)
  have hDeq : D' = Kf := AddSubgroup.eq_of_le_of_card_ge hDK hcard.le
  obtain ⟨w, hw⟩ := exists_dualForm_eq hτ f
  refine ⟨w, ?_, fun c => ?_⟩
  · rintro rfl
    apply hfx
    rw [← hw x]
    simp
  · rw [hDeq, hw c]
    rfl

end

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
