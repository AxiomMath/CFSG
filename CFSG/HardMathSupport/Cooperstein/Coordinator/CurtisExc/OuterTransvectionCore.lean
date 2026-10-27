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
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

section Core

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem zmod2_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by revert c; decide

theorem vec_add_self (x : V) : x + x = 0 := by
  have : (1 + 1 : ZMod 2) = 0 := by decide
  calc x + x = ((1 : ZMod 2) + 1) • x := by rw [add_smul, one_smul]
    _ = 0 := by rw [this, zero_smul]

theorem vec_neg_eq (x : V) : -x = x := by
  have := vec_add_self x
  exact neg_eq_of_add_eq_zero_right this

theorem vec_sub_eq (x y : V) : x - y = x + y := by rw [sub_eq_add_neg, vec_neg_eq]

abbrev opA (t : (Module.End (ZMod 2) V)ˣ) : Module.End (ZMod 2) V := (t : Module.End (ZMod 2) V) - 1

theorem unit_apply_inv (g : (Module.End (ZMod 2) V)ˣ) (v : V) : g.val (g⁻¹.val v) = v := by
  have := LinearMap.congr_fun (Units.mul_inv g) v
  rwa [Module.End.mul_apply, Module.End.one_apply] at this

theorem unit_inv_apply (g : (Module.End (ZMod 2) V)ˣ) (v : V) : g⁻¹.val (g.val v) = v := by
  have := LinearMap.congr_fun (Units.inv_mul g) v
  rwa [Module.End.mul_apply, Module.End.one_apply] at this

theorem opA_apply (t : (Module.End (ZMod 2) V)ˣ) (v : V) : opA t v = t.val v + v := by
  simp [opA, vec_sub_eq]

theorem opA_sq (t : (Module.End (ZMod 2) V)ˣ) (ht : t * t = 1) (v : V) : opA t (opA t v) = 0 := by
  have h : t.val (t.val v) = v := by
    have := congrArg (fun x : (Module.End (ZMod 2) V)ˣ => x.val v) ht
    simpa [Module.End.mul_apply] using this
  rw [opA_apply, opA_apply, map_add, h]
  have := vec_add_self (t.val v)
  have h2 := vec_add_self v
  calc v + t.val v + (t.val v + v) = (v + v) + (t.val v + t.val v) := by abel
    _ = 0 := by rw [vec_add_self, vec_add_self, add_zero]


theorem inv_iff (x : (Module.End (ZMod 2) V)ˣ) :
    x * x = 1 ↔ ∀ v, opA x (opA x v) = 0 := by
  constructor
  · intro h v; exact opA_sq x h v
  · intro h
    apply Units.ext
    apply LinearMap.ext
    intro v
    have h1 := h v
    rw [opA_apply, opA_apply, map_add] at h1
    have e : x.val (x.val v) + x.val v + (x.val v + v) = x.val (x.val v) + v := by
      calc x.val (x.val v) + x.val v + (x.val v + v) =
            x.val (x.val v) + (x.val v + x.val v) + v := by abel
        _ = _ := by rw [vec_add_self, add_zero]
    rw [e] at h1
    have h2 : x.val (x.val v) = v := by
      have := congrArg (fun y => y + v) h1
      simpa [add_assoc, vec_add_self] using this
    simpa [Module.End.mul_apply] using h2

def TvW (t : (Module.End (ZMod 2) V)ˣ) (w : V) : Prop :=
  w ≠ 0 ∧ (∃ v, opA t v = w) ∧ ∀ v, opA t v = 0 ∨ opA t v = w

theorem tvW_exists [Finite V] {t : (Module.End (ZMod 2) V)ˣ}
    (h : Module.finrank (ZMod 2) ↥(LinearMap.range (opA t)) = 1) : ∃ w, TvW t w := by
  obtain ⟨⟨w, hw⟩, hne, hall⟩ := finrank_eq_one_iff'.1 h
  refine ⟨w, fun h0 => hne (Subtype.ext h0), hw.imp fun v hv => hv, fun v => ?_⟩
  obtain ⟨c, hc⟩ := hall ⟨opA t v, ⟨v, rfl⟩⟩
  have hc' : c • w = opA t v := congrArg Subtype.val hc
  rcases zmod2_cases c with rfl | rfl
  · left; rw [← hc', zero_smul]
  · right; rw [← hc', one_smul]

theorem tvW_unique {t : (Module.End (ZMod 2) V)ˣ} {w w' : V} (h : TvW t w) (h' : TvW t w') :
    w = w' := by
  obtain ⟨v, hv⟩ := h'.2.1
  rcases h.2.2 v with h0 | h1
  · exact absurd (hv.symm.trans h0) h'.1
  · exact h1.symm.trans hv

theorem opA_conj (g t : (Module.End (ZMod 2) V)ˣ) (v : V) :
    opA (g * t * g⁻¹) v = g.val (opA t (g⁻¹.val v)) := by
  have h : g.val (g⁻¹.val v) = v := unit_apply_inv g v
  rw [opA_apply, opA_apply, map_add]
  simp only [Units.val_mul, Module.End.mul_apply]
  rw [h]

theorem tvW_conj (g t : (Module.End (ZMod 2) V)ˣ) {w : V} (h : TvW t w) :
    TvW (g * t * g⁻¹) (g.val w) := by
  have hg : ∀ x : V, g.val (g⁻¹.val x) = x := unit_apply_inv g
  have hg' : ∀ x : V, g⁻¹.val (g.val x) = x := unit_inv_apply g
  refine ⟨fun h0 => h.1 (by simpa [hg'] using congrArg g⁻¹.val h0), ?_, fun v => ?_⟩
  · obtain ⟨v₀, hv₀⟩ := h.2.1
    refine ⟨g.val v₀, ?_⟩
    rw [opA_conj, hg', hv₀]
  · rw [opA_conj]
    rcases h.2.2 (g⁻¹.val v) with h0 | h1
    · left; rw [h0, map_zero]
    · right; rw [h1]

theorem finrank_range_opA_le [Finite V] {s : (Module.End (ZMod 2) V)ˣ} {w : V} (h : TvW s w) :
    Module.finrank (ZMod 2) ↥(LinearMap.range (opA s)) ≤ 1 := by
  have hle : LinearMap.range (opA s) ≤ Submodule.span (ZMod 2) {w} := by
    rintro _ ⟨v, rfl⟩
    rcases h.2.2 v with h0 | h1
    · rw [h0]; exact zero_mem _
    · rw [h1]; exact Submodule.subset_span rfl
  refine (Submodule.finrank_mono hle).trans ?_
  simpa using finrank_span_le_card (R := ZMod 2) ({w} : Set V)


theorem app_eq (t : (Module.End (ZMod 2) V)ˣ) (v : V) : t.val v = opA t v + v := by
  rw [opA_apply, add_assoc, vec_add_self, add_zero]

theorem pair_ne [Finite V] {L : Subgroup (Module.End (ZMod 2) V)ˣ}
    (hrank : ∀ x ∈ L, x ≠ 1 → x * x = 1 → 5 ≤ Module.finrank (ZMod 2) ↥(LinearMap.range (opA x)))
    {s t : (Module.End (ZMod 2) V)ˣ} (hs : s * s = 1) (ht : t * t = 1) {ws wt : V}
    (hws : TvW s ws) (hwt : TvW t wt) (hne : s ≠ t) (hst : s * t ∈ L) : opA t ws ≠ 0 := by
  intro hc
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have hBA : ∀ v, opA t (opA s v) = 0 := fun v =>
    (hws.2.2 v).elim (fun h => by rw [h, map_zero]) (fun h => by rw [h]; exact hc)
  have hAA := opA_sq s hs
  have hBB := opA_sq t ht
  have hx : ∀ v, opA (s * t) v = opA s v + opA t v + opA s (opA t v) := by
    intro v
    rw [opA_apply]
    simp only [Units.val_mul, Module.End.mul_apply]
    rw [app_eq t v, map_add, app_eq s (opA t v), app_eq s v]
    calc opA s (opA t v) + opA t v + (opA s v + v) + v =
          (opA s (opA t v) + opA t v + opA s v) + (v + v) := by abel
      _ = opA s v + opA t v + opA s (opA t v) := by rw [vec_add_self, add_zero]; abel
  have hxx : ∀ v, opA (s * t) (opA (s * t) v) = opA s (opA t v) := by
    intro v
    rw [hx (opA (s * t) v), hx v]
    simp only [map_add, hAA, hBA, hBB, zero_add, add_zero, add_assoc]
    rw [map_zero, add_zero]
  have hAr := finrank_range_opA_le hws
  have hBr := finrank_range_opA_le hwt
  by_cases hcase : ∃ v, opA s (opA t v) ≠ 0
  · obtain ⟨v₀, hv₀⟩ := hcase
    have hyL : (s * t) * (s * t) ∈ L := mul_mem hst hst
    have hy : ∀ v, opA ((s * t) * (s * t)) v = opA s (opA t v) := by
      intro v
      have h1 : (s * t).val v = opA (s * t) v + v := app_eq _ v
      have h2 : (s * t).val ((s * t).val v) = opA s (opA t v) + v := by
        calc (s * t).val ((s * t).val v) = opA (s * t) ((s * t).val v) + (s * t).val v :=
              app_eq _ _
          _ = opA (s * t) (opA (s * t) v + v) + (opA (s * t) v + v) := by rw [h1]
          _ = (opA (s * t) (opA (s * t) v) + opA (s * t) v) + (opA (s * t) v + v) := by
              rw [map_add]
          _ = opA s (opA t v) + (opA (s * t) v + opA (s * t) v) + v := by rw [hxx]; abel
          _ = opA s (opA t v) + v := by rw [vec_add_self, add_zero]
      rw [opA_apply]
      simp only [Units.val_mul, Module.End.mul_apply] at h2 ⊢
      rw [h2, add_assoc, vec_add_self, add_zero]
    have hyinv : ((s * t) * (s * t)) * ((s * t) * (s * t)) = 1 :=
      (inv_iff _).2 fun v => by rw [hy, hy, hBA, map_zero]
    have hyne : (s * t) * (s * t) ≠ 1 := by
      intro h
      apply hv₀
      have := hy v₀
      rw [h, opA_apply] at this
      simpa [vec_add_self] using this.symm
    have hrk : Module.finrank (ZMod 2) ↥(LinearMap.range (opA ((s * t) * (s * t)))) ≤ 1 := by
      refine le_trans (Submodule.finrank_mono ?_) hAr
      rintro _ ⟨v, rfl⟩
      rw [hy]
      exact ⟨_, rfl⟩
    have := hrank _ hyL hyne hyinv
    omega
  · push_neg at hcase
    have hxinv : (s * t) * (s * t) = 1 := (inv_iff _).2 fun v => by rw [hxx, hcase]
    have hxne : s * t ≠ 1 := by
      intro h
      apply hne
      rw [eq_inv_of_mul_eq_one_left h]
      exact inv_eq_of_mul_eq_one_right ht
    have hrk : Module.finrank (ZMod 2) ↥(LinearMap.range (opA (s * t))) ≤ 2 := by
      have hle : LinearMap.range (opA (s * t)) ≤
          LinearMap.range (opA s) ⊔ LinearMap.range (opA t) := by
        rintro _ ⟨v, rfl⟩
        rw [hx, hcase, add_zero]
        exact add_mem (Submodule.mem_sup_left ⟨v, rfl⟩) (Submodule.mem_sup_right ⟨v, rfl⟩)
      calc _ ≤ Module.finrank (ZMod 2) ↥(LinearMap.range (opA s) ⊔ LinearMap.range (opA t)) :=
            Submodule.finrank_mono hle
        _ ≤ _ := Submodule.finrank_add_le_finrank_add_finrank _ _
        _ ≤ 2 := by omega
    have := hrank _ hst hxne hxinv
    omega


@[expose] def tvClass (L : Subgroup (Module.End (ZMod 2) V)ˣ) (b : (Module.End (ZMod 2) V)ˣ) :
    Set (Module.End (ZMod 2) V)ˣ := {t | ∃ g ∈ L, g * b * g⁻¹ = t}

theorem finite_units [Finite V] : Finite (Module.End (ZMod 2) V)ˣ := by
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have : Finite (Module.End (ZMod 2) V) := Module.finite_of_finite (ZMod 2)
  exact Finite.of_injective (fun x : (Module.End (ZMod 2) V)ˣ => x.val) Units.val_injective

theorem outer_transvection_core [Finite V] {L : Subgroup (Module.End (ZMod 2) V)ˣ}
    (hirr : ∀ U : Submodule (ZMod 2) V, (∀ g ∈ L, ∀ u ∈ U, g.val u ∈ U) → U = ⊥ ∨ U = ⊤)
    {b : (Module.End (ZMod 2) V)ˣ} (hbN : ∀ g ∈ L, b * g * b⁻¹ ∈ L) (hb2 : b * b = 1)
    (hbr : Module.finrank (ZMod 2) ↥(LinearMap.range (opA b)) = 1)
    (hrank : ∀ x ∈ L, x ≠ 1 → x * x = 1 → 5 ≤ Module.finrank (ZMod 2) ↥(LinearMap.range (opA x))) :
    Odd (Nat.card ↥(tvClass L b)) ∧ Module.finrank (ZMod 2) V ≤ Nat.card ↥(tvClass L b) ∧
      Nat.card ↥(tvClass L b) ≤ Module.finrank (ZMod 2) V + 1 := by
  classical
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have : Finite (Module.End (ZMod 2) V)ˣ := finite_units
  set D := tvClass L b with hD
  haveI : Fintype ↥D := Fintype.ofFinite _
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  obtain ⟨wb, hwb⟩ := tvW_exists hbr
  have hbD : b ∈ D := ⟨1, one_mem _, by simp⟩
  have hDinv : ∀ t ∈ D, t * t = 1 := by
    rintro _ ⟨g, hg, rfl⟩
    calc g * b * g⁻¹ * (g * b * g⁻¹) = g * (b * b) * g⁻¹ := by group
      _ = 1 := by rw [hb2]; group
  have hDtv : ∀ t ∈ D, ∃ w, TvW t w := by
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨_, tvW_conj g b hwb⟩
  have hDmul : ∀ s ∈ D, ∀ t ∈ D, s * t ∈ L := by
    rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩
    have e : g * b * g⁻¹ * (h * b * h⁻¹) = g * (b * (g⁻¹ * h) * b⁻¹) * h⁻¹ := by
      rw [hbi]; group
    rw [e]
    exact mul_mem (mul_mem hg (hbN _ (mul_mem (inv_mem hg) hh))) (inv_mem hh)
  have hDconj : ∀ g ∈ L, ∀ t ∈ D, g * t * g⁻¹ ∈ D := by
    rintro g hg _ ⟨h, hh, rfl⟩
    exact ⟨g * h, mul_mem hg hh, by group⟩
  let wOf : (Module.End (ZMod 2) V)ˣ → V := fun t => if h : ∃ w, TvW t w then h.choose else 0
  have hwOf : ∀ t, (∃ w, TvW t w) → TvW t (wOf t) := fun t h => by
    simp only [wOf, dif_pos h]
    exact h.choose_spec
  have hwOfconj : ∀ g t, (∃ w, TvW t w) → wOf (g * t * g⁻¹) = g.val (wOf t) := fun g t h =>
    tvW_unique (hwOf _ ⟨_, tvW_conj g t (hwOf t h)⟩) (tvW_conj g t (hwOf t h))
  let w : ↥D → V := fun t => wOf t.1
  have hwtv : ∀ t : ↥D, TvW t.1 (w t) := fun t => hwOf t.1 (hDtv t.1 t.2)
  have hwne : ∀ t, w t ≠ 0 := fun t => (hwtv t).1
  have hP' : ∀ s t : ↥D, s ≠ t → opA t.1 (w s) = w t := by
    intro s t hne
    have hne' : s.1 ≠ t.1 := fun h => hne (Subtype.ext h)
    have h1 := pair_ne hrank (hDinv s.1 s.2) (hDinv t.1 t.2) (hwtv s) (hwtv t) hne'
      (hDmul s.1 s.2 t.1 t.2)
    rcases (hwtv t).2.2 (w s) with h0 | h
    · exact absurd h0 h1
    · exact h
  have hP : ∀ s t : ↥D, s ≠ t → opA s.1 (w t) = w s := fun s t h => hP' t s h.symm
  have hself : ∀ t : ↥D, opA t.1 (w t) = 0 := by
    intro t
    obtain ⟨v, hv⟩ := (hwtv t).2.1
    show opA t.1 (w t) = 0
    rw [← hv]
    exact opA_sq t.1 (hDinv _ t.2) v
  have hinj : Function.Injective w := by
    intro s t h
    by_contra hne
    have h1 := hP s t hne
    rw [← h, hself s] at h1
    exact hwne s h1.symm
  let U := Submodule.span (ZMod 2) (Set.range w)
  have hUstable : ∀ g ∈ L, ∀ u ∈ U, g.val u ∈ U := by
    intro g hg u hu
    refine Submodule.span_induction (p := fun u _ => g.val u ∈ U) ?_ ?_ ?_ ?_ hu
    · rintro _ ⟨t, rfl⟩
      have : g.val (w t) = w ⟨g * t.1 * g⁻¹, hDconj g hg t.1 t.2⟩ :=
        (hwOfconj g t.1 (hDtv t.1 t.2)).symm
      rw [this]
      exact Submodule.subset_span ⟨_, rfl⟩
    · simp
    · intro x y _ _ hx hy
      rw [map_add]
      exact add_mem hx hy
    · intro a x _ hx
      rw [map_smul]
      exact Submodule.smul_mem _ _ hx
  have hUtop : U = ⊤ := (hirr U hUstable).resolve_left (fun h => by
    have : w ⟨b, hbD⟩ ∈ U := Submodule.subset_span ⟨_, rfl⟩
    rw [h] at this
    exact hwne ⟨b, hbD⟩ ((Submodule.mem_bot _).1 this))
  have hd_le : Module.finrank (ZMod 2) V ≤ Fintype.card ↥D := by
    have := finrank_range_le_card (R := ZMod 2) w
    rw [← finrank_top (ZMod 2) V, ← hUtop]
    exact this
  have hrel : ∀ c : ↥D → ZMod 2, ∑ t, c t • w t = 0 → ∀ s, (∑ t, c t) = c s := by
    intro c hc s
    have h1 : opA s.1 (∑ t, c t • w t) = 0 := by rw [hc, map_zero]
    have h2 : opA s.1 (∑ t, c t • w t) = (∑ t ∈ Finset.univ.erase s, c t) • w s := by
      rw [map_sum]
      simp_rw [map_smul]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s), hself s, smul_zero, zero_add,
        Finset.sum_smul]
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [hP s t (Finset.ne_of_mem_erase ht).symm]
    have h3 : (∑ t ∈ Finset.univ.erase s, c t) = 0 := by
      rw [h1] at h2
      exact (smul_eq_zero.1 h2.symm).resolve_right (hwne s)
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s), h3, add_zero]
  have hupper : Fintype.card ↥D ≤ Module.finrank (ZMod 2) V + 1 := by
    set t₀ : ↥D := ⟨b, hbD⟩ with ht₀
    have hli : LinearIndependent (ZMod 2) (fun i : {t : ↥D // t ≠ t₀} => w i.1) := by
      rw [Fintype.linearIndependent_iff]
      intro g hg i
      let c : ↥D → ZMod 2 := fun t => if h : t ≠ t₀ then g ⟨t, h⟩ else 0
      have hc : ∑ t, c t • w t = 0 := by
        have e1 : ∑ t ∈ Finset.univ.erase t₀, c t • w t = ∑ t, c t • w t :=
          Finset.sum_erase _ (by simp [c])
        rw [← e1, Finset.sum_subtype (Finset.univ.erase t₀) (p := fun t => t ≠ t₀)
          (fun t => by simp)]
        rw [← hg]
        refine Finset.sum_congr rfl fun x _ => ?_
        simp [c, x.2]
      have h0 := hrel c hc t₀
      have hz : c t₀ = 0 := by simp [c]
      have := hrel c hc i.1
      rw [h0, hz] at this
      simpa [c, i.2] using this.symm
    have hcard := hli.fintype_card_le_finrank
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq] at hcard
    omega
  have hodd : Odd (Fintype.card ↥D) := by
    have hpos : 0 < Fintype.card ↥D := Fintype.card_pos_iff.2 ⟨⟨b, hbD⟩⟩
    by_cases h1 : Fintype.card ↥D = 1
    · rw [h1]; exact odd_one
    have hlt : 1 < Fintype.card ↥D := by omega
    obtain ⟨s, hs⟩ := Fintype.exists_ne_of_one_lt_card hlt ⟨b, hbD⟩
    set t : ↥D := ⟨b, hbD⟩ with ht
    set m : ZMod 2 := ((Fintype.card ↥D - 1 : ℕ) : ZMod 2) with hm
    set u : V := ∑ r, w r with hu
    have hopA : ∀ r : ↥D, opA r.1 u = m • w r := by
      intro r
      show opA r.1 (∑ q, w q) = _
      rw [map_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ r), hself r, zero_add]
      rw [Finset.sum_congr rfl (fun q hq => hP r q (Finset.ne_of_mem_erase hq).symm), Finset.sum_const,
        Finset.card_erase_of_mem (Finset.mem_univ r), Finset.card_univ, hm,
        Nat.cast_smul_eq_nsmul]
    have hfix : ∀ g ∈ L, g.val u = u := by
      intro g hg
      let e : ↥D ≃ ↥D :=
        { toFun := fun r => ⟨g * r.1 * g⁻¹, hDconj g hg r.1 r.2⟩
          invFun := fun r => ⟨g⁻¹ * r.1 * g, by
            have := hDconj g⁻¹ (inv_mem hg) r.1 r.2
            simpa using this⟩
          left_inv := fun r => Subtype.ext (by simp [mul_assoc])
          right_inv := fun r => Subtype.ext (by simp [mul_assoc]) }
      show g.val (∑ r, w r) = ∑ r, w r
      rw [map_sum]
      calc ∑ r, g.val (w r) = ∑ r, w (e r) := by
            refine Finset.sum_congr rfl fun r _ => ?_
            exact (hwOfconj g r.1 (hDtv r.1 r.2)).symm
        _ = ∑ r, w r := Equiv.sum_comp e w
    have hx := hfix (s.1 * t.1) (hDmul s.1 s.2 t.1 t.2)
    have hts : t.1.val u = m • w t + u := by
      rw [app_eq, hopA t]
    have hsw : s.1.val (w t) = w s + w t := by
      rw [app_eq, hP s t hs]
    have hsu : s.1.val u = m • w s + u := by
      rw [app_eq, hopA s]
    have hx2 : (s.1 * t.1).val u = m • w t + u := by
      simp only [Units.val_mul, Module.End.mul_apply]
      rw [hts, map_add, map_smul, hsw, hsu, smul_add]
      calc m • w s + m • w t + (m • w s + u) = (m • w s + m • w s) + m • w t + u := by abel
        _ = m • w t + u := by rw [vec_add_self, zero_add]
    have hm0 : m • w t = 0 := by
      have := hx2.symm.trans hx
      simpa using this
    have hmz : m = 0 := (smul_eq_zero.1 hm0).resolve_right (hwne t)
    have h2 : 2 ∣ Fintype.card ↥D - 1 := by
      rw [hm] at hmz
      exact (ZMod.natCast_eq_zero_iff _ _).1 hmz
    obtain ⟨k, hk⟩ := h2
    exact ⟨k, by omega⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [Nat.card_eq_fintype_card]; exact hodd
  · rw [Nat.card_eq_fintype_card]; exact hd_le
  · rw [Nat.card_eq_fintype_card]; exact hupper

end Core

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc
