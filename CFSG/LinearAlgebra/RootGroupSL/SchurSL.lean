module

public import Mathlib.LinearAlgebra.SpecialLinearGroup
import Mathlib.LinearAlgebra.Transvection.Basic

public section

namespace CFSG.LinearAlgebra.RootGroupSL

private theorem exists_smul_of_forall_mem_span_singleton {F W : Type} [Field F]
    [AddCommGroup W] [Module F W] [Module.Finite F W] (hW : 2 ≤ Module.finrank F W) (S : W →+ W)
    (h : ∀ w : W, ∃ a : F, S w = a • w) :
    ∃ s : F, ∀ w : W, S w = s • w := by
  classical
  choose a ha using h
  have key_indep : ∀ {v w : W}, LinearIndependent F ![v, w] → a v = a w := by
    intro v w hli
    have heq : a (v + w) • (v + w) = a v • v + a w • w := by
      rw [← ha (v + w), S.map_add, ha v, ha w]
    have hzero : (a (v + w) - a v) • v + (a (v + w) - a w) • w = 0 := by
      have hthis : (a (v + w) - a v) • v + (a (v + w) - a w) • w =
          (a (v + w) • v + a (v + w) • w) - (a v • v + a w • w) := by
        rw [sub_smul, sub_smul]
        abel
      rw [hthis, ← smul_add, heq, sub_self]
    obtain ⟨h1, h2⟩ :=
      LinearIndependent.pair_iff.mp hli (a (v + w) - a v) (a (v + w) - a w) hzero
    exact (sub_eq_zero.mp h1).symm.trans (sub_eq_zero.mp h2)
  have exists_out : ∀ v : W, v ≠ 0 → ∃ u : W, u ∉ F ∙ v := by
    intro v hv
    have hlt : F ∙ v < ⊤ := by
      apply Submodule.lt_top_of_finrank_lt_finrank
      rw [finrank_span_singleton hv]
      exact Nat.lt_of_lt_of_le (by norm_num) hW
    exact SetLike.exists_not_mem_of_ne_top (F ∙ v) (ne_of_lt hlt)
  have key : ∀ v w : W, v ≠ 0 → w ≠ 0 → a v = a w := by
    intro v w hv hw
    by_cases hli : LinearIndependent F ![v, w]
    · exact key_indep hli
    · have hwv : w ∈ F ∙ v := by
        by_contra hcon
        apply hli
        rw [LinearIndependent.pair_iff' hv]
        intro b hb
        exact hcon (Submodule.mem_span_singleton.mpr ⟨b, hb⟩)
      obtain ⟨u, hu⟩ := exists_out v hv
      have hvu : LinearIndependent F ![v, u] := by
        rw [LinearIndependent.pair_iff' hv]
        intro b hb
        exact hu (Submodule.mem_span_singleton.mpr ⟨b, hb⟩)
      have hwu : LinearIndependent F ![w, u] := by
        rw [LinearIndependent.pair_iff' hw]
        intro b hb
        apply hu
        rw [← hb]
        exact Submodule.smul_mem _ b hwv
      exact (key_indep hvu).trans (key_indep hwu).symm
  have hpos : 0 < Module.finrank F W := Nat.lt_of_lt_of_le (by norm_num) hW
  obtain ⟨u, hu⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  refine ⟨a u, fun w => ?_⟩
  by_cases hw : w = 0
  · subst hw
    rw [map_zero S]
    simp
  · rw [ha w, key w u hw hu]

theorem exists_smul_of_commute_specialLinear {F V : Type} [Field F] [AddCommGroup V]
    [Module F V] [Module.Finite F V] (hV : 2 ≤ Module.finrank F V) (S : V →+ V)
    (hS : ∀ (g : SpecialLinearGroup F V) (v : V), S (g v) = g (S v)) :
    ∃ s : F, ∀ v, S v = s • v := by
  classical
  have hspan : ∀ v : V, ∃ s : F, S v = s • v := by
    intro v
    by_cases hv : v = 0
    · exact ⟨0, by simp [hv]⟩
    · by_contra hcon
      have hmem : S v ∉ F ∙ v := by
        intro hmem
        obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hmem
        exact hcon ⟨s, hs.symm⟩
      obtain ⟨f₀, hf₀, hle⟩ := Submodule.exists_le_ker_of_notMem hmem
      have hf₀v : f₀ v = 0 := by
        apply hle
        exact Submodule.mem_span_singleton.mpr ⟨1, one_smul F v⟩
      set f : Module.Dual F V := (f₀ (S v))⁻¹ • f₀ with hf
      have hfv : f v = 0 := by
        rw [hf]
        change (f₀ (S v))⁻¹ • f₀ v = 0
        rw [hf₀v, smul_zero]
      have hfSv : f (S v) = 1 := by
        rw [hf]
        change (f₀ (S v))⁻¹ • f₀ (S v) = 1
        rw [smul_eq_mul]
        exact inv_mul_cancel₀ hf₀
      let g : SpecialLinearGroup F V :=
        ⟨LinearEquiv.transvection (f := f) (v := v) hfv,
          LinearEquiv.transvection.det_eq_one hfv⟩
      have hgv : g v = v := by
        change LinearEquiv.transvection (f := f) (v := v) hfv v = v
        simp only [LinearEquiv.transvection.apply, hfv, zero_smul, add_zero]
      have hgSv : g (S v) = S v + v := by
        change LinearEquiv.transvection (f := f) (v := v) hfv (S v) = S v + v
        simp only [LinearEquiv.transvection.apply, hfSv, one_smul]
      have hcomm := hS g v
      rw [hgv, hgSv] at hcomm
      exact hv (by
        have hzero : S v + 0 = S v + v := by rw [add_zero]; exact hcomm
        exact (add_left_cancel hzero).symm)
  exact exists_smul_of_forall_mem_span_singleton hV S hspan

theorem exists_smul_of_commute_specialLinear_dual {F V : Type} [Field F] [AddCommGroup V]
    [Module F V] [Module.Finite F V] (hV : 2 ≤ Module.finrank F V)
    (S : Module.Dual F V →+ Module.Dual F V)
    (hS : ∀ (g : SpecialLinearGroup F V) (f : Module.Dual F V),
      S (f ∘ₗ (SpecialLinearGroup.toLinearEquiv g⁻¹).toLinearMap) =
        S f ∘ₗ (SpecialLinearGroup.toLinearEquiv g⁻¹).toLinearMap) :
    ∃ s : F, ∀ f, S f = s • f := by
  classical
  have hspan : ∀ f : Module.Dual F V, ∃ c : F, S f = c • f := by
    intro f
    by_cases hf : f = 0
    · exact ⟨0, by simp [hf]⟩
    · have hker : LinearMap.ker f ≤ LinearMap.ker (S f) := by
        intro w hw
        rw [LinearMap.mem_ker] at hw ⊢
        by_cases hw0 : w = 0
        · rw [hw0, map_zero]
        · have hlt : F ∙ w < ⊤ := by
            apply Submodule.lt_top_of_finrank_lt_finrank
            rw [finrank_span_singleton hw0]
            exact Nat.lt_of_lt_of_le (by norm_num) hV
          obtain ⟨φ, hφne, hφle⟩ := Submodule.exists_le_ker_of_lt_top (F ∙ w) hlt
          have hφw : φ w = 0 := by
            apply hφle
            exact Submodule.mem_span_singleton.mpr ⟨1, one_smul F w⟩
          let g : SpecialLinearGroup F V :=
            ⟨LinearEquiv.transvection (f := φ) (v := w) hφw,
              LinearEquiv.transvection.det_eq_one hφw⟩
          have hginv_apply : ∀ x : V,
              (SpecialLinearGroup.toLinearEquiv g⁻¹) x = x - φ x • w := by
            intro x
            change ((g⁻¹ : SpecialLinearGroup F V) : V ≃ₗ[F] V) x = x - φ x • w
            rw [SpecialLinearGroup.coe_inv]
            change ((g : V ≃ₗ[F] V)⁻¹) x = x - φ x • w
            rw [show (g : V ≃ₗ[F] V) =
              LinearEquiv.transvection (f := φ) (v := w) hφw from rfl]
            rw [LinearEquiv.transvection.inv_eq hφw (by simp [hφw]),
              LinearEquiv.transvection.apply]
            simp [sub_eq_add_neg, smul_neg]
          have hcomp : f ∘ₗ (SpecialLinearGroup.toLinearEquiv g⁻¹).toLinearMap = f := by
            ext x
            change f ((SpecialLinearGroup.toLinearEquiv g⁻¹) x) = f x
            rw [hginv_apply x, map_sub, map_smul, hw, smul_zero, sub_zero]
          have hSg := hS g f
          rw [hcomp] at hSg
          obtain ⟨x, hx⟩ : ∃ x : V, φ x ≠ 0 := by
            by_contra hcon
            simp only [not_exists, not_not] at hcon
            exact hφne (LinearMap.ext hcon)
          have happ : ∀ y : V,
              ((S f) ∘ₗ (SpecialLinearGroup.toLinearEquiv g⁻¹).toLinearMap) y
                = (S f) y - φ y * (S f) w := by
            intro y
            change (S f) ((SpecialLinearGroup.toLinearEquiv g⁻¹) y)
              = (S f) y - φ y * (S f) w
            rw [hginv_apply y, map_sub, map_smul, smul_eq_mul]
          have hx_eq : (S f) x =
              ((S f) ∘ₗ (SpecialLinearGroup.toLinearEquiv g⁻¹).toLinearMap) x :=
            DFunLike.congr_fun hSg x
          rw [happ x] at hx_eq
          have hzero : φ x * (S f) w = 0 := sub_eq_self.mp hx_eq.symm
          rcases mul_eq_zero.mp hzero with h | h
          · exact absurd h hx
          · exact h
      obtain ⟨u, hu⟩ : ∃ u : V, f u = 1 := by
        obtain ⟨u, hu⟩ : ∃ u : V, f u ≠ 0 := by
          by_contra hcon
          simp only [not_exists, not_not] at hcon
          exact hf (LinearMap.ext hcon)
        exact ⟨(f u)⁻¹ • u, by
          rw [map_smul, smul_eq_mul]
          exact inv_mul_cancel₀ hu⟩
      refine ⟨(S f) u, ?_⟩
      ext x
      have hxf : x - f x • u ∈ LinearMap.ker f := by
        rw [LinearMap.mem_ker, map_sub, map_smul, hu, smul_eq_mul, mul_one, sub_self]
      have hxS : (S f) (x - f x • u) = 0 := by
        have := hker hxf
        rwa [LinearMap.mem_ker] at this
      have heq : (S f) x = f x * (S f) u := by
        rw [map_sub, map_smul, smul_eq_mul] at hxS
        exact sub_eq_zero.mp hxS
      show (S f) x = ((S f) u) • f x
      rw [heq, smul_eq_mul, mul_comm]
  have hdual_finrank : 2 ≤ Module.finrank F (Module.Dual F V) := by
    rw [Subspace.dual_finrank_eq]
    exact hV
  exact exists_smul_of_forall_mem_span_singleton hdual_finrank S hspan

end CFSG.LinearAlgebra.RootGroupSL
