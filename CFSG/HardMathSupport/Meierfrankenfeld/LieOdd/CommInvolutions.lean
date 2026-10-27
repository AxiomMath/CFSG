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

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

noncomputable def nres (W : Submodule K V) (F : Finset (V →ₗ[K] V)) : ℕ := by
  classical exact (F.image fun f => (fun w : W => f (w : V))).card

theorem nres_le_two_pow (h2 : (2 : K) ≠ 0) :
    ∀ (n : ℕ) (W : Submodule K V) (F : Finset (V →ₗ[K] V)), finrank K W = n →
      (∀ f ∈ F, ∀ w ∈ W, f w ∈ W) → (∀ f ∈ F, ∀ w ∈ W, f (f w) = w) →
      (∀ f ∈ F, ∀ g ∈ F, ∀ v, f (g v) = g (f v)) → nres W F ≤ 2 ^ n := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro W F hn hmaps hinv hcomm
  by_cases hbase : ∀ f ∈ F, (∀ w ∈ W, f w = w) ∨ (∀ w ∈ W, f w = -w)
  ·
    by_cases hn0 : n = 0
    · subst hn0
      have hW : W = ⊥ := Submodule.finrank_eq_zero.1 hn
      have : (F.image fun f => (fun w : W => f (w : V))).card ≤ 1 := by
        refine Finset.card_le_one.2 fun a ha b hb => ?_
        obtain ⟨f, -, rfl⟩ := Finset.mem_image.1 ha
        obtain ⟨g, -, rfl⟩ := Finset.mem_image.1 hb
        funext w
        have h0 : ∀ x ∈ W, x = 0 := by
          intro x hx
          rw [hW] at hx
          exact (Submodule.mem_bot K).1 hx
        simp [h0 w w.2]
      unfold nres
      simpa using this
    · have : (F.image fun f => (fun w : W => f (w : V))).card ≤ 2 := by
        have hsub : (F.image fun f => (fun w : W => f (w : V))) ⊆
            {(fun w : W => (w : V)), (fun w : W => -(w : V))} := by
          intro r hr
          obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hr
          rcases hbase f hf with h | h
          · simp only [Finset.mem_insert, Finset.mem_singleton]
            left; funext w; exact h w w.2
          · simp only [Finset.mem_insert, Finset.mem_singleton]
            right; funext w; exact h w w.2
        exact (Finset.card_le_card hsub).trans Finset.card_le_two
      unfold nres
      calc _ ≤ 2 := this
        _ ≤ 2 ^ n := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  · push Not at hbase
    obtain ⟨f₀, hf₀, ⟨w₁, hw₁, hw₁'⟩, ⟨w₂, hw₂, hw₂'⟩⟩ := hbase
    set Wp : Submodule K V := W ⊓ LinearMap.ker (f₀ - LinearMap.id) with hWp
    set Wm : Submodule K V := W ⊓ LinearMap.ker (f₀ + LinearMap.id) with hWm
    have memp : ∀ w, w ∈ Wp ↔ w ∈ W ∧ f₀ w = w := fun w => by
      simp [hWp, LinearMap.mem_ker, sub_eq_zero]
    have memm : ∀ w, w ∈ Wm ↔ w ∈ W ∧ f₀ w = -w := fun w => by
      simp [hWm, LinearMap.mem_ker, add_eq_zero_iff_eq_neg]
    have hsup : Wp ⊔ Wm = W := by
      refine le_antisymm (sup_le inf_le_left inf_le_left) fun w hw => ?_
      have hw1 : (2⁻¹ : K) • (w + f₀ w) ∈ Wp := by
        rw [memp]
        refine ⟨W.smul_mem _ (W.add_mem hw (hmaps f₀ hf₀ w hw)), ?_⟩
        rw [map_smul, map_add, hinv f₀ hf₀ w hw, add_comm]
      have hw2 : (2⁻¹ : K) • (w - f₀ w) ∈ Wm := by
        rw [memm]
        refine ⟨W.smul_mem _ (W.sub_mem hw (hmaps f₀ hf₀ w hw)), ?_⟩
        rw [map_smul, map_sub, hinv f₀ hf₀ w hw, ← smul_neg, neg_sub]
      have : w = (2⁻¹ : K) • (w + f₀ w) + (2⁻¹ : K) • (w - f₀ w) := by
        rw [← smul_add, add_add_sub_cancel, ← two_smul K w, smul_smul, inv_mul_cancel₀ h2,
          one_smul]
      rw [this]
      exact Submodule.add_mem_sup hw1 hw2
    have hinf : Wp ⊓ Wm = ⊥ := by
      refine eq_bot_iff.2 fun w hw => ?_
      obtain ⟨h1, h2'⟩ := Submodule.mem_inf.1 hw
      rw [memp] at h1
      rw [memm] at h2'
      have : (2 : K) • w = 0 := by
        have := h1.2.symm.trans h2'.2
        calc (2 : K) • w = w - (-w) := by rw [two_smul]; abel
          _ = 0 := by rw [← this]; abel
      exact (Submodule.mem_bot K).2 ((smul_eq_zero.1 this).resolve_left h2)
    have hdim : finrank K Wp + finrank K Wm = n := by
      have := Submodule.finrank_sup_add_finrank_inf_eq Wp Wm
      rw [hsup, hinf, finrank_bot, hn] at this
      omega
    have hWpW : Wp < W := by
      refine lt_of_le_of_ne inf_le_left fun h => hw₁' ?_
      have : w₁ ∈ Wp := by rw [h]; exact hw₁
      exact ((memp w₁).1 this).2
    have hWmW : Wm < W := by
      refine lt_of_le_of_ne inf_le_left fun h => hw₂' ?_
      have : w₂ ∈ Wm := by rw [h]; exact hw₂
      exact ((memm w₂).1 this).2
    have hdp : finrank K Wp < n := hn ▸ Submodule.finrank_lt_finrank_of_lt hWpW
    have hdm : finrank K Wm < n := hn ▸ Submodule.finrank_lt_finrank_of_lt hWmW
    have hcomm0 : ∀ f ∈ F, ∀ v, f₀ (f v) = f (f₀ v) := fun f hf v => hcomm f₀ hf₀ f hf v
    have hmapsp : ∀ f ∈ F, ∀ w ∈ Wp, f w ∈ Wp := by
      intro f hf w hw
      obtain ⟨hwW, hwf⟩ := (memp w).1 hw
      exact (memp _).2 ⟨hmaps f hf w hwW, by rw [hcomm0 f hf, hwf]⟩
    have hmapsm : ∀ f ∈ F, ∀ w ∈ Wm, f w ∈ Wm := by
      intro f hf w hw
      obtain ⟨hwW, hwf⟩ := (memm w).1 hw
      exact (memm _).2 ⟨hmaps f hf w hwW, by rw [hcomm0 f hf, hwf, map_neg]⟩
    have h1 := ih _ hdp Wp F rfl hmapsp (fun f hf w hw => hinv f hf w (Submodule.mem_inf.1 hw).1) hcomm
    have h2' := ih _ hdm Wm F rfl hmapsm (fun f hf w hw => hinv f hf w (Submodule.mem_inf.1 hw).1) hcomm
    have hprod : nres W F ≤ nres Wp F * nres Wm F := by
      unfold nres
      rw [← Finset.card_product]
      refine Finset.card_le_card_of_injOn
        (fun r => ((fun w : Wp => r ⟨(w : V), hWpW.le w.2⟩),
          (fun w : Wm => r ⟨(w : V), hWmW.le w.2⟩))) ?_ ?_
      · intro r hr
        obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hr)
        simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe]
        exact ⟨Finset.mem_image.2 ⟨f, hf, rfl⟩, Finset.mem_image.2 ⟨f, hf, rfl⟩⟩
      · intro r hr r' hr' hrr
        obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hr)
        obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hr')
        obtain ⟨hp, hm⟩ := Prod.mk.inj hrr
        funext w
        have hwsup : (w : V) ∈ Wp ⊔ Wm := by rw [hsup]; exact w.2
        obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hwsup
        have e1 : f a = g a := congrFun hp ⟨a, ha⟩
        have e2 : f b = g b := congrFun hm ⟨b, hb⟩
        show f (w : V) = g (w : V)
        rw [← hab, map_add, map_add, e1, e2]
    calc nres W F ≤ nres Wp F * nres Wm F := hprod
      _ ≤ 2 ^ finrank K Wp * 2 ^ finrank K Wm := Nat.mul_le_mul h1 h2'
      _ = 2 ^ n := by rw [← pow_add, hdim]

theorem card_le_of_commuting_involutions (h2 : (2 : K) ≠ 0) (W : Submodule K V)
    (F : Finset (V →ₗ[K] V)) (hmaps : ∀ f ∈ F, ∀ w ∈ W, f w ∈ W)
    (hinv : ∀ f ∈ F, ∀ w ∈ W, f (f w) = w) (hcomm : ∀ f ∈ F, ∀ g ∈ F, ∀ v, f (g v) = g (f v))
    (hdist : ∀ f ∈ F, ∀ g ∈ F, (∀ w ∈ W, f w = g w) → f = g) : F.card ≤ 2 ^ finrank K W := by
  classical
  have h := nres_le_two_pow h2 _ W F rfl hmaps hinv hcomm
  have hinj : F.card = nres W F := by
    unfold nres
    rw [Finset.card_image_of_injOn]
    intro f hf g hg hfg
    refine hdist f hf g hg fun w hw => ?_
    exact congrFun hfg ⟨w, hw⟩
  rw [hinj]
  exact h

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
