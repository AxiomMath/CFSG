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
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
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

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

theorem card_modEq_one_of_pow_five {V : Type*} [Group V] [Finite V] (x : MulAut V)
    (hx5 : x ^ 5 = 1) (U : Subgroup V) (hxU : ∀ u ∈ U, x u ∈ U)
    (hfix : ∀ u ∈ U, x u = u → u = 1) : Nat.card U ≡ 1 [MOD 5] := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Fintype U := Fintype.ofFinite U
  let f : Function.End U := fun u => ⟨x u, hxU u u.2⟩
  have hpow : ∀ (n : ℕ) (u : U), ((f ^ n) u : V) = (x ^ n) u := by
    intro n
    induction n with
    | zero => intro u; rfl
    | succ n ih =>
      intro u
      have h1 : (f ^ (n + 1)) u = f ((f ^ n) u) := by
        change f^[n + 1] u = f (f^[n] u)
        exact Function.iterate_succ_apply' f n u
      rw [h1, pow_succ' x n, MulAut.mul_apply]
      exact congrArg x (ih u)
  have hf : f ^ 5 ^ 1 = 1 := by
    funext u
    apply Subtype.ext
    rw [pow_one, hpow, hx5]
    rfl
  have h := Equiv.Perm.card_fixedPoints_modEq (p := 5) (n := 1) hf
  have hfp : Function.fixedPoints f = {1} := by
    ext u
    simp only [Function.mem_fixedPoints, Function.IsFixedPt, Set.mem_singleton_iff]
    constructor
    · intro hu
      apply Subtype.ext
      exact hfix u u.2 (congrArg Subtype.val hu)
    · rintro rfl
      exact Subtype.ext (map_one x)
  have hcard : Fintype.card (Function.fixedPoints f) = 1 := by
    simp only [hfp]
    exact Fintype.card_unique
  rw [hcard] at h
  rwa [← Nat.card_eq_fintype_card] at h

theorem eq_bot_or_eq_of_card_eq_sixteen {V : Type*} [Group V] [Finite V] (x : MulAut V)
    (hx5 : x ^ 5 = 1) (W : Subgroup V) (hW : Nat.card W = 16)
    (hxfpf : ∀ w ∈ W, x w = w → w = 1) (U : Subgroup V) (hUW : U ≤ W)
    (hxU : ∀ u ∈ U, x u ∈ U) : U = ⊥ ∨ U = W := by
  have hmod := card_modEq_one_of_pow_five x hx5 U hxU (fun u hu hxu => hxfpf u (hUW hu) hxu)
  have hdvd : Nat.card U ∣ 16 := hW ▸ Subgroup.card_dvd_of_le hUW
  have hn : Nat.card U = 1 ∨ Nat.card U = 16 := by
    unfold Nat.ModEq at hmod
    generalize Nat.card U = n at *
    have hn : n ≤ 16 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases n <;> omega
  rcases hn with h | h
  · exact Or.inl (Subgroup.card_eq_one.1 h)
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge hUW (by rw [hW, h]))

private theorem mulAut_pow_succ_apply {V : Type*} [Group V] (x : MulAut V) (n : ℕ) (v : V) :
    (x ^ (n + 1)) v = x ((x ^ n) v) := by
  rw [pow_succ', MulAut.mul_apply]

private theorem frob_conj_apply {V : Type*} [Group V] {x y : MulAut V}
    (hyx : y * x * y⁻¹ = x ^ 3) (n : ℕ) (v : V) :
    y ((x ^ n) v) = (x ^ (3 * n)) (y v) := by
  have h1 : y * x ^ n * y⁻¹ = x ^ (3 * n) := by
    rw [← conj_pow, hyx, ← pow_mul]
  have h2 : y * x ^ n = x ^ (3 * n) * y := mul_inv_eq_iff_eq_mul.1 h1
  have h3 := congrArg (fun φ : MulAut V => φ v) h2
  simpa only [MulAut.mul_apply] using h3

private theorem zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

private theorem zmod_two_coord_aux :
    ∀ a b c d : ZMod 2, a + d = a → c + d = b → d = c → b + d = d → b = 0 ∧ c = 0 ∧ d = 0 := by
  decide

theorem fixed_vectors_of_frobenius20 {V : Type*} [CommGroup V] [Finite V]
    (hsq : ∀ a : V, a * a = 1)
    (W : Subgroup V) (hW : Nat.card W = 16)
    (x y : MulAut V) (hx5 : x ^ 5 = 1) (hxW : ∀ w ∈ W, x w ∈ W) (hyW : ∀ w ∈ W, y w ∈ W)
    (hxfpf : ∀ w ∈ W, x w = w → w = 1) (hyx : y * x * y⁻¹ = x ^ 3)
    (w₀ : V) (hw₀W : w₀ ∈ W) (hw₀1 : w₀ ≠ 1) (hw₀y : y w₀ = w₀) :
    ∀ w ∈ W, y w = w → w = 1 ∨ w = w₀ := by
  classical
  letI : Module (ZMod 2) (Additive V) :=
    AddCommGroup.zmodModule (n := 2) fun a => by
      rw [two_nsmul]
      exact hsq (Additive.toMul a)
  obtain ⟨g, hg⟩ : ∃ g : ℕ → V, ∀ n, g n = (x ^ n) w₀ := ⟨fun n => (x ^ n) w₀, fun _ => rfl⟩
  have hg0 : g 0 = w₀ := by rw [hg, pow_zero]; rfl
  have hgx : ∀ n, x (g n) = g (n + 1) := fun n => by
    rw [hg, hg, mulAut_pow_succ_apply]
  have hgper : ∀ n, g (n + 5) = g n := fun n => by
    rw [hg, hg, pow_add, hx5, mul_one]
  have hgy : ∀ n, y (g n) = g (3 * n) := fun n => by
    rw [hg, hg, frob_conj_apply hyx, hw₀y]
  have hgW : ∀ n, g n ∈ W := by
    intro n
    induction n with
    | zero => rw [hg0]; exact hw₀W
    | succ n ih => rw [← hgx]; exact hxW _ ih
  have hx0 : x (g 0) = g 1 := hgx 0
  have hx1 : x (g 1) = g 2 := hgx 1
  have hx2 : x (g 2) = g 3 := hgx 2
  have hx3 : x (g 3) = g 4 := hgx 3
  have hx4 : x (g 4) = g 0 := (hgx 4).trans (hgper 0)
  have hy0 : y (g 0) = g 0 := hgy 0
  have hy1 : y (g 1) = g 3 := hgy 1
  have hy2 : y (g 2) = g 1 := (hgy 2).trans (hgper 1)
  have hy3 : y (g 3) = g 4 := (hgy 3).trans (hgper 4)
  have hprod : g 0 * g 1 * g 2 * g 3 * g 4 = 1 := by
    refine hxfpf _
      (mul_mem (mul_mem (mul_mem (mul_mem (hgW 0) (hgW 1)) (hgW 2)) (hgW 3)) (hgW 4)) ?_
    rw [map_mul, map_mul, map_mul, map_mul, hx0, hx1, hx2, hx3, hx4]
    ac_rfl
  have hg4 : g 4 = g 0 * g 1 * g 2 * g 3 := by
    have h2 : (g 0 * g 1 * g 2 * g 3) * g 4 =
        (g 0 * g 1 * g 2 * g 3) * (g 0 * g 1 * g 2 * g 3) := by
      rw [hprod, hsq]
    exact mul_left_cancel h2
  obtain ⟨p, hp⟩ : ∃ p : ℕ → Additive V, ∀ n, p n = Additive.ofMul (g n) :=
    ⟨fun n => Additive.ofMul (g n), fun _ => rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : Additive V →ₗ[ZMod 2] Additive V,
      ∀ v : V, X (Additive.ofMul v) = Additive.ofMul (x v) :=
    ⟨AddMonoidHom.toZModLinearMap 2 (MulEquiv.toAdditive x).toAddMonoidHom, fun v => rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : Additive V →ₗ[ZMod 2] Additive V,
      ∀ v : V, Y (Additive.ofMul v) = Additive.ofMul (y v) :=
    ⟨AddMonoidHom.toZModLinearMap 2 (MulEquiv.toAdditive y).toAddMonoidHom, fun v => rfl⟩
  have hXp0 : X (p 0) = p 1 := by simp only [hp, hX, hx0]
  have hXp1 : X (p 1) = p 2 := by simp only [hp, hX, hx1]
  have hXp2 : X (p 2) = p 3 := by simp only [hp, hX, hx2]
  have hXp3 : X (p 3) = p 4 := by simp only [hp, hX, hx3]
  have hYp0 : Y (p 0) = p 0 := by simp only [hp, hY, hy0]
  have hYp1 : Y (p 1) = p 3 := by simp only [hp, hY, hy1]
  have hYp2 : Y (p 2) = p 1 := by simp only [hp, hY, hy2]
  have hYp3 : Y (p 3) = p 4 := by simp only [hp, hY, hy3]
  have hp4 : p 4 = p 0 + p 1 + p 2 + p 3 := by
    simp only [hp, hg4, ofMul_mul]
  obtain ⟨R, hR⟩ : ∃ R : Subgroup V, ∀ v : V, v ∈ R ↔
      ∃ a b c d : ZMod 2, Additive.ofMul v = a • p 0 + b • p 1 + c • p 2 + d • p 3 := by
    refine ⟨{ carrier := {v | ∃ a b c d : ZMod 2,
                Additive.ofMul v = a • p 0 + b • p 1 + c • p 2 + d • p 3}
              mul_mem' := ?_
              one_mem' := ?_
              inv_mem' := ?_ }, fun v => Iff.rfl⟩
    · rintro u v ⟨a, b, c, d, hu⟩ ⟨a', b', c', d', hv⟩
      refine ⟨a + a', b + b', c + c', d + d', ?_⟩
      rw [ofMul_mul, hu, hv]
      module
    · exact ⟨0, 0, 0, 0, by simp⟩
    · rintro u ⟨a, b, c, d, hu⟩
      refine ⟨a, b, c, d, ?_⟩
      rw [ofMul_inv, hu]
      exact neg_eq_of_add_eq_zero_right (hsq _)
  have hsmul : ∀ (a : ZMod 2) (n : ℕ), Additive.toMul (a • p n) ∈ W := by
    intro a n
    rcases zmod_two_cases a with rfl | rfl
    · rw [zero_smul]; exact one_mem W
    · rw [one_smul, hp]; exact hgW n
  have hRW : R ≤ W := by
    intro v hv
    obtain ⟨a, b, c, d, h⟩ := (hR v).1 hv
    have hv' : v = Additive.toMul (a • p 0) * Additive.toMul (b • p 1) *
        Additive.toMul (c • p 2) * Additive.toMul (d • p 3) := by
      have := congrArg Additive.toMul h
      simpa only [toMul_ofMul, toMul_add] using this
    rw [hv']
    exact mul_mem (mul_mem (mul_mem (hsmul _ _) (hsmul _ _)) (hsmul _ _)) (hsmul _ _)
  have hRx : ∀ u ∈ R, x u ∈ R := by
    intro u hu
    obtain ⟨a, b, c, d, hu⟩ := (hR u).1 hu
    refine (hR (x u)).2 ⟨d, a + d, b + d, c + d, ?_⟩
    rw [← hX, hu]
    simp only [map_add, map_smul, hXp0, hXp1, hXp2, hXp3, hp4]
    module
  have hw₀R : w₀ ∈ R := (hR w₀).2 ⟨1, 0, 0, 0, by simp [hp, hg0]⟩
  have hRW' : R = W := by
    rcases eq_bot_or_eq_of_card_eq_sixteen x hx5 W hW hxfpf R hRW hRx with hbot | h
    · exact absurd (by simpa [hbot] using hw₀R) hw₀1
    · exact h
  obtain ⟨ev, hev⟩ : ∃ ev : ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 → V, ∀ a b c d : ZMod 2,
      Additive.ofMul (ev (a, b, c, d)) = a • p 0 + b • p 1 + c • p 2 + d • p 3 :=
    ⟨fun t => Additive.toMul (t.1 • p 0 + t.2.1 • p 1 + t.2.2.1 • p 2 + t.2.2.2 • p 3),
      fun _ _ _ _ => rfl⟩
  have hevW : ∀ t, ev t ∈ W := fun ⟨a, b, c, d⟩ => hRW ((hR _).2 ⟨a, b, c, d, hev a b c d⟩)
  have hsurj : Function.Surjective (fun t => (⟨ev t, hevW t⟩ : W)) := by
    rintro ⟨w, hw⟩
    obtain ⟨a, b, c, d, h⟩ := (hR w).1 (by rw [hRW']; exact hw)
    exact ⟨(a, b, c, d), Subtype.ext (Additive.ofMul.injective (by rw [hev]; exact h.symm))⟩
  have hinj : Function.Injective (fun t => (⟨ev t, hevW t⟩ : W)) :=
    (hsurj.bijective_of_nat_card_le (by simp [hW])).1
  have hyev : ∀ a b c d : ZMod 2, y (ev (a, b, c, d)) = ev (a + d, c + d, d, b + d) := by
    intro a b c d
    apply Additive.ofMul.injective
    rw [← hY, hev, hev, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul,
      hYp0, hYp1, hYp2, hYp3, hp4]
    module
  intro w hw hyw
  obtain ⟨a, b, c, d, h⟩ := (hR w).1 (by rw [hRW']; exact hw)
  have hw_ev : w = ev (a, b, c, d) := Additive.ofMul.injective (by rw [hev]; exact h)
  have h1 : ev (a + d, c + d, d, b + d) = ev (a, b, c, d) := by
    rw [← hyev, ← hw_ev, hyw]
  have h2 := hinj (Subtype.ext h1)
  simp only [Prod.mk.injEq] at h2
  obtain ⟨e1, e2, e3, e4⟩ := h2
  obtain ⟨hb, hc, hd⟩ := zmod_two_coord_aux a b c d e1 e2 e3 e4
  subst hb hc hd
  rcases zmod_two_cases a with rfl | rfl
  · left
    rw [hw_ev]
    apply Additive.ofMul.injective
    rw [hev]
    simp
  · right
    rw [hw_ev]
    apply Additive.ofMul.injective
    rw [hev]
    simp [hp, hg0]

end CFSG.LocalAnalysis.EvenBN.Tits.N
