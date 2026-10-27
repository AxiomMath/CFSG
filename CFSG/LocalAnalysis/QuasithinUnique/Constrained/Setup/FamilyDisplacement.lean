module

public import Mathlib.Algebra.GCDMonoid.FinsetLemmas
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Action.Concrete
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Semisimple
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
public import Mathlib.Topology.Sheaves.Presheaf
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.QuasithinUnique.Setup.Family

open Module
open scoped IsMulCommutative

theorem simple_cyclic_card {S : Type*} [AddCommGroup S] [Module (ZMod 2) S] [Finite S]
    [Nontrivial S] (γ : Module.End (ZMod 2) S) (hfin : IsOfFinOrder γ)
    (hsimple : ∀ T : Submodule (ZMod 2) S, (∀ s ∈ T, γ s ∈ T) → T = ⊥ ∨ T = ⊤) :
    Nat.card S = 2 ^ orderOf (2 : ZMod (orderOf γ)) := by
  classical
  have hγunit : γ ^ (orderOf γ - 1) * γ = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos_iff.2 hfin), pow_orderOf_eq_one]
  have hγinj : Function.Injective γ := by
    intro a b hab
    have := congrArg (fun s => (γ ^ (orderOf γ - 1)) s) hab
    simpa [← Module.End.mul_apply, hγunit] using this
  let A0 : Subalgebra (ZMod 2) (Module.End (ZMod 2) S) := Algebra.adjoin (ZMod 2) {γ}
  have hc : IsMulCommutative A0 :=
    Algebra.isMulCommutative_adjoin (ZMod 2) (s := ({γ} : Set (Module.End (ZMod 2) S)))
      (Set.pairwise_singleton _ _)
  have hcomm : ∀ a b : A0, a * b = b * a := fun a b => mul_comm a b
  have hfinA : Finite A0 := by
    have : Finite (Module.End (ZMod 2) S) :=
      Finite.of_injective (fun f : Module.End (ZMod 2) S => (f : S → S)) DFunLike.coe_injective
    infer_instance
  have hγmem : γ ∈ A0 := Algebra.subset_adjoin rfl
  let γA : A0 := ⟨γ, hγmem⟩
  have hker : ∀ a : A0, a ≠ 0 → LinearMap.ker (a : Module.End (ZMod 2) S) = ⊥ := by
    intro a ha
    have hinv : ∀ s ∈ LinearMap.ker (a : Module.End (ZMod 2) S),
        γ s ∈ LinearMap.ker (a : Module.End (ZMod 2) S) := by
      intro s hs
      rw [LinearMap.mem_ker] at hs ⊢
      have h1 := congrArg (fun f : A0 => (f : Module.End (ZMod 2) S) s) (hcomm a γA)
      simp only [Subalgebra.coe_mul, Module.End.mul_apply] at h1
      have h2 : (γA : Module.End (ZMod 2) S) = γ := rfl
      rw [h2] at h1
      rw [h1, hs, map_zero]
    rcases hsimple _ hinv with h | h
    · exact h
    · exfalso
      apply ha
      apply Subtype.ext
      ext s
      have : s ∈ LinearMap.ker (a : Module.End (ZMod 2) S) := by rw [h]; trivial
      simpa using this
  have hinj : ∀ a : A0, a ≠ 0 → Function.Injective (a : Module.End (ZMod 2) S) := fun a ha =>
    LinearMap.ker_eq_bot.1 (hker a ha)
  have hnzd : NoZeroDivisors A0 := by
    refine ⟨fun {a b} hab => ?_⟩
    by_cases ha : a = 0
    · exact Or.inl ha
    right
    apply Subtype.ext
    ext s
    have h1 := congrArg (fun f : A0 => (f : Module.End (ZMod 2) S) s) hab
    simp only [Subalgebra.coe_mul, Module.End.mul_apply] at h1
    have : (a : Module.End (ZMod 2) S) ((b : Module.End (ZMod 2) S) s) =
        (a : Module.End (ZMod 2) S) 0 := by
      rw [map_zero]; simpa using h1
    simpa using hinj a ha this
  have hnt : Nontrivial A0 := ⟨⟨0, 1, fun h => by
    obtain ⟨s, hs⟩ := exists_ne (0 : S)
    have := LinearMap.congr_fun (congrArg Subtype.val h) s
    simp at this
    exact hs this.symm⟩⟩
  have : IsDomain A0 := NoZeroDivisors.to_isDomain A0
  have : Fintype A0 := Fintype.ofFinite A0
  let _ : Field A0 := (Finite.isField_of_domain A0).toField
  have hchar : CharP A0 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) A0).injective 2
  have _hS : Fintype S := Fintype.ofFinite S
  obtain ⟨v, hv⟩ := exists_ne (0 : S)
  let ev : A0 →ₗ[ZMod 2] S := (LinearMap.applyₗ v).comp A0.val.toLinearMap
  have hev_apply : ∀ a : A0, ev a = (a : Module.End (ZMod 2) S) v := fun a => rfl
  have hev_inj : Function.Injective ev := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    by_contra hne
    have h0 : (a : Module.End (ZMod 2) S) v = (a : Module.End (ZMod 2) S) 0 := by
      rw [map_zero]; simpa [hev_apply] using ha
    exact hv (hinj a hne h0)
  have hev_surj : Function.Surjective ev := by
    have hinv : ∀ s ∈ LinearMap.range ev, γ s ∈ LinearMap.range ev := by
      rintro _ ⟨a, rfl⟩
      refine ⟨γA * a, ?_⟩
      rw [hev_apply, hev_apply]
      simp [γA]
    rcases hsimple _ hinv with h | h
    · exfalso
      have : ev 1 ∈ LinearMap.range ev := ⟨1, rfl⟩
      rw [h, Submodule.mem_bot, hev_apply] at this
      exact hv (by simpa using this)
    · exact LinearMap.range_eq_top.1 h
  have hcardS : Nat.card S = Fintype.card A0 := by
    rw [Nat.card_eq_fintype_card]
    exact (Fintype.card_of_bijective ⟨hev_inj, hev_surj⟩).symm
  have hord : orderOf γA = orderOf γ :=
    (orderOf_injective (A0.val : A0 →ₐ[ZMod 2] Module.End (ZMod 2) S).toRingHom.toMonoidHom
      Subtype.val_injective γA).symm ▸ rfl
  set n := orderOf γ with hn
  obtain ⟨e, -, he⟩ := FiniteField.card A0 2
  have hγA0 : γA ≠ 0 := by
    intro h
    have := congrArg (fun f : A0 => (f : Module.End (ZMod 2) S) v) h
    simp only [γA, ZeroMemClass.coe_zero, LinearMap.zero_apply] at this
    exact hv (hγinj (by rw [this, map_zero]))
  have hlag : γA ^ (Fintype.card A0 - 1) = 1 := FiniteField.pow_card_sub_one_eq_one γA hγA0
  have hn_dvd : n ∣ 2 ^ (e : ℕ) - 1 := by
    rw [← hord, ← he]
    exact orderOf_dvd_of_pow_eq_one hlag
  have hpow2 : (2 : ZMod n) ^ (e : ℕ) = 1 := by
    have h1 : ((2 ^ (e : ℕ) - 1 : ℕ) : ZMod n) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hn_dvd
    rw [Nat.cast_sub Nat.one_le_two_pow] at h1
    push_cast at h1
    exact sub_eq_zero.1 h1
  set o := orderOf (2 : ZMod n) with ho
  have hodvd : o ∣ (e : ℕ) := orderOf_dvd_of_pow_eq_one hpow2
  have hope : 0 < o := Nat.pos_of_dvd_of_pos hodvd e.pos
  have hole : o ≤ (e : ℕ) := Nat.le_of_dvd e.pos hodvd
  have hpowo : (2 : ZMod n) ^ o = 1 := pow_orderOf_eq_one _
  have hdvd_o : n ∣ 2 ^ o - 1 := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub Nat.one_le_two_pow]
    push_cast
    rw [hpowo, sub_self]
  have hγfix : γ ^ (2 ^ o) = γ := by
    have h1 : γ ^ (2 ^ o - 1) = 1 := orderOf_dvd_iff_pow_eq_one.1 hdvd_o
    calc γ ^ (2 ^ o) = γ ^ (2 ^ o - 1 + 1) := by rw [Nat.sub_add_cancel Nat.one_le_two_pow]
      _ = γ := by rw [pow_succ, h1, one_mul]
  have hcharE : CharP (Module.End (ZMod 2) S) 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) (Module.End (ZMod 2) S)).injective 2
  have hfrob : ∀ x ∈ Algebra.adjoin (ZMod 2) ({γ} : Set (Module.End (ZMod 2) S)),
      x ^ (2 ^ o) = x := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      rw [hx]; exact hγfix
    | algebraMap r =>
      rw [← map_pow, ZMod.pow_card_pow]
    | add x y hx hy ihx ihy =>
      have hxy : Commute x y := congrArg Subtype.val (hcomm ⟨x, hx⟩ ⟨y, hy⟩)
      rw [add_pow_char_pow_of_commute 2 o hxy, ihx, ihy]
    | mul x y hx hy ihx ihy =>
      have hxy : Commute x y := congrArg Subtype.val (hcomm ⟨x, hx⟩ ⟨y, hy⟩)
      rw [Commute.mul_pow hxy, ihx, ihy]
  have hcardle : Fintype.card A0 ≤ 2 ^ o := by
    have hp1 : 1 < 2 ^ o := Nat.one_lt_two_pow hope.ne'
    have hdeg : (Polynomial.X ^ (2 ^ o) - Polynomial.X : Polynomial A0).natDegree = 2 ^ o :=
      FiniteField.X_pow_card_sub_X_natDegree_eq A0 hp1
    have hp0 : (Polynomial.X ^ (2 ^ o) - Polynomial.X : Polynomial A0) ≠ 0 := by
      intro h
      rw [h] at hdeg
      simp at hdeg
      exact (Nat.two_pow_pos o).ne' hdeg.symm
    have hroots : (Finset.univ : Finset A0).val ⊆
        (Polynomial.X ^ (2 ^ o) - Polynomial.X : Polynomial A0).roots := by
      intro a _
      rw [Polynomial.mem_roots hp0]
      simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
      refine sub_eq_zero.2 (Subtype.ext ?_)
      simpa using hfrob (a : Module.End (ZMod 2) S) a.2
    have := Polynomial.card_le_degree_of_subset_roots hroots
    rw [hdeg] at this
    simpa using this
  have hee : (e : ℕ) ≤ o := by
    have : 2 ^ (e : ℕ) ≤ 2 ^ o := by rw [← he]; exact hcardle
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
  have : (e : ℕ) = o := le_antisymm hee hole
  rw [hcardS, he, this]

theorem four_dvd_of_dvd_four_mul {o n : ℕ} (h4 : o ∣ 4 * n) (h2 : ¬ o ∣ 2 * n) :
    ∃ d, o = 4 * d ∧ d ∣ n := by
  obtain ⟨a, b, ha, hb, hab⟩ := Nat.dvd_mul.1 h4
  have ha' : a ∈ Nat.divisors 4 := by simp [ha]
  have hdiv : Nat.divisors 4 = {1, 2, 4} := by decide
  rw [hdiv] at ha'
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha'
  rcases ha' with rfl | rfl | rfl
  · exfalso; apply h2
    rw [← hab, one_mul]
    exact hb.mul_left 2
  · exfalso; apply h2
    rw [← hab]
    exact Nat.mul_dvd_mul_left 2 hb
  · exact ⟨b, hab.symm, hb⟩

theorem order_two_quartic {n N : ℕ} (hn : Odd n) (hN : N ∣ 2 ^ (2 * n) + 1) (hN1 : N ≠ 1) :
    ∃ d, orderOf (2 : ZMod N) = 4 * d ∧ d ∣ n ∧ N ∣ 2 ^ (2 * d) + 1 := by
  have hev : Even (2 ^ (2 * n)) := even_two.pow_of_ne_zero (by have := hn.pos; omega)
  have hNodd : Odd N := Odd.of_dvd_nat hev.add_one hN
  have hcast : (2 : ZMod N) ^ (2 * n) = -1 := by
    have h := (ZMod.natCast_eq_zero_iff _ _).2 hN
    push_cast at h
    exact eq_neg_of_add_eq_zero_left h
  have h4n : (2 : ZMod N) ^ (4 * n) = 1 := by
    calc (2 : ZMod N) ^ (4 * n) = ((2 : ZMod N) ^ (2 * n)) ^ 2 := by ring
      _ = 1 := by rw [hcast]; norm_num
  have hnot : ¬ (2 : ZMod N) ^ (2 * n) = 1 := by
    intro h
    rw [hcast] at h
    have h2 : ((2 : ℕ) : ZMod N) = 0 := by
      have : (1 : ZMod N) + 1 = 0 := by
        nth_rewrite 1 [← h]
        ring
      push_cast
      rw [← this]
      norm_num
    have hN2 : N ∣ 2 := (ZMod.natCast_eq_zero_iff _ _).1 h2
    have : N ≤ 2 := Nat.le_of_dvd (by norm_num) hN2
    have hpos : 0 < N := hNodd.pos
    interval_cases N
    · exact hN1 rfl
    · exact absurd hNodd (by decide)
  have hdvd4 : orderOf (2 : ZMod N) ∣ 4 * n := orderOf_dvd_of_pow_eq_one h4n
  have hndvd2 : ¬ orderOf (2 : ZMod N) ∣ 2 * n := fun h => hnot (orderOf_dvd_iff_pow_eq_one.1 h)
  obtain ⟨d, hod, hdn⟩ := four_dvd_of_dvd_four_mul hdvd4 hndvd2
  refine ⟨d, hod, hdn, ?_⟩
  obtain ⟨j, hj⟩ := hdn
  have hjodd : Odd j := by
    have : Odd (d * j) := hj ▸ hn
    exact (Nat.odd_mul.1 this).2
  obtain ⟨i, hi⟩ := hjodd
  have h4d : (2 : ZMod N) ^ (4 * d) = 1 := by
    rw [← hod]; exact pow_orderOf_eq_one _
  have h2d : (2 : ZMod N) ^ (2 * d) = -1 := by
    have : 2 * n = 2 * d + 4 * d * i := by rw [hj, hi]; ring
    rw [← hcast, this, pow_add, pow_mul (2 : ZMod N) (4 * d) i, h4d, one_pow, mul_one]
  have : ((2 ^ (2 * d) + 1 : ℕ) : ZMod N) = 0 := by
    push_cast
    rw [h2d]; ring
  exact (ZMod.natCast_eq_zero_iff _ _).1 this

theorem prod_one_add_le (D : Finset ℕ) (f : ℕ → ℝ) (hf : ∀ d ∈ D, 0 ≤ f d)
    (hsum : ∑ d ∈ D, f d ≤ 1 / 2) : ∏ d ∈ D, (1 + f d) ≤ 1 + 2 * ∑ d ∈ D, f d := by
  classical
  induction D using Finset.induction_on with
  | empty => simp
  | insert a D ha ih =>
    rw [Finset.prod_insert ha]
    rw [Finset.sum_insert ha] at hsum ⊢
    have hfa : 0 ≤ f a := hf a (Finset.mem_insert_self a D)
    have hfD : ∀ d ∈ D, 0 ≤ f d := fun d hd => hf d (Finset.mem_insert_of_mem hd)
    have hsD : 0 ≤ ∑ d ∈ D, f d := Finset.sum_nonneg hfD
    have hsumD : ∑ d ∈ D, f d ≤ 1 / 2 := by linarith
    have h1 := ih hfD hsumD
    calc (1 + f a) * ∏ d ∈ D, (1 + f d) ≤ (1 + f a) * (1 + 2 * ∑ d ∈ D, f d) := by gcongr
      _ ≤ 1 + 2 * (f a + ∑ d ∈ D, f d) := by
        nlinarith [mul_nonneg hfa (by linarith : 0 ≤ 1 - 2 * ∑ d ∈ D, f d)]

theorem geom_sum_Icc_quarter (M : ℕ) :
    ∑ d ∈ Finset.Icc 1 M, ((1 : ℝ) / 4) ^ d = (1 - ((1 : ℝ) / 4) ^ M) / 3 := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, pow_succ]
    ring

theorem sum_quarter_le {D : Finset ℕ} (hD : ∀ d ∈ D, 0 < d) :
    ∑ d ∈ D, ((1 : ℝ) / 4) ^ d ≤ 1 / 3 := by
  calc ∑ d ∈ D, ((1 : ℝ) / 4) ^ d ≤ ∑ d ∈ Finset.Icc 1 (D.sup id), ((1 : ℝ) / 4) ^ d := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro d hd
          rw [Finset.mem_Icc]
          exact ⟨hD d hd, Finset.le_sup (f := id) hd⟩
        · intros; positivity
    _ = (1 - ((1 : ℝ) / 4) ^ (D.sup id)) / 3 := geom_sum_Icc_quarter _
    _ ≤ 1 / 3 := by
        have : (0 : ℝ) ≤ ((1 : ℝ) / 4) ^ (D.sup id) := by positivity
        linarith

theorem prod_four_pow_add_one_lt (D : Finset ℕ) (hD : ∀ d ∈ D, 0 < d) :
    ∏ d ∈ D, (4 ^ d + 1) < 2 * 4 ^ (∑ d ∈ D, d) := by
  have hσ := sum_quarter_le hD
  have hprod := prod_one_add_le D (fun d => ((1 : ℝ) / 4) ^ d) (fun d _ => by positivity)
    (by linarith)
  have hreal : ((∏ d ∈ D, (4 ^ d + 1) : ℕ) : ℝ) =
      4 ^ (∑ d ∈ D, d) * ∏ d ∈ D, (1 + ((1 : ℝ) / 4) ^ d) := by
    push_cast
    rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun d _ => ?_
    have h4 : (4 : ℝ) ^ d * ((1 : ℝ) / 4) ^ d = 1 := by
      rw [← mul_pow]; norm_num
    rw [mul_add, mul_one, h4, add_comm]
  have : ((∏ d ∈ D, (4 ^ d + 1) : ℕ) : ℝ) < 2 * 4 ^ (∑ d ∈ D, d) := by
    rw [hreal]
    have h4 : (0 : ℝ) < 4 ^ (∑ d ∈ D, d) := by positivity
    nlinarith [hprod, hσ]
  exact_mod_cast this

theorem isSemisimple_of_pow_eq_one {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (x : Module.End (ZMod 2) W) {K : ℕ} (hK : Odd K) (hx : x ^ K = 1) :
    Module.End.IsSemisimple x := by
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (p := (Polynomial.X ^ K - Polynomial.C 1 : Polynomial (ZMod 2))) ?_ ?_
  · refine (Polynomial.separable_X_pow_sub_C 1 ?_ one_ne_zero).squarefree
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => (Nat.not_even_iff_odd.2 hK) (even_iff_two_dvd.2 h)
  · simp [hx]

theorem pow_apply_eq_self_of_mul {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (x : Module.End (ZMod 2) W) {a : ℕ} {w : W} (h : (x ^ a) w = w) (q : ℕ) :
    (x ^ (a * q)) w = w := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.mul_succ, pow_add, Module.End.mul_apply, h, ih]

theorem displacement_simple {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    {n : ℕ} (hn : Odd n) (x : Module.End (ZMod 2) W) (hx : x ^ (2 ^ (2 * n) + 1) = 1)
    (p : Submodule (ZMod 2) W) (hp : ∀ w ∈ p, x w ∈ p) (hp0 : p ≠ ⊥)
    (hsimp : ∀ S : Submodule (ZMod 2) W, S ≤ p → (∀ w ∈ S, x w ∈ S) → S = ⊥ ∨ S = p) :
    ∃ D : Finset ℕ, (∀ d ∈ D, 0 < d ∧ d ∣ n) ∧
        4 ∣ finrank (ZMod 2) (p.map (x - 1)) ∧
        4 * ∑ d ∈ D, d ≤ finrank (ZMod 2) (p.map (x - 1)) ∧
        ∀ w ∈ p, (x ^ (D.lcm fun d => 2 ^ (2 * d) + 1)) w = w := by
  classical
  have hnt : Nontrivial ↥p := Submodule.nontrivial_iff_ne_bot.2 hp0
  let γ : Module.End (ZMod 2) ↥p := x.restrict hp
  have hγapp : ∀ w : ↥p, ((γ w : ↥p) : W) = x w := fun w => rfl
  have hγpow_apply : ∀ (k : ℕ) (w : ↥p), (((γ ^ k) w : ↥p) : W) = (x ^ k) w := by
    intro k
    induction k with
    | zero => intro w; simp
    | succ k ih =>
      intro w
      rw [pow_succ, Module.End.mul_apply, ih, hγapp, pow_succ, Module.End.mul_apply]
  have hγK : γ ^ (2 ^ (2 * n) + 1) = 1 :=
    LinearMap.ext fun w => Subtype.ext (by rw [hγpow_apply, hx]; rfl)
  have hfinord : IsOfFinOrder γ :=
    isOfFinOrder_iff_pow_eq_one.2 ⟨2 ^ (2 * n) + 1, Nat.succ_pos _, hγK⟩
  have hγsimple : ∀ T : Submodule (ZMod 2) ↥p, (∀ s ∈ T, γ s ∈ T) → T = ⊥ ∨ T = ⊤ := by
    intro T hT
    have hTx : ∀ w ∈ T.map p.subtype, x w ∈ T.map p.subtype := by
      rintro _ ⟨s, hs, rfl⟩
      exact ⟨γ s, hT s hs, rfl⟩
    rcases hsimp (T.map p.subtype) (by rintro _ ⟨s, _, rfl⟩; exact s.2) hTx with h | h
    · left
      apply Submodule.map_injective_of_injective p.injective_subtype
      rw [h, Submodule.map_bot]
    · right
      apply Submodule.map_injective_of_injective p.injective_subtype
      rw [h, Submodule.map_subtype_top]
  have hcard := simple_cyclic_card γ hfinord hγsimple
  by_cases hfix : ∀ w ∈ p, x w = w
  · have hbot : p.map (x - 1) = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨w, hw, rfl⟩
      simp [hfix w hw]
    refine ⟨∅, by simp, ?_, ?_, ?_⟩
    · rw [hbot, finrank_bot]; exact dvd_zero 4
    · rw [hbot, finrank_bot]; simp
    · intro w hw
      simpa using hfix w hw
  · have hinj : ∀ w ∈ p, (x - 1) w = 0 → w = 0 := by
      intro w hw h0
      have hSinv : ∀ v ∈ p ⊓ LinearMap.ker (x - 1), x v ∈ p ⊓ LinearMap.ker (x - 1) := by
        rintro v ⟨hvp, hvk⟩
        have hvk' : (x - 1) v = 0 := LinearMap.mem_ker.1 hvk
        refine ⟨hp v hvp, LinearMap.mem_ker.2 ?_⟩
        have h1 : (x - 1) (x v) = x ((x - 1) v) := by simp
        rw [h1, hvk', map_zero]
      rcases hsimp _ inf_le_left hSinv with h | h
      · have : w ∈ p ⊓ LinearMap.ker (x - 1) := ⟨hw, h0⟩
        rw [h] at this
        exact this
      · exfalso
        apply hfix
        intro v hv
        have : v ∈ p ⊓ LinearMap.ker (x - 1) := by rw [h]; exact hv
        have h2 : (x - 1) v = 0 := LinearMap.mem_ker.1 this.2
        simpa [sub_eq_zero] using h2
    have hinj' : Function.Injective ((x - 1).domRestrict p) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro w hw
      apply Subtype.ext
      exact hinj w w.2 hw
    have hrk : finrank (ZMod 2) (p.map (x - 1)) = finrank (ZMod 2) p := by
      rw [← LinearMap.range_domRestrict, LinearMap.finrank_range_of_inj hinj']
    have hcard2 : Nat.card ↥p = 2 ^ finrank (ZMod 2) ↥p := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    have hfo : finrank (ZMod 2) ↥p = orderOf (2 : ZMod (orderOf γ)) :=
      Nat.pow_right_injective (le_refl 2) (hcard2.symm.trans hcard)
    have hpos : 1 ≤ finrank (ZMod 2) ↥p := Submodule.one_le_finrank_iff.2 hp0
    have hNK : orderOf γ ∣ 2 ^ (2 * n) + 1 := orderOf_dvd_of_pow_eq_one hγK
    have hN1 : orderOf γ ≠ 1 := by
      intro h1
      apply hfix
      intro w hw
      have hγ1 : γ = 1 := orderOf_eq_one_iff.1 h1
      have := congrArg (fun f : Module.End (ZMod 2) ↥p => ((f ⟨w, hw⟩ : ↥p) : W)) hγ1
      simpa [hγapp] using this
    obtain ⟨d, hd4, hdn, hdN⟩ := order_two_quartic hn hNK hN1
    have hdpos : 0 < d := by omega
    refine ⟨{d}, ?_, ?_, ?_, ?_⟩
    · intro d' hd'
      rw [Finset.mem_singleton] at hd'
      subst hd'
      exact ⟨hdpos, hdn⟩
    · rw [hrk, hfo, hd4]; exact dvd_mul_right 4 d
    · rw [hrk, hfo, hd4]; simp
    · intro w hw
      have hL : (({d} : Finset ℕ).lcm fun d => 2 ^ (2 * d) + 1) = 2 ^ (2 * d) + 1 := by
        simp
      rw [hL]
      have hγL : γ ^ (2 ^ (2 * d) + 1) = 1 := orderOf_dvd_iff_pow_eq_one.1 hdN
      have := congrArg (fun f : Module.End (ZMod 2) ↥p => ((f ⟨w, hw⟩ : ↥p) : W)) hγL
      simpa [hγpow_apply] using this

theorem displacement_decomposition {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    {n : ℕ} (hn : Odd n) (x : Module.End (ZMod 2) W) (hx : x ^ (2 ^ (2 * n) + 1) = 1) :
    ∀ p : Submodule (ZMod 2) W, (∀ w ∈ p, x w ∈ p) →
      ∃ D : Finset ℕ, (∀ d ∈ D, 0 < d ∧ d ∣ n) ∧
        4 ∣ finrank (ZMod 2) (p.map (x - 1)) ∧
        4 * ∑ d ∈ D, d ≤ finrank (ZMod 2) (p.map (x - 1)) ∧
        ∀ w ∈ p, (x ^ (D.lcm fun d => 2 ^ (2 * d) + 1)) w = w := by
  classical
  have hKodd : Odd (2 ^ (2 * n) + 1) :=
    (even_two.pow_of_ne_zero (by have := hn.pos; omega)).add_one
  have hsemi := isSemisimple_of_pow_eq_one x hKodd hx
  have hfs := hsemi.isFinitelySemisimple
  suffices H : ∀ k : ℕ, ∀ p : Submodule (ZMod 2) W, finrank (ZMod 2) p = k →
      (∀ w ∈ p, x w ∈ p) →
      ∃ D : Finset ℕ, (∀ d ∈ D, 0 < d ∧ d ∣ n) ∧
        4 ∣ finrank (ZMod 2) (p.map (x - 1)) ∧
        4 * ∑ d ∈ D, d ≤ finrank (ZMod 2) (p.map (x - 1)) ∧
        ∀ w ∈ p, (x ^ (D.lcm fun d => 2 ^ (2 * d) + 1)) w = w from
    fun p hp => H _ p rfl hp
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro p hpk hp
    by_cases hsplit : ∃ S : Submodule (ZMod 2) W, S ≤ p ∧ (∀ w ∈ S, x w ∈ S) ∧ S ≠ ⊥ ∧ S ≠ p
    · obtain ⟨S, hSp, hSx, hS0, hSp'⟩ := hsplit
      have hpinv : p ∈ Module.End.invtSubmodule x := by
        rw [Module.End.mem_invtSubmodule]; intro w hw; exact hp w hw
      have hSinv : S ∈ Module.End.invtSubmodule x := by
        rw [Module.End.mem_invtSubmodule]; intro w hw; exact hSx w hw
      obtain ⟨r, hrp, hrinv, hdisj, hsup⟩ :=
        Module.End.isFinitelySemisimple_iff.1 hfs p hpinv inferInstance S hSinv hSp
      have hrx : ∀ w ∈ r, x w ∈ r := by
        rw [Module.End.mem_invtSubmodule] at hrinv; exact fun w hw => hrinv hw
      have hfin : finrank (ZMod 2) p = finrank (ZMod 2) S + finrank (ZMod 2) r := by
        have := Submodule.finrank_sup_add_finrank_inf_eq S r
        rw [hsup, disjoint_iff.1 hdisj, finrank_bot] at this
        omega
      have hr0 : r ≠ ⊥ := by
        rintro rfl
        apply hSp'; rw [← hsup]; simp
      have hSpos : 1 ≤ finrank (ZMod 2) S := Submodule.one_le_finrank_iff.2 hS0
      have hrpos : 1 ≤ finrank (ZMod 2) r := Submodule.one_le_finrank_iff.2 hr0
      obtain ⟨DS, hDS1, hDS2, hDS3, hDS4⟩ := ih _ (by omega) S rfl hSx
      obtain ⟨Dr, hDr1, hDr2, hDr3, hDr4⟩ := ih _ (by omega) r rfl hrx
      have hsub : ∀ T : Submodule (ZMod 2) W, (∀ w ∈ T, x w ∈ T) → T.map (x - 1) ≤ T := by
        rintro T hT _ ⟨w, hw, rfl⟩
        have : (x - 1) w = x w - w := by simp
        rw [this]
        exact T.sub_mem (hT w hw) hw
      have hrk : finrank (ZMod 2) (p.map (x - 1)) =
          finrank (ZMod 2) (S.map (x - 1)) + finrank (ZMod 2) (r.map (x - 1)) := by
        rw [← hsup, Submodule.map_sup]
        have hdisj' : Disjoint (S.map (x - 1)) (r.map (x - 1)) :=
          Disjoint.mono (hsub S hSx) (hsub r hrx) hdisj
        have := Submodule.finrank_sup_add_finrank_inf_eq (S.map (x - 1)) (r.map (x - 1))
        rw [disjoint_iff.1 hdisj', finrank_bot] at this
        omega
      refine ⟨DS ∪ Dr, ?_, ?_, ?_, ?_⟩
      · intro d hd
        rcases Finset.mem_union.1 hd with h | h
        · exact hDS1 d h
        · exact hDr1 d h
      · rw [hrk]; exact dvd_add hDS2 hDr2
      · rw [hrk]
        have := Finset.sum_union_inter (s₁ := DS) (s₂ := Dr) (f := fun d => d)
        have h0 : 0 ≤ ∑ d ∈ DS ∩ Dr, d := Nat.zero_le _
        omega
      · intro w hw
        rw [← hsup] at hw
        obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.1 hw
        have hLS : DS.lcm (fun d => 2 ^ (2 * d) + 1) ∣
            (DS ∪ Dr).lcm (fun d => 2 ^ (2 * d) + 1) := by
          rw [Finset.lcm_union]; exact dvd_lcm_left _ _
        have hLr : Dr.lcm (fun d => 2 ^ (2 * d) + 1) ∣
            (DS ∪ Dr).lcm (fun d => 2 ^ (2 * d) + 1) := by
          rw [Finset.lcm_union]; exact dvd_lcm_right _ _
        obtain ⟨qS, hqS⟩ := hLS
        obtain ⟨qr, hqr⟩ := hLr
        have h1 : (x ^ ((DS ∪ Dr).lcm (fun d => 2 ^ (2 * d) + 1))) s = s := by
          rw [hqS]; exact pow_apply_eq_self_of_mul x (hDS4 s hs) qS
        have h2 : (x ^ ((DS ∪ Dr).lcm (fun d => 2 ^ (2 * d) + 1))) t = t := by
          rw [hqr]; exact pow_apply_eq_self_of_mul x (hDr4 t ht) qr
        rw [map_add, h1, h2]
    · have hsimp : ∀ S : Submodule (ZMod 2) W, S ≤ p → (∀ w ∈ S, x w ∈ S) → S = ⊥ ∨ S = p := by
        intro S hSp hSx
        by_contra hcon
        exact hsplit ⟨S, hSp, hSx, fun h => hcon (Or.inl h), fun h => hcon (Or.inr h)⟩
      by_cases hp0 : p = ⊥
      · subst hp0
        refine ⟨∅, by simp, ?_, ?_, ?_⟩
        · rw [Submodule.map_bot, finrank_bot]
          exact dvd_zero 4
        · rw [Submodule.map_bot, finrank_bot]
          simp
        · intro w hw
          rw [Submodule.mem_bot] at hw
          simp [hw]
      · exact displacement_simple hn x hx p hp hp0 hsimp

theorem odd_quartic_displacement_rank_bound {n : ℕ} (hn : Odd n) {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] [Finite W] (x : W ≃ₗ[ZMod 2] W) (hx : orderOf x ∣ 2 ^ (2 * n) + 1) :
    4 ∣ finrank (ZMod 2) (LinearMap.range ((x : W →ₗ[ZMod 2] W) - 1)) ∧
    ∃ D : Finset ℕ, (∀ d ∈ D, 0 < d ∧ d ∣ n) ∧
      4 * ∑ d ∈ D, d ≤ finrank (ZMod 2) (LinearMap.range ((x : W →ₗ[ZMod 2] W) - 1)) ∧
      orderOf x ∣ D.lcm (fun d => 2 ^ (2 * d) + 1) := by
  classical
  let ι : (W ≃ₗ[ZMod 2] W) →* Module.End (ZMod 2) W :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom
  have hι : Function.Injective ι := LinearEquiv.toLinearMap_injective
  have hxK : (ι x) ^ (2 ^ (2 * n) + 1) = 1 := by
    rw [← map_pow, orderOf_dvd_iff_pow_eq_one.1 hx, map_one]
  obtain ⟨D, hD1, hD2, hD3, hD4⟩ :=
    displacement_decomposition hn (ι x) hxK ⊤ (fun _ _ => trivial)
  have hmap : (⊤ : Submodule (ZMod 2) W).map (ι x - 1) =
      LinearMap.range ((x : W →ₗ[ZMod 2] W) - 1) := by
    rw [← LinearMap.range_eq_map]; rfl
  rw [hmap] at hD2 hD3
  refine ⟨hD2, D, hD1, hD3, ?_⟩
  apply orderOf_dvd_of_pow_eq_one
  apply hι
  rw [map_pow, map_one]
  exact LinearMap.ext fun w => hD4 w trivial

theorem odd_quartic_order_lt {n : ℕ} (hn : Odd n) {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] [Finite W] (x : W ≃ₗ[ZMod 2] W) (hx : orderOf x ∣ 2 ^ (2 * n) + 1)
    (hR : finrank (ZMod 2) (LinearMap.range ((x : W →ₗ[ZMod 2] W) - 1)) ≤ 2 * n) :
    orderOf x < 2 ^ n := by
  obtain ⟨-, D, hD1, hD2, hD3⟩ := odd_quartic_displacement_rank_bound hn x hx
  have hprodpos : 0 < ∏ d ∈ D, (4 ^ d + 1) := Finset.prod_pos fun d _ => by positivity
  have hdvd : orderOf x ∣ ∏ d ∈ D, (4 ^ d + 1) := by
    refine hD3.trans ((Finset.lcm_dvd_prod D _).trans ?_)
    refine Finset.prod_dvd_prod_of_dvd _ _ fun d _ => ?_
    rw [pow_mul]; norm_num
  have hle : orderOf x ≤ ∏ d ∈ D, (4 ^ d + 1) := Nat.le_of_dvd hprodpos hdvd
  have hlt := prod_four_pow_add_one_lt D fun d hd => (hD1 d hd).1
  set s := ∑ d ∈ D, d with hs
  have h2s : 2 * s + 1 ≤ n := by
    obtain ⟨k, hk⟩ := hn
    omega
  calc orderOf x < 2 * 4 ^ s := lt_of_le_of_lt hle hlt
    _ = 2 ^ (2 * s + 1) := by rw [pow_succ, pow_mul]; norm_num; ring
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h2s

theorem odd_quartic_rank_ge {n : ℕ} (hn : Odd n) {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] [Finite W] (x : W ≃ₗ[ZMod 2] W) (hx : orderOf x ∣ 2 ^ (2 * n) + 1)
    (hm : 2 ^ n ≤ orderOf x) :
    2 * n + 2 ≤ finrank (ZMod 2) (LinearMap.range ((x : W →ₗ[ZMod 2] W) - 1)) := by
  obtain ⟨h4, -⟩ := odd_quartic_displacement_rank_bound hn x hx
  by_contra hcon
  have hR : finrank (ZMod 2) (LinearMap.range ((x : W →ₗ[ZMod 2] W) - 1)) ≤ 2 * n := by
    obtain ⟨k, hk⟩ := h4
    omega
  exact absurd (odd_quartic_order_lt hn x hx hR) (not_lt.2 hm)

theorem finrank_range_conj {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (e : W ≃ₗ[ZMod 2] W) (f : W →ₗ[ZMod 2] W) :
    finrank (ZMod 2) (LinearMap.range ((e : W →ₗ[ZMod 2] W) ∘ₗ f ∘ₗ (e.symm : W →ₗ[ZMod 2] W))) =
      finrank (ZMod 2) (LinearMap.range f) := by
  rw [LinearMap.range_comp, LinearEquiv.range_comp]
  exact LinearEquiv.finrank_map_eq e _

theorem finrank_range_sub_one_conj {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : G →* (W ≃ₗ[ZMod 2] W)) (g a : G) :
    finrank (ZMod 2) (LinearMap.range ((ρ (g * a * g⁻¹) : W →ₗ[ZMod 2] W) - 1)) =
      finrank (ZMod 2) (LinearMap.range ((ρ a : W →ₗ[ZMod 2] W) - 1)) := by
  have h : (ρ (g * a * g⁻¹) : W →ₗ[ZMod 2] W) - 1 =
      (ρ g : W →ₗ[ZMod 2] W) ∘ₗ ((ρ a : W →ₗ[ZMod 2] W) - 1) ∘ₗ ((ρ g).symm : W →ₗ[ZMod 2] W) := by
    ext w
    simp [map_mul, map_inv]
  rw [h]
  exact finrank_range_conj (ρ g) _

theorem finrank_range_sub_one_mul_le {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W] (ρ : G →* (W ≃ₗ[ZMod 2] W)) (t y : G) :
    finrank (ZMod 2) (LinearMap.range ((ρ (t * y) : W →ₗ[ZMod 2] W) - 1)) ≤
      finrank (ZMod 2) (LinearMap.range ((ρ y : W →ₗ[ZMod 2] W) - 1)) +
        finrank (ZMod 2) (LinearMap.range ((ρ t : W →ₗ[ZMod 2] W) - 1)) := by
  have h : (ρ (t * y) : W →ₗ[ZMod 2] W) - 1 =
      (ρ t : W →ₗ[ZMod 2] W) ∘ₗ ((ρ y : W →ₗ[ZMod 2] W) - 1) + ((ρ t : W →ₗ[ZMod 2] W) - 1) := by
    ext w
    simp [map_mul]
  rw [h]
  have h1 : LinearMap.range ((ρ t : W →ₗ[ZMod 2] W) ∘ₗ ((ρ y : W →ₗ[ZMod 2] W) - 1) +
      ((ρ t : W →ₗ[ZMod 2] W) - 1)) ≤
      LinearMap.range ((ρ t : W →ₗ[ZMod 2] W) ∘ₗ ((ρ y : W →ₗ[ZMod 2] W) - 1)) ⊔
        LinearMap.range ((ρ t : W →ₗ[ZMod 2] W) - 1) := LinearMap.range_add_le _ _
  have h2 : finrank (ZMod 2) (LinearMap.range ((ρ t : W →ₗ[ZMod 2] W) ∘ₗ
      ((ρ y : W →ₗ[ZMod 2] W) - 1))) =
      finrank (ZMod 2) (LinearMap.range ((ρ y : W →ₗ[ZMod 2] W) - 1)) := by
    rw [LinearMap.range_comp]
    exact LinearEquiv.finrank_map_eq (ρ t) _
  calc _ ≤ finrank (ZMod 2) ↥(LinearMap.range ((ρ t : W →ₗ[ZMod 2] W) ∘ₗ
        ((ρ y : W →ₗ[ZMod 2] W) - 1)) ⊔ LinearMap.range ((ρ t : W →ₗ[ZMod 2] W) - 1)) :=
        Submodule.finrank_mono h1
    _ ≤ _ := by
      have := Submodule.finrank_add_le_finrank_add_finrank
        (LinearMap.range ((ρ t : W →ₗ[ZMod 2] W) ∘ₗ ((ρ y : W →ₗ[ZMod 2] W) - 1)))
        (LinearMap.range ((ρ t : W →ₗ[ZMod 2] W) - 1))
      rw [h2] at this
      exact this

theorem quartic_torus_involution_rank {n : ℕ} (hn : Odd n) {G : Type*} [Group G]
    (hconj : ∀ a b : G, orderOf a = 2 → orderOf b = 2 → IsConj a b)
    {x t : G} (ht : orderOf t = 2) (htx : t * x * t⁻¹ = x⁻¹)
    (hxm : orderOf x ∣ 2 ^ (2 * n) + 1) (hm : 2 ^ n ≤ orderOf x)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : G →* (W ≃ₗ[ZMod 2] W)) (hρ : Function.Injective ρ) :
    ∀ a : G, orderOf a = 2 →
      n + 1 ≤ finrank (ZMod 2) (LinearMap.range ((ρ a : W →ₗ[ZMod 2] W) - 1)) := by
  intro a ha
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htt : t * t = 1 := by rw [← pow_two, ← ht]; exact pow_orderOf_eq_one t
  have hodd : Odd (2 ^ (2 * n) + 1) :=
    (even_two.pow_of_ne_zero (by have := hn.pos; omega)).add_one
  have hxodd : Odd (orderOf x) := Odd.of_dvd_nat hodd hxm
  have htx2 : (t * x) * (t * x) = 1 := by
    calc t * x * (t * x) = (t * x * t⁻¹) * (t * t) * x := by group
      _ = 1 := by rw [htx, htt]; group
  have htx1 : t * x ≠ 1 := by
    intro h
    have hx' : x = t⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [hx', orderOf_inv, ht] at hxodd
    exact absurd hxodd (by decide)
  have ho2 : orderOf (t * x) = 2 := orderOf_eq_prime (by rw [pow_two]; exact htx2) htx1
  have hrt : finrank (ZMod 2) (LinearMap.range ((ρ t : W →ₗ[ZMod 2] W) - 1)) =
      finrank (ZMod 2) (LinearMap.range ((ρ a : W →ₗ[ZMod 2] W) - 1)) := by
    obtain ⟨c, hc⟩ := isConj_iff.1 (hconj a t ha ht)
    rw [← hc, finrank_range_sub_one_conj]
  have hrtx : finrank (ZMod 2) (LinearMap.range ((ρ (t * x) : W →ₗ[ZMod 2] W) - 1)) =
      finrank (ZMod 2) (LinearMap.range ((ρ a : W →ₗ[ZMod 2] W) - 1)) := by
    obtain ⟨c, hc⟩ := isConj_iff.1 (hconj a (t * x) ha ho2)
    rw [← hc, finrank_range_sub_one_conj]
  have hord : orderOf (ρ x) = orderOf x := orderOf_injective ρ hρ x
  have hge := odd_quartic_rank_ge hn (ρ x) (by rw [hord]; exact hxm) (by rw [hord]; exact hm)
  have hle := finrank_range_sub_one_mul_le ρ t (t * x)
  have hxeq : t * (t * x) = x := by rw [← mul_assoc, htt, one_mul]
  rw [hxeq, hrt, hrtx] at hle
  omega

theorem quartic_torus_card_lt {n : ℕ} (hn : Odd n) {G : Type*} [Group G]
    (hconj : ∀ a b : G, orderOf a = 2 → orderOf b = 2 → IsConj a b)
    (hela : ∀ A : Subgroup G, (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → (∀ a ∈ A, a * a = 1) →
      Nat.card A ≤ 2 ^ n)
    {x t : G} (ht : orderOf t = 2) (htx : t * x * t⁻¹ = x⁻¹)
    (hxm : orderOf x ∣ 2 ^ (2 * n) + 1) (hm : 2 ^ n ≤ orderOf x)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : G →* (W ≃ₗ[ZMod 2] W)) (hρ : Function.Injective ρ) (A : Subgroup G) (hA0 : A ≠ ⊥)
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA2 : ∀ a ∈ A, a * a = 1) :
    Nat.card A * Nat.card {w : W // ∀ a ∈ A, ρ a w = w} < Nat.card W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a', ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hA0
  have haA : (a' : G) ∈ A := a'.2
  have ha : orderOf (a' : G) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hA2 _ haA) (fun h => ha1 (Subtype.ext h))
  have hrank := quartic_torus_involution_rank hn hconj ht htx hxm hm ρ hρ (a' : G) ha
  set f : W →ₗ[ZMod 2] W := (ρ (a' : G) : W →ₗ[ZMod 2] W) - 1 with hf
  have hnk := LinearMap.finrank_range_add_finrank_ker f
  have hcardW : Nat.card W = 2 ^ finrank (ZMod 2) W := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hcardK : Nat.card (LinearMap.ker f) = 2 ^ finrank (ZMod 2) (LinearMap.ker f) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hC : Nat.card {w : W // ∀ a ∈ A, ρ a w = w} ≤ Nat.card (LinearMap.ker f) := by
    refine Nat.card_le_card_of_injective
      (fun w => (⟨w.1, ?_⟩ : LinearMap.ker f)) ?_
    · rw [LinearMap.mem_ker, hf]
      have := w.2 (a' : G) haA
      simp [this]
    · intro u v huv
      have h1 := congrArg Subtype.val huv
      exact Subtype.ext h1
  have hAle := hela A hAc hA2
  have hpos : 0 < 2 ^ finrank (ZMod 2) (LinearMap.ker f) := Nat.two_pow_pos _
  rw [hcardW, ← hnk, pow_add]
  calc Nat.card A * Nat.card {w : W // ∀ a ∈ A, ρ a w = w}
      ≤ 2 ^ n * 2 ^ finrank (ZMod 2) (LinearMap.ker f) := by
        rw [← hcardK] at *
        exact Nat.mul_le_mul hAle hC
    _ < 2 ^ (n + 1) * 2 ^ finrank (ZMod 2) (LinearMap.ker f) := by
        apply Nat.mul_lt_mul_of_pos_right _ hpos
        exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    _ ≤ 2 ^ finrank (ZMod 2) (LinearMap.range f) * 2 ^ finrank (ZMod 2) (LinearMap.ker f) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hrank)

open scoped Pointwise in
theorem exists_conj_le_sylow_two {H : Type*} [Group H] [Finite H] (U : Sylow 2 H)
    (A : Subgroup H) (hA : ∀ a ∈ A, a * a = 1) :
    ∃ g : H, ∀ a ∈ A, g⁻¹ * a * g ∈ (U : Subgroup H) := by
  have hp : IsPGroup 2 A := by
    refine IsPGroup.iff_orderOf.2 fun a => ?_
    have h2 : (a : H) ^ 2 = 1 := by rw [pow_two]; exact hA a a.2
    have : orderOf (a : H) ∣ 2 ^ 1 := by simpa using orderOf_dvd_of_pow_eq_one h2
    obtain ⟨k, -, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 this
    exact ⟨k, by rw [← Subgroup.orderOf_coe]; exact hk'⟩
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H U P
  refine ⟨g, fun a ha => ?_⟩
  have h1 : a ∈ (P : Subgroup H) := hP ha
  rw [← hg] at h1
  have h2 : a ∈ MulAut.conj g • (U : Subgroup H) := h1
  rw [Subgroup.mem_smul_pointwise_iff_exists] at h2
  obtain ⟨u, hu, rfl⟩ := h2
  have : g⁻¹ * (MulAut.conj g • u) * g = u := by
    simp [MulAut.smul_def, MulAut.conj_apply, mul_assoc]
  rw [this]
  exact hu

theorem involutions_conjugate_of_sylow_two {H : Type*} [Group H] [Finite H] (U : Sylow 2 H)
    (Z : Subgroup H) (hZU : ∀ x ∈ (U : Subgroup H), x * x = 1 → x ∈ Z)
    (hZconj : ∀ z ∈ Z, z ≠ 1 → ∀ z' ∈ Z, z' ≠ 1 → IsConj z z') :
    ∀ a b : H, orderOf a = 2 → orderOf b = 2 → IsConj a b := by
  have key : ∀ a : H, orderOf a = 2 → ∃ g : H, g⁻¹ * a * g ∈ Z ∧ g⁻¹ * a * g ≠ 1 := by
    intro a ha
    have ha2 : a * a = 1 := by rw [← pow_two]; rw [← ha]; exact pow_orderOf_eq_one a
    obtain ⟨g, hg⟩ := exists_conj_le_sylow_two U (Subgroup.zpowers a) (by
      intro x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      have h2z : a ^ (2 : ℤ) = 1 := by
        exact_mod_cast (by rw [pow_two]; exact ha2 : a ^ 2 = 1)
      rw [← zpow_add, ← two_mul, zpow_mul, h2z, one_zpow])
    have hU : g⁻¹ * a * g ∈ (U : Subgroup H) := hg a (Subgroup.mem_zpowers a)
    have hsq : (g⁻¹ * a * g) * (g⁻¹ * a * g) = 1 := by
      calc (g⁻¹ * a * g) * (g⁻¹ * a * g) = g⁻¹ * (a * a) * g := by group
        _ = 1 := by rw [ha2]; group
    refine ⟨g, hZU _ hU hsq, ?_⟩
    intro h1
    have : a = 1 := by
      have := congrArg (fun x => g * x * g⁻¹) h1
      simpa [mul_assoc] using this
    rw [this] at ha
    simp at ha
  intro a b ha hb
  obtain ⟨g, hgZ, hg1⟩ := key a ha
  obtain ⟨h, hhZ, hh1⟩ := key b hb
  have hc : IsConj (g⁻¹ * a * g) (h⁻¹ * b * h) := hZconj _ hgZ hg1 _ hhZ hh1
  have h1 : IsConj a (g⁻¹ * a * g) := by
    rw [isConj_iff]
    exact ⟨g⁻¹, by simp [mul_assoc]⟩
  have h2 : IsConj (h⁻¹ * b * h) b := by
    rw [isConj_iff]
    exact ⟨h, by simp [mul_assoc]⟩
  exact (h1.trans hc).trans h2

theorem card_le_of_sylow_two {H : Type*} [Group H] [Finite H] (U : Sylow 2 H)
    (Z : Subgroup H) (hZU : ∀ x ∈ (U : Subgroup H), x * x = 1 → x ∈ Z)
    (A : Subgroup H) (hA : ∀ a ∈ A, a * a = 1) : Nat.card A ≤ Nat.card Z := by
  obtain ⟨g, hg⟩ := exists_conj_le_sylow_two U A hA
  have hle : A.map (MulAut.conj g⁻¹).toMonoidHom ≤ Z := by
    rintro _ ⟨a, ha, rfl⟩
    have hsq : (g⁻¹ * a * g) * (g⁻¹ * a * g) = 1 := by
      calc (g⁻¹ * a * g) * (g⁻¹ * a * g) = g⁻¹ * (a * a) * g := by group
        _ = 1 := by rw [hA a ha]; group
    refine hZU _ (hg a ha) hsq |> fun h => ?_
    simpa [MulAut.conj_apply] using h
  have hcard : Nat.card (A.map (MulAut.conj g⁻¹).toMonoidHom) = Nat.card A :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  rw [← hcard]
  exact Nat.card_le_card_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)

end CFSG.QuasithinUnique.Setup.Family
