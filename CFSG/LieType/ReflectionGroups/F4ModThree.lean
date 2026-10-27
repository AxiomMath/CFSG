module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.GroupTheory.Coxeter.Matrix
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.LieType.ReflectionGroups.F4ModThree

open Module

@[expose] def f4Cartan3 : Fin 4 → Fin 4 → ZMod 3 :=
  ![![2, -1, 0, 0], ![-1, 2, -2, 0], ![0, -1, 2, -1], ![0, 0, -1, 2]]

@[expose] def f4Refl3 (i : Fin 4) (v : Fin 4 → ZMod 3) : Fin 4 → ZMod 3 :=
  v - (∑ j, f4Cartan3 i j * v j) • Pi.single i 1

private def pairStep (p q α β : ZMod 3) (xy : ZMod 3 × ZMod 3) : ZMod 3 × ZMod 3 :=
  (xy.1 * (p * q - 1) + xy.2 * p - (β - p * α), -(xy.1 * q) - xy.2 - α)

private theorem pairStep_apply {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {s t : V ≃ₗ[ZMod 3] V} {a b : V} {f g : Dual (ZMod 3) V} (hfa : f a = 2) (hgb : g b = 2)
    (hs : ∀ v, s v = v - f v • a) (ht : ∀ v, t v = v - g v • b) (v : V) (x y : ZMod 3) :
    (s * t) (v + x • a + y • b) =
      v + (pairStep (f b) (g a) (g v) (f v) (x, y)).1 • a +
        (pairStep (f b) (g a) (g v) (f v) (x, y)).2 • b := by
  rw [LinearEquiv.mul_apply, ht, hs]
  simp only [pairStep, map_add, map_sub, map_smul, smul_eq_mul, hfa, hgb]
  module

private theorem pairStep_pow_apply {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {s t : V ≃ₗ[ZMod 3] V} {a b : V} {f g : Dual (ZMod 3) V} (hfa : f a = 2) (hgb : g b = 2)
    (hs : ∀ v, s v = v - f v • a) (ht : ∀ v, t v = v - g v • b) (n : ℕ) (v : V)
    (x y : ZMod 3) :
    ((s * t) ^ n) (v + x • a + y • b) =
      v + ((pairStep (f b) (g a) (g v) (f v))^[n] (x, y)).1 • a +
        ((pairStep (f b) (g a) (g v) (f v))^[n] (x, y)).2 • b := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', LinearEquiv.mul_apply, ih, Function.iterate_succ_apply']
    exact pairStep_apply hfa hgb hs ht v _ _

private theorem pairStep_pow_apply_zero {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {s t : V ≃ₗ[ZMod 3] V} {a b : V} {f g : Dual (ZMod 3) V} (hfa : f a = 2) (hgb : g b = 2)
    (hs : ∀ v, s v = v - f v • a) (ht : ∀ v, t v = v - g v • b) (n : ℕ) (x y : ZMod 3) :
    ((s * t) ^ n) (x • a + y • b) =
      ((pairStep (f b) (g a) 0 0)^[n] (x, y)).1 • a +
        ((pairStep (f b) (g a) 0 0)^[n] (x, y)).2 • b := by
  simpa only [zero_add, map_zero] using pairStep_pow_apply hfa hgb hs ht n 0 x y

private theorem pairStep_three :
    ∀ p q α β : ZMod 3, p * q = 1 → (pairStep p q α β)^[3] (0, 0) = (0, 0) := by
  decide +kernel

private theorem pairStep_zero_two :
    ∀ α β : ZMod 3, (pairStep 0 0 α β)^[2] (0, 0) = (0, 0) := by
  decide +kernel

private theorem pair_indep : ∀ p q x y : ZMod 3, p * q ≠ 1 → x * 2 + y * p = 0 →
    x * q + y * 2 = 0 → x = 0 ∧ y = 0 := by
  decide +kernel

private theorem pairStep_two : ∀ p q : ZMod 3, p * q ≠ 1 →
    (pairStep p q 0 0)^[2] (1, 0) = (1, 0) → (pairStep p q 0 0)^[2] (0, 1) = (0, 1) →
    p = 0 ∧ q = 0 := by
  decide +kernel

private theorem pairStep_three_ne : ∀ p q : ZMod 3, p * q ≠ 1 →
    (pairStep p q 0 0)^[3] (1, 0) ≠ (1, 0) := by
  decide +kernel

private theorem pairStep_four : ∀ p q : ZMod 3, p * q ≠ 1 →
    (pairStep p q 0 0)^[4] (1, 0) = (1, 0) → (pairStep p q 0 0)^[4] (0, 1) = (0, 1) →
    p * q = 2 ∨ p = 0 ∧ q = 0 := by
  decide +kernel

private theorem eq_of_smul_add_smul {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {a b : V}
    {f g : Dual (ZMod 3) V} (hfa : f a = 2) (hgb : g b = 2) (hpq : f b * g a ≠ 1)
    {x y x' y' : ZMod 3} (h : x • a + y • b = x' • a + y' • b) : x = x' ∧ y = y' := by
  have h0 : (x - x') • a + (y - y') • b = 0 := by
    linear_combination (norm := module) h
  have h1 := congrArg f h0
  have h2 := congrArg g h0
  simp only [map_add, map_smul, map_zero, smul_eq_mul, hfa, hgb] at h1 h2
  obtain ⟨hx, hy⟩ := pair_indep (f b) (g a) (x - x') (y - y') hpq h1 h2
  exact ⟨sub_eq_zero.mp hx, sub_eq_zero.mp hy⟩

private theorem pairStep_fix_fst {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {s t : V ≃ₗ[ZMod 3] V} {a b : V} {f g : Dual (ZMod 3) V} (hfa : f a = 2) (hgb : g b = 2)
    (hs : ∀ v, s v = v - f v • a) (ht : ∀ v, t v = v - g v • b) (hpq : f b * g a ≠ 1) (n : ℕ)
    (h : (s * t) ^ n = 1) : (pairStep (f b) (g a) 0 0)^[n] (1, 0) = (1, 0) := by
  have h1 := pairStep_pow_apply_zero hfa hgb hs ht n 1 0
  rw [h] at h1
  obtain ⟨e1, e2⟩ := eq_of_smul_add_smul hfa hgb hpq h1.symm
  exact Prod.ext e1 e2

private theorem pairStep_fix_snd {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {s t : V ≃ₗ[ZMod 3] V} {a b : V} {f g : Dual (ZMod 3) V} (hfa : f a = 2) (hgb : g b = 2)
    (hs : ∀ v, s v = v - f v • a) (ht : ∀ v, t v = v - g v • b) (hpq : f b * g a ≠ 1) (n : ℕ)
    (h : (s * t) ^ n = 1) : (pairStep (f b) (g a) 0 0)^[n] (0, 1) = (0, 1) := by
  have h1 := pairStep_pow_apply_zero hfa hgb hs ht n 0 1
  rw [h] at h1
  obtain ⟨e1, e2⟩ := eq_of_smul_add_smul hfa hgb hpq h1.symm
  exact Prod.ext e1 e2

private theorem pow_eq_one_of_pairStep {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {s t : V ≃ₗ[ZMod 3] V} {a b : V} {f g : Dual (ZMod 3) V} (hfa : f a = 2) (hgb : g b = 2)
    (hs : ∀ v, s v = v - f v • a) (ht : ∀ v, t v = v - g v • b) (n : ℕ)
    (hn : ∀ α β, (pairStep (f b) (g a) α β)^[n] (0, 0) = (0, 0)) : (s * t) ^ n = 1 := by
  ext w
  have := pairStep_pow_apply hfa hgb hs ht n w 0 0
  rw [hn] at this
  simpa using this

private theorem pair_two {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {s t : V ≃ₗ[ZMod 3] V} {a b : V} {f g : Dual (ZMod 3) V} (hfa : f a = 2) (hgb : g b = 2)
    (hs : ∀ v, s v = v - f v • a) (ht : ∀ v, t v = v - g v • b) (h : orderOf (s * t) = 2) :
    f b = 0 ∧ g a = 0 := by
  have h2 : (s * t) ^ 2 = 1 := by
    have := pow_orderOf_eq_one (s * t)
    rwa [h] at this
  have hne : s * t ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at h
    exact absurd h (by decide)
  by_cases hpq : f b * g a = 1
  · exfalso
    apply hne
    have h3 := pow_eq_one_of_pairStep hfa hgb hs ht 3
      (fun α β => pairStep_three (f b) (g a) α β hpq)
    rw [pow_succ, h2, one_mul] at h3
    exact h3
  · exact pairStep_two (f b) (g a) hpq (pairStep_fix_fst hfa hgb hs ht hpq 2 h2)
      (pairStep_fix_snd hfa hgb hs ht hpq 2 h2)

private theorem pair_three {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {s t : V ≃ₗ[ZMod 3] V} {a b : V} {f g : Dual (ZMod 3) V} (hfa : f a = 2) (hgb : g b = 2)
    (hs : ∀ v, s v = v - f v • a) (ht : ∀ v, t v = v - g v • b) (h : orderOf (s * t) = 3) :
    f b * g a = 1 := by
  have h3 : (s * t) ^ 3 = 1 := by
    have := pow_orderOf_eq_one (s * t)
    rwa [h] at this
  by_contra hpq
  exact pairStep_three_ne (f b) (g a) hpq (pairStep_fix_fst hfa hgb hs ht hpq 3 h3)

private theorem pair_four {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {s t : V ≃ₗ[ZMod 3] V} {a b : V} {f g : Dual (ZMod 3) V} (hfa : f a = 2) (hgb : g b = 2)
    (hs : ∀ v, s v = v - f v • a) (ht : ∀ v, t v = v - g v • b) (h : orderOf (s * t) = 4) :
    f b * g a = 2 := by
  have h4 : (s * t) ^ 4 = 1 := by
    have := pow_orderOf_eq_one (s * t)
    rwa [h] at this
  have hne : (s * t) ^ 2 ≠ 1 := by
    intro h2
    have := orderOf_dvd_of_pow_eq_one h2
    rw [h] at this
    exact absurd this (by decide)
  by_cases hpq : f b * g a = 1
  · exfalso
    apply hne
    have h3 := pow_eq_one_of_pairStep hfa hgb hs ht 3
      (fun α β => pairStep_three (f b) (g a) α β hpq)
    rw [pow_succ, h3, one_mul] at h4
    rw [h4, one_pow]
  · rcases pairStep_four (f b) (g a) hpq (pairStep_fix_fst hfa hgb hs ht hpq 4 h4)
      (pairStep_fix_snd hfa hgb hs ht hpq 4 h4) with h' | ⟨hp, hq⟩
    · exact h'
    · exfalso
      apply hne
      refine pow_eq_one_of_pairStep hfa hgb hs ht 2 fun α β => ?_
      rw [hp, hq]
      exact pairStep_zero_two α β

private theorem exists_refl_data {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V] (hV : finrank (ZMod 3) V = 4) (r : V ≃ₗ[ZMod 3] V)
    (hr2 : r * r = 1)
    (hfix : finrank (ZMod 3) (LinearMap.ker ((r : V →ₗ[ZMod 3] V) - LinearMap.id)) = 3) :
    ∃ (a : V) (f : Dual (ZMod 3) V), f a = 2 ∧ ∀ v, r v = v - f v • a := by
  set M : V →ₗ[ZMod 3] V := (r : V →ₗ[ZMod 3] V) - LinearMap.id
  have h1 : finrank (ZMod 3) (LinearMap.range M) = 1 := by
    have := M.finrank_range_add_finrank_ker
    omega
  let e : LinearMap.range M ≃ₗ[ZMod 3] ZMod 3 :=
    LinearEquiv.ofFinrankEq _ _ (h1.trans (Module.finrank_self (ZMod 3)).symm)
  have key : ∀ w : LinearMap.range M, (w : V) = e w • ((e.symm 1 : LinearMap.range M) : V) := by
    intro w
    have hw : w = e w • e.symm 1 := by
      rw [← map_smul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]
    conv_lhs => rw [hw]
    rfl
  set a : V := ((e.symm 1 : LinearMap.range M) : V)
  have ha0 : a ≠ 0 := by
    intro h0
    have : e.symm 1 = 0 := Subtype.ext h0
    exact one_ne_zero (e.symm.injective (this.trans (map_zero e.symm).symm))
  have hr : ∀ v, r v = v - (-(e.toLinearMap ∘ₗ M.rangeRestrict)) v • a := by
    intro v
    have hv := key (M.rangeRestrict v)
    simp only [LinearMap.neg_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, neg_smul,
      sub_neg_eq_add]
    rw [← hv]
    simp [M]
  refine ⟨a, -(e.toLinearMap ∘ₗ M.rangeRestrict), ?_, hr⟩
  have hra : r a = -a := by
    obtain ⟨w, hw⟩ : a ∈ LinearMap.range M := (e.symm 1).2
    have hrr : r (r w) = w := by
      rw [← LinearEquiv.mul_apply, hr2]
      rfl
    have hw' : r w - w = a := by simpa [M] using hw
    rw [← hw', map_sub, hrr]
    abel
  have h2 : ((-(e.toLinearMap ∘ₗ M.rangeRestrict)) a - 2) • a = 0 := by
    have := (hr a).symm.trans hra
    linear_combination (norm := module) -this
  rcases smul_eq_zero.mp h2 with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h ha0

private def cartanOf (x01 x10 x12 x21 x23 x32 : ZMod 3) : Fin 4 → Fin 4 → ZMod 3 :=
  ![![2, x01, 0, 0], ![x10, 2, x12, 0], ![0, x21, 2, x23], ![0, 0, x32, 2]]

private def cartanSigns (x01 x12 x23 : ZMod 3) : Fin 4 → ZMod 3 :=
  ![1, 2 * x01, 2 * x01 * x12, 2 * (2 * x01 * x12) * x23]

private theorem cartanSigns_spec : ∀ x01 x10 x12 x21 x23 x32 : ZMod 3, x01 * x10 = 1 →
    x12 * x21 = 2 → x23 * x32 = 1 → (∀ i, cartanSigns x01 x12 x23 i ≠ 0) ∧
      ∀ i j, cartanSigns x01 x12 x23 j * cartanOf x01 x10 x12 x21 x23 x32 i j =
        cartanSigns x01 x12 x23 i * f4Cartan3 i j := by
  decide +kernel

private theorem f4Cartan3_inj :
    ∀ v : Fin 4 → ZMod 3, (∀ i, ∑ j, f4Cartan3 i j * v j = 0) → v = 0 := by
  decide +kernel

theorem exists_linearEquiv_f4Refl3 {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V] (hV : Module.finrank (ZMod 3) V = 4)
    (r : Fin 4 → (V ≃ₗ[ZMod 3] V))
    (hr2 : ∀ i, r i * r i = 1)
    (hfix : ∀ i, Module.finrank (ZMod 3)
      (LinearMap.ker ((r i : V →ₗ[ZMod 3] V) - LinearMap.id)) = 3)
    (hord : ∀ i j, orderOf (r i * r j) = CoxeterMatrix.F₄ i j) :
    ∃ θ : V ≃ₗ[ZMod 3] (Fin 4 → ZMod 3), ∀ i v, θ (r i v) = f4Refl3 i (θ v) := by
  choose a f hfa hrf using fun i => exists_refl_data hV (r i) (hr2 i) (hfix i)
  have P01 := pair_three (hfa 0) (hfa 1) (hrf 0) (hrf 1) (by rw [hord]; rfl)
  have P02 := pair_two (hfa 0) (hfa 2) (hrf 0) (hrf 2) (by rw [hord]; rfl)
  have P03 := pair_two (hfa 0) (hfa 3) (hrf 0) (hrf 3) (by rw [hord]; rfl)
  have P12 := pair_four (hfa 1) (hfa 2) (hrf 1) (hrf 2) (by rw [hord]; rfl)
  have P13 := pair_two (hfa 1) (hfa 3) (hrf 1) (hrf 3) (by rw [hord]; rfl)
  have P23 := pair_three (hfa 2) (hfa 3) (hrf 2) (hrf 3) (by rw [hord]; rfl)
  obtain ⟨hε, hK⟩ := cartanSigns_spec _ _ _ _ _ _ P01 P12 P23
  have hA : ∀ i j, f i (a j) = cartanOf (f 0 (a 1)) (f 1 (a 0)) (f 1 (a 2)) (f 2 (a 1))
      (f 2 (a 3)) (f 3 (a 2)) i j := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [cartanOf, hfa, P02.1, P02.2, P03.1, P03.2, P13.1, P13.2]
  set ε := cartanSigns (f 0 (a 1)) (f 1 (a 2)) (f 2 (a 3))
  have hK' : ∀ i j, ε j * f i (a j) = ε i * f4Cartan3 i j := fun i j => by
    rw [hA]; exact hK i j
  set Φ : (Fin 4 → ZMod 3) →ₗ[ZMod 3] V := Fintype.linearCombination (ZMod 3) fun j => ε j • a j
    with hΦ
  have hΦs : ∀ i, Φ (Pi.single i 1) = ε i • a i := fun i => by
    rw [hΦ, Fintype.linearCombination_apply_single, one_smul]
  have hfΦ : ∀ i μ, f i (Φ μ) = ε i * ∑ j, f4Cartan3 i j * μ j := by
    intro i μ
    rw [hΦ, Fintype.linearCombination_apply, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    linear_combination μ j * hK' i j
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro μ hμ
    refine f4Cartan3_inj μ fun i => ?_
    have := hfΦ i μ
    rw [hμ, map_zero] at this
    exact (mul_eq_zero.mp this.symm).resolve_left (hε i)
  have hdim : finrank (ZMod 3) (Fin 4 → ZMod 3) = finrank (ZMod 3) V := by
    rw [Module.finrank_fin_fun, hV]
  let E := Φ.linearEquivOfInjective hinj hdim
  have hE : ∀ μ, E μ = Φ μ := fun μ => rfl
  refine ⟨E.symm, fun i v => ?_⟩
  obtain ⟨μ, rfl⟩ : ∃ μ, E μ = v := ⟨E.symm v, E.apply_symm_apply v⟩
  rw [E.symm_apply_apply, LinearEquiv.symm_apply_eq, hE, hE, hrf, hfΦ]
  simp only [f4Refl3, map_sub, map_smul, hΦs]
  module

theorem exists_mulEquiv_f4Refl3_of_comm {H : Type} [Group H]
    (hcomm : ∀ a b : H, a * b = b * a) (h3 : ∀ x : H, x ^ 3 = 1) (hcard : Nat.card H = 3 ^ 4)
    (φ : Fin 4 → MulAut H) (hφ2 : ∀ i, φ i ^ 2 = 1)
    (hfix : ∀ i, Nat.card {b : H // φ i b = b} * 3 = Nat.card H)
    (hord : ∀ i j, orderOf (φ i * φ j) = CoxeterMatrix.F₄ i j) :
    ∃ θ : H ≃* Multiplicative (Fin 4 → ZMod 3), ∀ (i : Fin 4) (b : H),
      θ (φ i b) = Multiplicative.ofAdd (f4Refl3 i (Multiplicative.toAdd (θ b))) := by
  have : Finite H := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  let : AddCommGroup (Additive H) :=
    { Additive.addGroup with
      add_comm := fun a b => hcomm (Additive.toMul a) (Additive.toMul b) }
  let : Module (ZMod 3) (Additive H) := AddCommGroup.zmodModule fun x => by
    apply Additive.toMul.injective
    rw [toMul_nsmul, h3]
    rfl
  have hV : finrank (ZMod 3) (Additive H) = 4 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := Additive H)
    rw [Nat.card_zmod] at h
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) (h.symm.trans hcard)
  let ρ : MulAut H →* (Additive H ≃ₗ[ZMod 3] Additive H) :=
    { toFun := fun ψ => (MulEquiv.toAdditive ψ).toLinearEquiv (ZMod.map_smul _)
      map_one' := LinearEquiv.ext fun _ => rfl
      map_mul' := fun _ _ => LinearEquiv.ext fun _ => rfl }
  have hρ : Function.Injective ρ := fun ψ₁ ψ₂ h => MulEquiv.ext fun x =>
    LinearEquiv.congr_fun h (Additive.ofMul x)
  have hr2 : ∀ i, ρ (φ i) * ρ (φ i) = 1 := fun i => by
    rw [← map_mul, ← pow_two, hφ2, map_one]
  have hord' : ∀ i j, orderOf (ρ (φ i) * ρ (φ j)) = CoxeterMatrix.F₄ i j := fun i j => by
    rw [← map_mul, orderOf_injective ρ hρ, hord]
  have hfix' : ∀ i, finrank (ZMod 3)
      (LinearMap.ker ((ρ (φ i) : Additive H →ₗ[ZMod 3] Additive H) - LinearMap.id)) = 3 := by
    intro i
    have hc : Nat.card
        (LinearMap.ker ((ρ (φ i) : Additive H →ₗ[ZMod 3] Additive H) - LinearMap.id)) =
          Nat.card {b : H // φ i b = b} :=
      Nat.card_congr (Equiv.subtypeEquiv Additive.toMul fun v => by
        rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
        exact Iff.rfl)
    have h27 : Nat.card {b : H // φ i b = b} = 3 ^ 3 := by
      have := hfix i
      rw [hcard] at this
      omega
    have h := Module.natCard_eq_pow_finrank (K := ZMod 3)
      (V := LinearMap.ker ((ρ (φ i) : Additive H →ₗ[ZMod 3] Additive H) - LinearMap.id))
    rw [Nat.card_zmod, hc, h27] at h
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) h).symm
  obtain ⟨θ₀, hθ₀⟩ := exists_linearEquiv_f4Refl3 hV (fun i => ρ (φ i)) hr2 hfix' hord'
  exact ⟨AddEquiv.toMultiplicativeRight θ₀.toAddEquiv, fun i b =>
    congrArg Multiplicative.ofAdd (hθ₀ i (Additive.ofMul b))⟩

@[expose] def f4Bil3 (u v : Fin 4 → ZMod 3) : ZMod 3 :=
  ∑ i, ∑ j, u i * v j * (![2, 2, 1, 1] i * f4Cartan3 i j)

@[expose] def f4Q3 (v : Fin 4 → ZMod 3) : ZMod 3 := 2 * f4Bil3 v v

@[expose] def f4Frame3 (v : Fin 4 → ZMod 3) : Finset (Fin 4 → ZMod 3) :=
  Finset.univ.filter fun w => f4Bil3 v w = 0 ∧ f4Q3 w = f4Q3 v

theorem card_f4Frame3 : ∀ v : Fin 4 → ZMod 3, f4Q3 v ≠ 0 → (f4Frame3 v).card = 6 := by
  decide +kernel

theorem exists_f4Witness : ∀ x : Fin 4 → ZMod 3, f4Q3 x ≠ 0 → ∀ z ∈ f4Frame3 x,
    ∃ m : Fin 4 → ZMod 3, f4Bil3 x m = 0 ∧ f4Bil3 z m = 0 ∧ f4Q3 m = -f4Q3 x := by
  decide +kernel

@[expose] def f4Cross3 (x : Fin 4 → ZMod 3) : Finset (Fin 4 → ZMod 3) :=
  insert x (insert (-x) (f4Frame3 x))

theorem not_stable_f4Cross3 : ∀ x : Fin 4 → ZMod 3, f4Q3 x ≠ 0 →
    ∃ i : Fin 4, ∃ w ∈ f4Cross3 x, f4Refl3 i w ∉ f4Cross3 x := by
  decide +kernel

theorem f4Q3_refl : ∀ (i : Fin 4) (v : Fin 4 → ZMod 3), f4Q3 (f4Refl3 i v) = f4Q3 v := by
  decide +kernel

private theorem f4Gram3_symm : ∀ i j : Fin 4,
    (![2, 2, 1, 1] i * f4Cartan3 i j : ZMod 3) = ![2, 2, 1, 1] j * f4Cartan3 j i := by
  decide +kernel

theorem f4Bil3_comm (u v : Fin 4 → ZMod 3) : f4Bil3 u v = f4Bil3 v u := by
  unfold f4Bil3
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [f4Gram3_symm j i]
  ring

theorem f4Bil3_add_left (u u' v : Fin 4 → ZMod 3) :
    f4Bil3 (u + u') v = f4Bil3 u v + f4Bil3 u' v := by
  simp only [f4Bil3, Fin.sum_univ_four, Pi.add_apply]
  ring

theorem f4Bil3_add_right (u v v' : Fin 4 → ZMod 3) :
    f4Bil3 u (v + v') = f4Bil3 u v + f4Bil3 u v' := by
  rw [f4Bil3_comm, f4Bil3_add_left, f4Bil3_comm v, f4Bil3_comm v']

theorem f4Q3_add (u v : Fin 4 → ZMod 3) : f4Q3 (u + v) = f4Q3 u + f4Q3 v + f4Bil3 u v := by
  unfold f4Q3
  rw [f4Bil3_add_left, f4Bil3_add_right, f4Bil3_add_right, f4Bil3_comm v u]
  generalize f4Bil3 u u = a
  generalize f4Bil3 u v = b
  generalize f4Bil3 v v = c
  revert a b c
  decide

theorem card_f4Perp3 : ∀ v : Fin 4 → ZMod 3, v ≠ 0 →
    (Finset.univ.filter fun w : Fin 4 → ZMod 3 => f4Bil3 v w = 0).card = 27 := by
  decide +kernel

theorem f4Cross3_eq_of_mem_f4Frame3 : ∀ x : Fin 4 → ZMod 3, f4Q3 x ≠ 0 → ∀ z ∈ f4Frame3 x,
    f4Cross3 z = f4Cross3 x := by
  decide +kernel

end CFSG.LieType.ReflectionGroups.F4ModThree
