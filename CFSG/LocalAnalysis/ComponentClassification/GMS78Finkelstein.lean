module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78FinkelsteinBasic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal

public section

namespace CFSG.ComponentClassification.GMS78

open Finkelstein

namespace Finkelstein

theorem pow_mod_four {V : Type} [Monoid V] {w : V} (hw : w ^ 4 = 1) (m : ℕ) :
    w ^ (m % 4) = w ^ m := by
  conv_rhs => rw [← Nat.mod_add_div m 4, pow_add, pow_mul, hw, one_pow, mul_one]

theorem nonempty_mulEquiv_zmod_four {V : Type} [CommGroup V] [Finite V] {n : ℕ}
    (A : Subgroup V) (hA : Nat.card A = 2 ^ n) (hV : Nat.card V = 2 ^ (2 * n))
    (hA2 : ∀ u : V, u * u = 1 ↔ u ∈ A)
    (hroot : ∀ a ∈ A, ∃ w : V, w * w = a) :
    Nonempty (V ≃* (Fin n → Multiplicative (ZMod 4))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Module (ZMod 2) (Additive A) := AddCommGroup.zmodModule fun x => by
    rw [two_nsmul]
    apply Additive.toMul.injective
    rw [toMul_add, toMul_zero]
    exact Subtype.ext ((hA2 _).mpr (Additive.toMul x).2)
  have hfin : Module.finrank (ZMod 2) (Additive A) = n := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive A)
    rw [Nat.card_zmod, show Nat.card (Additive A) = Nat.card A from rfl, hA] at h1
    exact (Nat.pow_right_injective le_rfl h1).symm
  set b := Module.finBasisOfFinrankEq (ZMod 2) (Additive A) hfin with hb
  set e : Fin n → V := fun i => ((Additive.toMul (b i) : A) : V) with he
  have he2 : ∀ i, e i * e i = 1 := fun i => (hA2 _).mpr (Additive.toMul (b i)).2
  choose w hw using fun i => hroot (e i) (Additive.toMul (b i)).2
  have hw4 : ∀ i, w i ^ 4 = 1 := fun i => by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq (w i), hw, sq, he2]
  have hind : ∀ c : Fin n → ℕ, ∏ i, e i ^ c i = 1 → ∀ i, 2 ∣ c i := by
    intro c hc
    have hsum : ∑ i, ((c i : ℕ) : ZMod 2) • b i = 0 := by
      apply Additive.toMul.injective
      rw [toMul_zero, toMul_sum]
      apply Subtype.ext
      rw [Subgroup.val_finsetProd, OneMemClass.coe_one, ← hc]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Nat.cast_smul_eq_nsmul, toMul_nsmul, SubgroupClass.coe_pow]
    intro i
    exact (ZMod.natCast_eq_zero_iff _ _).mp
      (Fintype.linearIndependent_iff.mp b.linearIndependent _ hsum i)
  set Φ : (Fin n → Multiplicative (ZMod 4)) →* V :=
    { toFun := fun x => ∏ i, w i ^ (Multiplicative.toAdd (x i)).val
      map_one' := by simp
      map_mul' := fun x x' => by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [Pi.mul_apply, toAdd_mul, ZMod.val_add, pow_mod_four (hw4 i), pow_add] } with hΦ
  have hΦ_apply : ∀ x, Φ x = ∏ i, w i ^ (Multiplicative.toAdd (x i)).val := fun x => rfl
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    set p : Fin n → ℕ := fun i => (Multiplicative.toAdd (x i)).val with hp
    have hp4 : ∀ i, p i < 4 := fun i => ZMod.val_lt _
    have hx' : ∏ i, w i ^ p i = 1 := (hΦ_apply x).symm.trans hx
    have h2 : ∏ i, e i ^ p i = 1 := by
      have h3 : (∏ i, w i ^ p i) * (∏ i, w i ^ p i) = 1 := by rw [hx', mul_one]
      rw [← Finset.prod_mul_distrib] at h3
      rw [← h3]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← hw i, mul_pow]
    have hev := hind p h2
    have h4 : ∏ i, e i ^ (p i / 2) = 1 := by
      rw [← hx']
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← hw i, ← sq, ← pow_mul, Nat.mul_div_cancel' (hev i)]
    have hev2 := hind _ h4
    funext i
    have hpi : p i = 0 := by
      have := hev i
      have := hev2 i
      have := hp4 i
      omega
    rw [Pi.one_apply, ← toAdd_eq_zero, ← ZMod.val_eq_zero]
    exact hpi
  have hbij : Function.Bijective Φ := by
    refine hinj.bijective_of_nat_card_le ?_
    rw [hV, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin,
      show Nat.card (Multiplicative (ZMod 4)) = Nat.card (ZMod 4) from rfl, Nat.card_zmod,
      pow_mul]
    norm_num
  exact ⟨(MulEquiv.ofBijective Φ hbij).symm⟩

end Finkelstein

theorem finkelsteinLemmaSq :
    ∀ (U : Type) [Group U] [Finite U] (n : ℕ), 1 ≤ n → Nat.card U = 2 ^ (2 * n) →
      ∀ t y : MulAut U, t ^ 2 = 1 → t * y = y * t → orderOf y = 2 ^ n - 1 →
      (∀ a b : U, t a = a → t b = b → a ≠ 1 → b ≠ 1 →
        ∃! k : ℕ, k < 2 ^ n - 1 ∧ (y ^ k) a = b) →
      ((∃ k : ℕ, 1 ≤ k ∧ Nonempty (U ≃* (Fin n → Multiplicative (ZMod (2 ^ k))))) ∧
        ∀ u : U, t u = u⁻¹) ∨
      ((∃ k : ℕ, 1 ≤ k ∧ Nonempty (U ≃* (Fin n → Multiplicative (ZMod (2 ^ k))))) ∧
        ∀ u : U, u * t u = 1 → ∃ v : U, u = v * (t v)⁻¹) ∨
      ((∀ a b : U, a * b = b * a) ∧ (∀ a : U, a ^ 2 = 1) ∧ Nat.card U = 2 ^ (2 * n) ∧
        ∀ u : U, u * t u = 1 → ∃ v : U, u = v * (t v)⁻¹) := by
  intro U _ _ n hn hcard t y ht hty hord hreg
  have h : FinkHyp U n t y := ⟨hn, hcard, ht, hty, hord, hreg⟩
  have hc := h.mul_comm'
  have hut : ∀ u, u * t u = u * u * psi t u := fun u => by
    rw [← mul_psi t u, mul_assoc]
  have hconj : ∀ u ∈ fixSubgroup t, ∃ v, u = v * (t v)⁻¹ := by
    intro u hu
    obtain ⟨v, hv⟩ := h.exists_psi_eq (inv_mem hu)
    refine ⟨v, ?_⟩
    rw [← mul_psi t v, mul_inv_rev, hv, inv_inv, hc u v⁻¹, mul_inv_cancel_left]
  rcases h.squares_cases with hsq | ⟨k, hk⟩
  ·
    right; right
    refine ⟨hc, fun a => by rw [pow_two]; exact hsq a, hcard, fun u hu => hconj u ?_⟩
    rw [hut, hsq, one_mul] at hu
    exact psi_eq_one_iff.mp hu
  ·
    have hA2 : ∀ u : U, u * u = 1 ↔ u ∈ fixSubgroup t := by
      intro u
      refine ⟨fun h1 => ?_, h.mul_self_eq_one_of_mem_fix⟩
      rw [hk, ← map_one (y ^ k)] at h1
      exact psi_eq_one_iff.mp ((y ^ k).injective h1)
    have hroot : ∀ a ∈ fixSubgroup t, ∃ w : U, w * w = a := by
      intro a ha
      have hb : (y ^ k).symm a ∈ fixSubgroup t := by
        apply (y ^ k).injective
        rw [← h.t_pow_y, MulEquiv.apply_symm_apply]
        exact ha
      obtain ⟨v, hv⟩ := h.exists_psi_eq hb
      exact ⟨v, by rw [hk, hv, MulEquiv.apply_symm_apply]⟩
    have hiso : Nonempty (U ≃* (Fin n → Multiplicative (ZMod (2 ^ 2)))) := by
      let _ : CommGroup U := { ‹Group U› with mul_comm := hc }
      exact nonempty_mulEquiv_zmod_four (fixSubgroup t) h.natCard_fix hcard hA2 hroot
    by_cases hk1 : y ^ k = 1
    ·
      left
      refine ⟨⟨2, by norm_num, hiso⟩, fun u => ?_⟩
      have h1 := hk u
      rw [hk1, MulAut.one_apply, psi] at h1
      have h4 : u * u * (u * u) = 1 := h.mul_self_eq_one_of_mem_fix (h.mul_self_mem_fix u)
      calc t u = u * (u⁻¹ * t u) := by group
        _ = u * (u * u) := by rw [← h1]
        _ = u⁻¹ := by
          rw [eq_inv_iff_mul_eq_one, ← h4]
          group
    ·
      right; left
      refine ⟨⟨2, by norm_num, hiso⟩, fun u hu => hconj u ?_⟩
      rw [hut, hk] at hu
      by_contra hA
      have hψ1 : psi t u ≠ 1 := fun h1 => hA (psi_eq_one_iff.mp h1)
      have hfix : (y ^ k) (psi t u) = psi t u := by
        have h2 := h.mul_self_eq_one_of_mem_fix (h.psi_mem_fix u)
        rw [mul_eq_one_iff_eq_inv] at hu
        rw [hu, inv_eq_of_mul_eq_one_right h2]
      exact hk1 (h.pow_eq_one_of_fix (h.psi_mem_fix u) hψ1 hfix)

end CFSG.ComponentClassification.GMS78
