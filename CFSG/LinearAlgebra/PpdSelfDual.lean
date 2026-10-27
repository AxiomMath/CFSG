module

public import CFSG.CGT.T75N.PpdCyclic
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Irr
public import CFSG.Timmesfeld.Orders.Bang
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.LinearAlgebra.PpdSelfDual

open Polynomial

theorem dvd_two_pow_add_one_of_orderOf_two {r f : ℕ} (hr : r.Prime)
    (hord : orderOf (2 : ZMod r) = 4 * f) (hf : 1 ≤ f) : r ∣ 2 ^ (2 * f) + 1 := by
  have h4 : (2 : ZMod r) ^ (4 * f) = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one _
  have hdvd4 : r ∣ 2 ^ (4 * f) - 1 :=
    (CFSG.Timmesfeld.Bang.dvd_two_pow_sub_one_iff (4 * f)).2 h4
  have hndvd : ¬ r ∣ 2 ^ (2 * f) - 1 := by
    intro h
    have h2 : (2 : ZMod r) ^ (2 * f) = 1 :=
      (CFSG.Timmesfeld.Bang.dvd_two_pow_sub_one_iff (2 * f)).1 h
    have hdiv : orderOf (2 : ZMod r) ∣ 2 * f := orderOf_dvd_of_pow_eq_one h2
    rw [hord] at hdiv
    have : 4 * f ≤ 2 * f := Nat.le_of_dvd (by omega) hdiv
    omega
  have hfac : 2 ^ (4 * f) - 1 = (2 ^ (2 * f) - 1) * (2 ^ (2 * f) + 1) := by
    rw [show 2 ^ (4 * f) = (2 ^ (2 * f)) ^ 2 by
      rw [show 4 * f = 2 * f * 2 by ring, pow_mul]]
    have h1 : 1 ≤ 2 ^ (2 * f) := Nat.one_le_pow _ _ (by norm_num)
    have h2 : 1 ≤ (2 ^ (2 * f)) ^ 2 := Nat.one_le_pow 2 _ (by omega)
    zify [h1, h2]
    ring
  have hdvdprod : r ∣ (2 ^ (2 * f) - 1) * (2 ^ (2 * f) + 1) := by
    rw [← hfac]
    exact hdvd4
  rcases hr.dvd_or_dvd hdvdprod with h | h
  · exact absurd h hndvd
  · exact h

theorem eq_one_of_pow_two_pow_add_one {G : Type*} [Group G] {x : G} {f : ℕ} (hf : 1 ≤ f)
    (h1 : x ^ (2 ^ f + 1) = 1) (h2 : x ^ (2 ^ (2 * f) + 1) = 1) : x = 1 := by
  have hxq : x ^ (2 ^ f) = x⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ]
    exact h1
  have h22 : x ^ ((2 ^ f) ^ 2) = x := by
    rw [sq, pow_mul, hxq, inv_pow, hxq, inv_inv]
  have hx2 : x ^ 2 = 1 := by
    have hpow : 2 ^ (2 * f) = (2 ^ f) ^ 2 := by
      rw [show 2 * f = f * 2 by ring, pow_mul]
    rw [hpow, pow_succ, h22, ← pow_two] at h2
    exact h2
  have hq : 2 ^ f = 2 * 2 ^ (f - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hf]
  have hx : x ^ (2 ^ f + 1) = x := by
    rw [hq, pow_succ, pow_mul, hx2, one_pow, one_mul]
  rw [hx] at h1
  exact h1

theorem bilin_apply_eq_pow_of_commute {X : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    [Finite X] {f r : ℕ} (hX : Nat.card X = 2 ^ (4 * f)) (hr : r.Prime)
    (hord : orderOf (2 : ZMod r) = 4 * f) {a : X ≃ₗ[ZMod 2] X} (ha : a ^ r = 1)
    (ha1 : a ≠ 1) (β : X →ₗ[ZMod 2] X →ₗ[ZMod 2] ZMod 2)
    (hβa : ∀ x y, β (a x) (a y) = β x y)
    {B : Module.End (ZMod 2) X} (hB : Commute (a : Module.End (ZMod 2) X) B) (x y : X) :
    β (B x) y = β x ((B ^ 2 ^ (2 * f)) y) := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  have hf : 1 ≤ f := by
    by_contra hf
    have hX1 : Nat.card X = 1 := by simpa [show f = 0 by omega] using hX
    haveI : Subsingleton X := Finite.card_le_one_iff_subsingleton.mp (le_of_eq hX1)
    exact ha1 (LinearEquiv.ext fun v => Subsingleton.elim _ _)
  have hfin : Module.finrank (ZMod 2) X = 4 * f := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := X)
    rw [hX, Nat.card_zmod] at h
    exact Nat.pow_right_injective (by norm_num) h.symm
  have hpn : r ∣ 2 ^ (4 * f) - 1 :=
    (CFSG.Timmesfeld.Bang.dvd_two_pow_sub_one_iff (4 * f)).2 (by
      rw [← hord]; exact pow_orderOf_eq_one _)
  have hnp : ∀ k, 0 < k → k < 4 * f → ¬ r ∣ 2 ^ k - 1 := by
    intro k hk hklt hdvd
    have hdiv : orderOf (2 : ZMod r) ∣ k :=
      orderOf_dvd_of_pow_eq_one ((CFSG.Timmesfeld.Bang.dvd_two_pow_sub_one_iff k).1 hdvd)
    rw [hord] at hdiv
    exact absurd (Nat.le_of_dvd hk hdiv) (by omega)
  haveI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [hX]; exact Nat.one_lt_two_pow (by omega))
  have hirr : ∀ W : Submodule (ZMod 2) X,
      W ≤ W.comap (a : Module.End (ZMod 2) X) → W = ⊥ ∨ W = ⊤ := fun W hW =>
    (CFSG.CGT.T75N.simple_of_ppd (F := ZMod 2) (V := X) (n := 4 * f) (p := r)
      hfin (by simpa [ZMod.card] using hpn)
      (fun k hk hklt hdvd => hnp k hk hklt (by simpa [ZMod.card] using hdvd)) a ha ha1).2 W
      fun v hv => by simpa using hW hv
  obtain ⟨P, rfl⟩ := CFSG.ComponentClassification.CatFactsL4U4.exists_eq_aeval_of_commute
    (F := ZMod 2) (V := X) hirr hB
  have hAA' : ∀ u v : X, β ((a : Module.End (ZMod 2) X) u) v =
      β u (((a⁻¹ : X ≃ₗ[ZMod 2] X) : Module.End (ZMod 2) X) v) := fun u v =>
    by simpa using hβa u (a⁻¹ v)
  let N : ℕ := 2 ^ (2 * f)
  have hdvdN : r ∣ N + 1 := by simpa [N] using dvd_two_pow_add_one_of_orderOf_two hr hord hf
  have haN : a ^ (N + 1) = 1 :=
    (orderOf_dvd_iff_pow_eq_one).1 ((orderOf_dvd_of_pow_eq_one ha).trans hdvdN)
  have haNinv : a ^ N = a⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ]; exact haN
  have hAN : ((a : Module.End (ZMod 2) X) ^ N) =
      ((a⁻¹ : X ≃ₗ[ZMod 2] X) : Module.End (ZMod 2) X) := by
    have h := map_pow (LinearEquiv.automorphismGroup.toLinearMapMonoidHom
      (R := ZMod 2) (M := X)) a N
    simpa [haNinv, LinearEquiv.automorphismGroup.toLinearMapMonoidHom_apply] using h.symm
  have hexp : expand (ZMod 2) N P = P ^ N := by
    have h := CFSG.ComponentClassification.CatFactsL4U4.expand_card_pow (F := ZMod 2) P (2 * f)
    simpa [ZMod.card, N] using h
  have hpow : aeval ((a⁻¹ : X ≃ₗ[ZMod 2] X) : Module.End (ZMod 2) X) P =
      (aeval (a : Module.End (ZMod 2) X) P) ^ N := by
    rw [← hAN, ← Polynomial.expand_aeval, hexp, map_pow]
  have hmain := CFSG.ComponentClassification.CatFactsL4U4.bilin_aeval_left β hAA' P x y
  rw [hpow] at hmain
  exact hmain

theorem eq_one_of_ppd_selfDual {X : Type*} [AddCommGroup X] [Module (ZMod 2) X] [Finite X]
    {f r : ℕ} (hX : Nat.card X = 2 ^ (4 * f)) (hr : r.Prime)
    (hord : orderOf (2 : ZMod r) = 4 * f)
    {a b : X ≃ₗ[ZMod 2] X} (hab : a * b = b * a) (ha : a ^ r = 1) (ha1 : a ≠ 1)
    (hb : b ^ (2 ^ f + 1) = 1)
    (β : X →ₗ[ZMod 2] X →ₗ[ZMod 2] ZMod 2) (hβr : ∀ y, (∀ x, β x y = 0) → y = 0)
    (hβa : ∀ x y, β (a x) (a y) = β x y) (hβb : ∀ x y, β (b x) (b y) = β x y) :
    b = 1 := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  have hf : 1 ≤ f := by
    by_contra hf
    have hX1 : Nat.card X = 1 := by simpa [show f = 0 by omega] using hX
    haveI : Subsingleton X := Finite.card_le_one_iff_subsingleton.mp (le_of_eq hX1)
    exact ha1 (LinearEquiv.ext fun v => Subsingleton.elim _ _)
  let N : ℕ := 2 ^ (2 * f)
  have hB : Commute (a : Module.End (ZMod 2) X) (b : Module.End (ZMod 2) X) := by
    have h := ((commute_iff_eq a b).2 hab).map
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := ZMod 2) (M := X))
    simpa [LinearEquiv.automorphismGroup.toLinearMapMonoidHom_apply] using h
  have hbN_end : ((b : Module.End (ZMod 2) X) ^ N) =
      ((b⁻¹ : X ≃ₗ[ZMod 2] X) : Module.End (ZMod 2) X) := by
    ext y
    have h5 : ∀ x, β x (((b : Module.End (ZMod 2) X) ^ N) y) =
        β x ((((b⁻¹ : X ≃ₗ[ZMod 2] X) : Module.End (ZMod 2) X)) y) := by
      intro x
      have h3 := bilin_apply_eq_pow_of_commute (f := f) (r := r) hX hr hord ha ha1 β hβa
        (B := (b : Module.End (ZMod 2) X)) hB x y
      have h4 : β ((b : Module.End (ZMod 2) X) x) y =
          β x (((b⁻¹ : X ≃ₗ[ZMod 2] X) : Module.End (ZMod 2) X) y) := by
        simpa using hβb x (b⁻¹ y)
      exact h3.symm.trans h4
    apply sub_eq_zero.mp
    apply hβr
    intro x
    rw [map_sub, h5 x]
    exact sub_self _
  have hbN : b ^ N = b⁻¹ := by
    have h := (map_pow (LinearEquiv.automorphismGroup.toLinearMapMonoidHom
      (R := ZMod 2) (M := X)) b N).trans hbN_end
    exact LinearEquiv.toLinearMap_inj.mp h
  have hbN1 : b ^ (N + 1) = 1 := by
    rw [pow_succ, hbN, inv_mul_cancel]
  exact eq_one_of_pow_two_pow_add_one hf hb (by simpa [N] using hbN1)

end CFSG.LinearAlgebra.PpdSelfDual
