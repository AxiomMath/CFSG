module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

public section

namespace CFSG.CGT.T75N

variable {V : Type} [CommGroup V] [Finite V]

theorem exists_fixed_ne_one (hV : Even (Nat.card V)) {a : MulAut V} (ha : a * a = 1) :
    ∃ v : V, v ≠ 1 ∧ a v = v := by
  classical
  have := Fintype.ofFinite V
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f : Function.End V := (a : V → V)
  have hf : f ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two]
    funext v
    have := congrArg (fun b : MulAut V => b v) ha
    change a (a v) = v
    simpa [MulAut.mul_apply] using this
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 2) (n := 1) hf
  by_contra hcon
  push Not at hcon
  have hcard : Fintype.card (Function.fixedPoints f) = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨1, ?_⟩, fun ⟨x, hx⟩ => Subtype.ext ?_⟩
    · exact map_one a
    · by_contra hx1
      exact hcon x hx1 hx
  rw [hcard, ← Nat.card_eq_fintype_card] at hmod
  have h2 : (Nat.card V) % 2 = 1 % 2 := hmod
  rcases hV with ⟨k, hk⟩
  omega

theorem eq_one_of_central_sq_eq_one (hV : Even (Nat.card V)) (H : Subgroup (MulAut V))
    (htrans : ∀ v w : V, v ≠ 1 → w ≠ 1 → ∃ h ∈ H, h v = w) {a : MulAut V} (ha : a * a = 1)
    (hcen : ∀ h ∈ H, a * h = h * a) : a = 1 := by
  obtain ⟨v, hv, hav⟩ := exists_fixed_ne_one hV ha
  ext w
  by_cases hw : w = 1
  · subst hw
    simp
  · obtain ⟨h, hh, rfl⟩ := htrans v w hv hw
    have := congrArg (fun x : MulAut V => x v) (hcen h hh)
    simpa [MulAut.mul_apply, hav] using this

theorem odd_card_of_le_center (hV : Even (Nat.card V)) (H : Subgroup (MulAut V))
    (htrans : ∀ v w : V, v ≠ 1 → w ≠ 1 → ∃ h ∈ H, h v = w) (C : Subgroup H)
    (hC : C ≤ Subgroup.center H) : Odd (Nat.card C) := by
  by_contra hodd
  have h2 : 2 ∣ Nat.card C := even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hodd)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 h2
  set a : MulAut V := ((x : H) : MulAut V) with ha
  have hord : orderOf a = 2 := by
    rw [ha, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
  have hsq : a * a = 1 := by
    rw [← pow_two, ← hord, pow_orderOf_eq_one]
  have hcen : ∀ h ∈ H, a * h = h * a := by
    intro h hh
    have := Subgroup.mem_center_iff.1 (hC x.2) ⟨h, hh⟩
    have h3 := congrArg (fun y : H => (y : MulAut V)) this
    exact h3.symm
  have h1 := eq_one_of_central_sq_eq_one hV H htrans hsq hcen
  rw [h1, orderOf_one] at hord
  omega

end CFSG.CGT.T75N
