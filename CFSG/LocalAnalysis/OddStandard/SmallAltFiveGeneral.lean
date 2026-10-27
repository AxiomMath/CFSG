module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.GroupTheory.SpecificGroups.KleinFour

public section

namespace CFSG.OddStandard

open Subgroup

variable {G : Type*} [Group G]

theorem card_sup_of_commute {A B : Subgroup G} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hAB : A ⊓ B = ⊥) : Nat.card (A ⊔ B : Subgroup G) = Nat.card A * Nat.card B := by
  let f : A × B →* G := (A.subtype).noncommCoprod B.subtype (fun a b => hc a a.2 b b.2)
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, b⟩ hab
    have h1 : (a : G) * b = 1 := hab
    have h2 : (a : G) = (b : G)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3 : (a : G) ∈ A ⊓ B := ⟨a.2, h2 ▸ B.inv_mem b.2⟩
    rw [hAB, mem_bot] at h3
    have h4 : (b : G) = 1 := by rw [h3, eq_comm, inv_eq_one] at h2; exact h2
    exact Prod.ext (Subtype.ext h3) (Subtype.ext h4)
  have hrange : f.range = A ⊔ B :=
    (MonoidHom.noncommCoprod_range A.subtype B.subtype _).trans (by simp)
  rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod]

theorem card_eq_card_range_mul_card_ker {H : Type*} [Group H] (f : G →* H) :
    Nat.card G = Nat.card f.range * Nat.card f.ker := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]

theorem comm_of_mul_self_eq_one {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : (a * b) * (a * b) = 1) : a * b = b * a := by
  have h1 : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have h2 : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have h3 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right hab
  rw [mul_inv_rev, h1, h2] at h3
  exact h3.symm

theorem card_eq_of_maximal [Finite G] {p : ℕ} [Fact p.Prime] {X Q : Subgroup G} (hQX : Q ≤ X)
    (hQ : IsPGroup p Q) (hmax : ∀ Q' : Subgroup G, Q' ≤ X → IsPGroup p Q' → Q ≤ Q' → Q' = Q) :
    Nat.card Q = p ^ (Nat.card X).factorization p := by
  have hQ' : IsPGroup p (Q.subgroupOf X) := hQ.of_equiv (subgroupOfEquivOfLe hQX).symm
  obtain ⟨V, hV⟩ := hQ'.exists_le_sylow
  have h1 : Q ≤ (V : Subgroup X).map X.subtype := fun x hx =>
    ⟨⟨x, hQX hx⟩, hV (mem_subgroupOf.mpr hx), rfl⟩
  have h2 : (V : Subgroup X).map X.subtype = Q :=
    hmax _ (map_subtype_le _) (V.isPGroup'.map _) h1
  rw [← h2, Subgroup.card_map_of_injective X.subtype_injective, Sylow.card_eq_multiplicity]

theorem isKleinFour_of_card_four_of_mul_self {H : Type*} [Group H] (h4 : Nat.card H = 4)
    (hsq : ∀ x : H, x * x = 1) : IsKleinFour H := by
  refine ⟨h4, ?_⟩
  have hsq' : ∀ x : H, x ^ 2 = 1 := fun x => by rw [pow_two, hsq]
  rcases (Nat.dvd_prime Nat.prime_two).mp (Monoid.exponent_dvd_of_forall_pow_eq_one hsq') with
    h | h
  · have : Subsingleton H := Monoid.exp_eq_one_iff.mp h
    have := Nat.card_of_subsingleton (1 : H)
    omega
  · exact h

theorem nonempty_mulEquiv_klein {P : Subgroup G} (h4 : Nat.card P = 4)
    (hsq : ∀ p ∈ P, p * p = 1) :
    Nonempty (P ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) := by
  have hKP : IsKleinFour P :=
    isKleinFour_of_card_four_of_mul_self h4 fun x => Subtype.ext (hsq x x.2)
  have hKV : IsKleinFour (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :=
    isKleinFour_of_card_four_of_mul_self (by
      rw [Nat.card_prod, Nat.card_eq_fintype_card]; rfl) (by decide)
  exact IsKleinFour.nonempty_mulEquiv

theorem mem_sup_iff_of_commute {A B : Subgroup G} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (x : G) : x ∈ A ⊔ B ↔ ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  have hAB : A ≤ normalizer (B : Set G) := fun a ha =>
    centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun b hb => (hc a ha b hb).symm)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right A B hAB, Set.mem_mul]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩

theorem eq_one_or_eq_of_mem_zpowers_of_mul_self {x y : G} (hx : x * x = 1) (hy : y ∈ zpowers x) :
    y = 1 ∨ y = x := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
  have h2 : x ^ (2 : ℤ) = 1 := by rw [zpow_two, hx]
  rw [zpow_eq_zpow_emod k h2]
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left
    rw [h0, zpow_zero]
  · right
    rw [h1, zpow_one]

theorem exists_pow_orderOf_eq_two {g : G} {k : ℕ} (hg : orderOf g = 2 ^ k) (hg1 : g ≠ 1) :
    ∃ m : ℕ, orderOf (g ^ m) = 2 := by
  have hk : k ≠ 0 := by
    rintro rfl
    exact hg1 (orderOf_eq_one_iff.mp (by simpa using hg))
  have h2 : 2 ∣ orderOf g := by
    rw [hg]
    exact dvd_pow_self 2 hk
  exact ⟨orderOf g / 2, orderOf_pow_orderOf_div (by rw [hg]; positivity) h2⟩

end CFSG.OddStandard
