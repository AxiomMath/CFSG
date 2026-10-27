module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5Preimages

public section

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace Involution

variable {Q : Type*} [Group Q] [Finite Q]

omit [Finite Q] in
theorem sq_eq_one_or_orderOf_four {u : Q} {k : ℕ} (hk : orderOf u = 2 ^ k) :
    u ^ 2 = 1 ∨ (2 ≤ k ∧ orderOf (u ^ 2 ^ (k - 2)) = 4) := by
  by_cases h2 : 2 ≤ k
  · right
    refine ⟨h2, ?_⟩
    rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) (hk ▸ pow_dvd_pow 2 (Nat.sub_le k 2)), hk]
    rw [show k = (k - 2) + 2 by omega, pow_add, Nat.add_sub_cancel]
    rw [Nat.mul_div_cancel_left _ (pow_pos two_pos _)]
    norm_num
  · left
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [hk]
    exact (pow_dvd_pow 2 (show k ≤ 1 by omega)).trans (pow_one 2).dvd

omit [Finite Q] in
theorem card_le_two_of_subset {P : Subgroup Q} {c : Q} (hsub : (P : Set Q) ⊆ {1, c}) :
    Nat.card P ≤ 2 := by
  have hfin : ({1, c} : Set Q).Finite := Set.toFinite _
  have h1 : (P : Set Q).ncard ≤ ({1, c} : Set Q).ncard := Set.ncard_le_ncard hsub hfin
  have h2 : ({1, c} : Set Q).ncard ≤ 2 :=
    (Set.ncard_insert_le 1 {c}).trans (by rw [Set.ncard_singleton])
  have h3 : Nat.card P = (P : Set Q).ncard := by
    rw [← Nat.card_coe_set_eq]
    rfl
  omega

omit [Finite Q] in
theorem exists_orderOf_four {P : Subgroup Q} (hP : IsPGroup 2 P) (h4 : 4 ≤ Nat.card P) {c : Q}
    (hc : ∀ x ∈ P, orderOf x = 2 → x = c) : ∃ y ∈ P, orderOf y = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hno
  push Not at hno
  have hsq : ∀ x ∈ P, x ^ 2 = 1 := by
    intro x hx
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP) ⟨x, hx⟩
    rw [Subgroup.orderOf_mk] at hk
    rcases sq_eq_one_or_orderOf_four hk with h | ⟨-, h⟩
    · exact h
    · exact absurd h (hno _ (P.pow_mem hx _))
  have hsub : (P : Set Q) ⊆ {1, c} := by
    intro x hx
    by_cases h1 : x = 1
    · exact Or.inl h1
    · exact Or.inr (hc x hx (orderOf_eq_prime (hsq x hx) h1))
  have hle : Nat.card P ≤ 2 := card_le_two_of_subset hsub
  omega

@[expose] def fixedIn (P : Subgroup Q) (σ : Q →* Q) : Subgroup Q where
  carrier := {x | x ∈ P ∧ σ x = x}
  mul_mem' := fun ha hb => ⟨P.mul_mem ha.1 hb.1, by rw [map_mul, ha.2, hb.2]⟩
  one_mem' := ⟨P.one_mem, map_one σ⟩
  inv_mem' := fun ha => ⟨P.inv_mem ha.1, by rw [map_inv, ha.2]⟩

omit [Finite Q] in
theorem mem_fixedIn {P : Subgroup Q} {σ : Q →* Q} {x : Q} :
    x ∈ fixedIn P σ ↔ x ∈ P ∧ σ x = x := Iff.rfl

omit [Finite Q] in
theorem fixedIn_le (P : Subgroup Q) (σ : Q →* Q) : fixedIn P σ ≤ P := fun _ hx => hx.1

omit [Finite Q] in
theorem unique_involution_central {P : Subgroup Q} {c : Q} (hcP : c ∈ P) (hc2 : orderOf c = 2)
    (hc : ∀ x ∈ P, orderOf x = 2 → x = c) {p : Q} (hp : p ∈ P) : p * c = c * p := by
  have hconj : p * c * p⁻¹ = c := by
    apply hc _ (P.mul_mem (P.mul_mem hp hcP) (P.inv_mem hp))
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hc2]
  calc p * c = p * c * p⁻¹ * p := by group
    _ = c * p := by rw [hconj]

theorem exists_orderOf_four_fixed_or_inverted {P : Subgroup Q} (hP : IsPGroup 2 P)
    (h8 : 8 ≤ Nat.card P) {c : Q} (hcP : c ∈ P) (hc2 : orderOf c = 2)
    (hc : ∀ x ∈ P, orderOf x = 2 → x = c) (σ : Q →* Q) (hσ : ∀ x, σ (σ x) = x)
    (hσP : ∀ x ∈ P, σ x ∈ P) :
    ∃ y ∈ P, orderOf y = 4 ∧ (σ y = y ∨ σ y = y⁻¹) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hF : 4 ≤ Nat.card (fixedIn P σ)
  · obtain ⟨y, hy, hy4⟩ := exists_orderOf_four (hP.to_le (fixedIn_le P σ)) hF
      (fun x hx hx2 => hc x hx.1 hx2)
    exact ⟨y, hy.1, hy4, Or.inl hy.2⟩
  push Not at hF
  by_contra hno
  push Not at hno
  have hval : ∀ z ∈ P, z⁻¹ * σ z = 1 ∨ z⁻¹ * σ z = c := by
    intro z hz
    set u := z⁻¹ * σ z with hu
    have huP : u ∈ P := P.mul_mem (P.inv_mem hz) (hσP z hz)
    have hσu : σ u = u⁻¹ := by
      rw [hu, map_mul, map_inv, hσ, mul_inv_rev, inv_inv]
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP) ⟨u, huP⟩
    rw [Subgroup.orderOf_mk] at hk
    rcases sq_eq_one_or_orderOf_four hk with h | ⟨-, h⟩
    · by_cases h1 : u = 1
      · exact Or.inl h1
      · exact Or.inr (hc u huP (orderOf_eq_prime h h1))
    · exfalso
      refine (hno _ (P.pow_mem huP _) h).2 ?_
      rw [map_pow, hσu, inv_pow]
  have hcent : ∀ p ∈ P, p * c = c * p := fun p hp => unique_involution_central hcP hc2 hc hp
  let φ : P →* Q :=
    { toFun := fun z => (z : Q)⁻¹ * σ z
      map_one' := by simp
      map_mul' := fun z w => by
        have hzc : ((z : Q)⁻¹ * σ z) * (w : Q)⁻¹ = (w : Q)⁻¹ * ((z : Q)⁻¹ * σ z) := by
          rcases hval z z.2 with h | h
          · rw [h, one_mul, mul_one]
          · rw [h, hcent _ (P.inv_mem w.2)]
        change ((z : Q) * w)⁻¹ * σ (z * w) = ((z : Q)⁻¹ * σ z) * ((w : Q)⁻¹ * σ w)
        calc ((z : Q) * w)⁻¹ * σ (z * w) = (w : Q)⁻¹ * ((z : Q)⁻¹ * σ z) * σ w := by
              rw [map_mul, mul_inv_rev]
              group
          _ = ((z : Q)⁻¹ * σ z) * (w : Q)⁻¹ * σ w := by rw [hzc]
          _ = ((z : Q)⁻¹ * σ z) * ((w : Q)⁻¹ * σ w) := by group }
  have hrange : Nat.card φ.range ≤ 2 := by
    apply card_le_two_of_subset
    rintro _ ⟨z, rfl⟩
    rcases hval z z.2 with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hker : Nat.card φ.ker ≤ Nat.card (fixedIn P σ) := by
    apply Nat.card_le_card_of_injective (fun z : φ.ker => (⟨z.1.1, z.1.2, ?_⟩ : fixedIn P σ))
    · intro a b hab
      exact Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hab))
    · have hz := z.2
      rw [MonoidHom.mem_ker] at hz
      change ((z.1 : Q))⁻¹ * σ z.1 = 1 at hz
      rw [inv_mul_eq_one] at hz
      exact hz.symm
  have hcard := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker] at hcard
  have : Nat.card P ≤ 3 * 2 := by
    rw [← hcard]
    exact Nat.mul_le_mul (hker.trans (by omega)) hrange
  omega

end Involution

end CFSG.ComponentClassification.AschbacherTheorem5
