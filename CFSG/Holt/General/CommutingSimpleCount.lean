module

public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Holt.General

open MulAction

private theorem two_mul_le_two_pow (b : ℕ) : 2 * b ≤ 2 ^ b := by
  rcases b with _ | b
  · simp
  · have := Nat.lt_two_pow_self (n := b)
    rw [pow_succ]
    omega

theorem card_sq_le_two_pow_ncard_of_forall_sq_eq_one {N : Type*} [Finite N]
    (U : Subgroup (Equiv.Perm N)) (hU : ∀ u ∈ U, u ^ 2 = 1) (S : Set N)
    (hS : ∀ u ∈ U, ∀ y ∉ S, u y = y) : Nat.card U ^ 2 ≤ 2 ^ S.ncard := by
  obtain ⟨n, hn⟩ : ∃ n, S.ncard = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing U S with
  | _ n ih =>
    rcases S.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · have hbot : U = ⊥ := by
        rw [eq_bot_iff]
        intro u hu
        rw [Subgroup.mem_bot]
        ext y
        exact hS u hu y (Set.notMem_empty y)
      subst hbot
      simp
    · have hinv : ∀ u ∈ U, u⁻¹ = u := fun u hu =>
        inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hU u hu)
      have hcomm : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u := by
        intro u hu v hv
        calc u * v = (u * v)⁻¹ := (hinv _ (U.mul_mem hu hv)).symm
          _ = v * u := by rw [mul_inv_rev, hinv u hu, hinv v hv]
      set O : Set N := orbit U x with hO
      have hOS : O ⊆ S := by
        rintro _ ⟨u, rfl⟩
        show (u : Equiv.Perm N) x ∈ S
        by_contra hy
        have h2 : (u : Equiv.Perm N) ((u : Equiv.Perm N) x) = x := by
          rw [← Equiv.Perm.mul_apply, ← pow_two, hU u u.2, Equiv.Perm.one_apply]
        exact hy (by rw [← hS u u.2 _ hy, h2]; exact hx)
      have hxO : x ∈ O := mem_orbit_self x
      set U' : Subgroup (Equiv.Perm N) := (stabilizer U x).map U.subtype with hU'
      have hU'U : U' ≤ U := by
        rintro _ ⟨w, -, rfl⟩
        exact w.2
      have hfixO : ∀ v ∈ U', ∀ y ∈ O, v y = y := by
        rintro _ ⟨w, hw, rfl⟩ _ ⟨u, rfl⟩
        have hwx : (w : Equiv.Perm N) x = x := hw
        show (w : Equiv.Perm N) ((u : Equiv.Perm N) x) = (u : Equiv.Perm N) x
        rw [← Equiv.Perm.mul_apply, hcomm _ w.2 _ u.2, Equiv.Perm.mul_apply, hwx]
      have hS' : ∀ v ∈ U', ∀ y ∉ S \ O, v y = y := by
        intro v hv y hy
        by_cases hyO : y ∈ O
        · exact hfixO v hv y hyO
        · exact hS v (hU'U hv) y (fun hyS => hy ⟨hyS, hyO⟩)
      have hcard : (S \ O).ncard + O.ncard = S.ncard := Set.ncard_sdiff_add_ncard_of_subset hOS
      have hOpos : 0 < O.ncard := (Set.ncard_pos (Set.toFinite O)).mpr ⟨x, hxO⟩
      have ih' := ih _ (by omega) U' (fun v hv => hU v (hU'U hv)) (S \ O) hS' rfl
      have hos : Nat.card U = Nat.card U' * O.ncard := by
        rw [hU', Subgroup.card_map_of_injective U.subtype_injective, hO, ← index_stabilizer,
          Subgroup.card_mul_index]
      have hp : IsPGroup 2 U := fun u => ⟨1, Subtype.ext (by simpa using hU u u.2)⟩
      obtain ⟨b, hb⟩ := hp.card_orbit x
      rw [Nat.card_coe_set_eq, ← hO] at hb
      rw [hos, mul_pow, ← hcard, pow_add, hb, ← pow_mul]
      exact Nat.mul_le_mul ih' (Nat.pow_le_pow_right (by norm_num)
        (by have := two_mul_le_two_pow b; omega))

end CFSG.Holt.General
