module

public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.EvenSporadicStandard.Induction.AutBound

open Subgroup

theorem eq_one_of_triangle_comm {A : Type*} [CommGroup A] {x y : A} {m : ℕ}
    (hm : Nat.Coprime m 6) (hx : x * x = 1) (hy : y * y * y = 1) (h : (x * y) ^ m = 1) :
    x = 1 ∧ y = 1 := by
  have hx2 : x ^ 2 = 1 := by rw [sq]; exact hx
  have hy3 : y ^ 3 = 1 := by rw [pow_succ, sq]; exact hy
  have h6 : (x * y) ^ 6 = 1 := by
    rw [mul_pow, show (6 : ℕ) = 2 * 3 by norm_num, pow_mul, hx2, one_pow, one_mul, mul_comm 2 3,
      pow_mul, hy3, one_pow]
  have hd : orderOf (x * y) ∣ Nat.gcd m 6 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h) (orderOf_dvd_of_pow_eq_one h6)
  rw [hm] at hd
  have hxy : x * y = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 hd)
  have hyx : y = x⁻¹ := eq_inv_of_mul_eq_one_right hxy
  have hxx : x = x⁻¹ := eq_inv_of_mul_eq_one_left hx
  have h1 : y = 1 := by
    have : y * y = 1 := by rw [hyx, ← hxx]; exact hx
    calc y = y * (y * y) := by rw [this, mul_one]
      _ = 1 := by rw [← mul_assoc]; exact hy
  refine ⟨?_, h1⟩
  rw [h1, mul_one] at hxy
  exact hxy

theorem commutator_eq_top_of_triangle {P : Type*} [Group P] {a b : P} {m : ℕ}
    (hm : Nat.Coprime m 6) (hgen : closure ({a, b} : Set P) = ⊤) (ha : a * a = 1)
    (hb : b * b * b = 1) (hab : (a * b) ^ m = 1) : commutator P = ⊤ := by
  obtain ⟨h1, h2⟩ := eq_one_of_triangle_comm (x := Abelianization.of a)
    (y := Abelianization.of b) hm (by rw [← map_mul, ha, map_one])
    (by rw [← map_mul, ← map_mul, hb, map_one]) (by rw [← map_mul, ← map_pow, hab, map_one])
  have hker : closure ({a, b} : Set P) ≤ (Abelianization.of : P →* Abelianization P).ker := by
    rw [Subgroup.closure_le]
    intro z hz
    rcases hz with h | h
    · rw [h]
      exact h1
    · rw [Set.mem_singleton_iff] at h
      rw [h]
      exact h2
  rw [hgen, top_le_iff, Abelianization.ker_of] at hker
  exact hker

theorem isPerfect_closure_triangle {K : Type*} [Group K] {a b : K} {m : ℕ} (hm : Nat.Coprime m 6)
    (ha : a * a = 1) (hb : b * b * b = 1) (hab : (a * b) ^ m = 1) :
    Group.IsPerfect ↥(closure ({a, b} : Set K)) := by
  have hamem : a ∈ closure ({a, b} : Set K) := subset_closure (Set.mem_insert _ _)
  have hbmem : b ∈ closure ({a, b} : Set K) :=
    subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hgen : closure ({⟨a, hamem⟩, ⟨b, hbmem⟩} : Set ↥(closure ({a, b} : Set K))) = ⊤ := by
    have h := Subgroup.closure_closure_coe_preimage (G := K) (k := ({a, b} : Set K))
    convert h using 2
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage]
    constructor
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (h | h)
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
  refine Group.isPerfect_def.2 (commutator_eq_top_of_triangle hm hgen ?_ ?_ ?_)
  · exact Subtype.ext ha
  · exact Subtype.ext hb
  · exact Subtype.ext hab

theorem not_isSolvable_of_triangle {G : Type*} [Group G] (H : Subgroup G) {a b : G} {m : ℕ}
    (hm : Nat.Coprime m 6) (ha : a ∈ H) (hb : b ∈ H) (hoa : orderOf a = 2) (hob : orderOf b = 3)
    (hoab : orderOf (a * b) = m) : ¬ Group.IsSolvable ↥H := by
  have ha2 : a * a = 1 := by
    have := pow_orderOf_eq_one a
    rwa [hoa, pow_two] at this
  have hb3 : b * b * b = 1 := by
    have := pow_orderOf_eq_one b
    rwa [hob, pow_succ, pow_two] at this
  have habm : (a * b) ^ m = 1 := by
    have := pow_orderOf_eq_one (a * b)
    rwa [hoab] at this
  have ha1 : a ≠ 1 := fun h => by
    rw [h, orderOf_one] at hoa
    exact absurd hoa (by norm_num)
  have hP := isPerfect_closure_triangle hm ha2 hb3 habm
  have hle : closure ({a, b} : Set G) ≤ H := by
    rw [Subgroup.closure_le]
    intro z hz
    rcases hz with h | h
    · rw [h]; exact ha
    · rw [Set.mem_singleton_iff] at h
      rw [h]; exact hb
  have hamem : a ∈ closure ({a, b} : Set G) := subset_closure (Set.mem_insert _ _)
  have : Nontrivial ↥(closure ({a, b} : Set G)) :=
    ⟨⟨⟨a, hamem⟩, 1, fun h => ha1 (congrArg Subtype.val h)⟩⟩
  intro hsolv
  have hs : Group.IsSolvable ↥(closure ({a, b} : Set G)) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  exact Group.IsPerfect.not_isSolvable _ hs

end CFSG.EvenSporadicStandard.Induction.AutBound
