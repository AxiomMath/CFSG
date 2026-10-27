module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_20A6

public section

namespace CFSG.QuasithinUnique.A6Rank

open Equiv Subgroup

@[expose] def c1 : alternatingGroup (Fin 6) :=
  ⟨c[0, 1, 2], by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

@[expose] def c2 : alternatingGroup (Fin 6) :=
  ⟨c[3, 4, 5], by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

@[expose] def g2 : alternatingGroup (Fin 6) :=
  ⟨c[0, 1, 3], by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

@[expose] def v1 : alternatingGroup (Fin 6) :=
  ⟨swap 0 1 * swap 2 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

@[expose] def v2 : alternatingGroup (Fin 6) :=
  ⟨swap 0 2 * swap 1 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

@[expose] def v3 : alternatingGroup (Fin 6) :=
  ⟨swap 0 3 * swap 1 2, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

set_option maxRecDepth 100000 in
theorem c1_pow : c1 ^ 3 = 1 := by decide

set_option maxRecDepth 100000 in
theorem c2_pow : c2 ^ 3 = 1 := by decide

set_option maxRecDepth 100000 in
theorem c1_ne : c1 ≠ 1 := by decide

set_option maxRecDepth 100000 in
theorem c2_ne : c2 ≠ 1 := by decide

set_option maxRecDepth 100000 in
theorem c12_comm : c1 * c2 = c2 * c1 := by decide

set_option maxRecDepth 100000 in
theorem c1_c2_ind : ∀ m n : Fin 3, c1 ^ (m : ℕ) = c2 ^ (n : ℕ) → m = 0 := by decide

set_option maxRecDepth 100000 in
theorem cen_triv :
    ∀ x : alternatingGroup (Fin 6), x * c1 = c1 * x → x * g2 = g2 * x → x = 1 := by
  decide +kernel

@[expose] def V4 : Subgroup (alternatingGroup (Fin 6)) where
  carrier := {x | x = 1 ∨ x = v1 ∨ x = v2 ∨ x = v3}
  mul_mem' := by
    set_option maxRecDepth 100000 in
    rintro x y (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) <;> decide
  one_mem' := Or.inl rfl
  inv_mem' := by
    set_option maxRecDepth 100000 in
    rintro x (rfl | rfl | rfl | rfl) <;> decide

set_option maxRecDepth 100000 in
theorem v1_ne : v1 ≠ 1 := by decide

theorem V4_ne_bot : V4 ≠ ⊥ := by
  intro h
  have : v1 ∈ V4 := Or.inr (Or.inl rfl)
  rw [h, Subgroup.mem_bot] at this
  exact v1_ne this

theorem V4_pGroup : IsPGroup 2 V4 := by
  intro x
  refine ⟨1, ?_⟩
  obtain ⟨x, hx⟩ := x
  apply Subtype.ext
  set_option maxRecDepth 100000 in
  rcases hx with (rfl | rfl | rfl | rfl) <;> decide

theorem c1_normalizes : c1 ∈ Subgroup.normalizer (V4 : Set (alternatingGroup (Fin 6))) := by
  apply Subgroup.mem_normalizer_fintype
  intro n hn
  set_option maxRecDepth 100000 in
  rcases hn with (rfl | rfl | rfl | rfl) <;>
    exact (by show _ = 1 ∨ _ = v1 ∨ _ = v2 ∨ _ = v3; decide)

theorem zpow_cases {G : Type*} [Group G] (x : G) (hx : x ^ 3 = 1) (i : ℤ) :
    ∃ r : Fin 3, x ^ i = x ^ (r : ℕ) := by
  have h3 : x ^ (3 : ℤ) = 1 := by simpa using hx
  have hnn : 0 ≤ i % 3 := Int.emod_nonneg i (by norm_num)
  have hlt : i % 3 < 3 := Int.emod_lt_of_pos i (by norm_num)
  refine ⟨⟨(i % 3).toNat, by omega⟩, ?_⟩
  rw [zpow_eq_zpow_emod i h3]
  simp only
  rw [← zpow_natCast, Int.toNat_of_nonneg hnn]

theorem zpow_ind (i j : ℤ) (h : c1 ^ i = c2 ^ j) : c1 ^ i = 1 := by
  obtain ⟨m, hm⟩ := zpow_cases c1 c1_pow i
  obtain ⟨n, hn⟩ := zpow_cases c2 c2_pow j
  rw [hm, hn] at h
  have := c1_c2_ind m n h
  rw [hm, this]
  simp

end CFSG.QuasithinUnique.A6Rank

namespace CFSG.QuasithinUnique

open Equiv Subgroup

theorem a6RankFacts : A6RankFacts := by
  intro X _ ⟨e⟩
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨e.symm A6Rank.c1, e.symm A6Rank.c2, ?_, ?_, ?_, ?_⟩
    · rw [MulEquiv.orderOf_eq]; exact orderOf_eq_prime A6Rank.c1_pow A6Rank.c1_ne
    · rw [MulEquiv.orderOf_eq]; exact orderOf_eq_prime A6Rank.c2_pow A6Rank.c2_ne
    · rw [← map_mul, A6Rank.c12_comm, map_mul]
    · rw [eq_bot_iff]
      rintro x ⟨hx1, hx2⟩
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx1
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hx2
      have h1 : A6Rank.c1 ^ i = A6Rank.c2 ^ j := by
        have := congrArg e hj
        simpa using this.symm
      have h2 := A6Rank.zpow_ind i j h1
      rw [Subgroup.mem_bot]
      have : e ((e.symm A6Rank.c1) ^ i) = 1 := by simpa using h2
      exact e.map_eq_one_iff.mp this
  · refine ⟨A6Rank.V4.map e.symm.toMonoidHom, ?_, ?_, e.symm A6Rank.c1, ?_, ?_⟩
    · intro h
      exact A6Rank.V4_ne_bot ((Subgroup.map_eq_bot_iff_of_injective _ e.symm.injective).mp h)
    · exact A6Rank.V4_pGroup.of_equiv
        (Subgroup.equivMapOfInjective A6Rank.V4 e.symm.toMonoidHom e.symm.injective)
    · rw [← Subgroup.map_equiv_normalizer_eq]
      exact ⟨A6Rank.c1, A6Rank.c1_normalizes, rfl⟩
    · rw [MulEquiv.orderOf_eq]; exact orderOf_eq_prime A6Rank.c1_pow A6Rank.c1_ne
  · intro x hx
    have h1 : e x * A6Rank.c1 = A6Rank.c1 * e x := by
      have := congrArg e (hx (e.symm A6Rank.c1))
      simpa using this.symm
    have h2 : e x * A6Rank.g2 = A6Rank.g2 * e x := by
      have := congrArg e (hx (e.symm A6Rank.g2))
      simpa using this.symm
    have := A6Rank.cen_triv (e x) h1 h2
    exact e.injective (by simpa using this)

end CFSG.QuasithinUnique
