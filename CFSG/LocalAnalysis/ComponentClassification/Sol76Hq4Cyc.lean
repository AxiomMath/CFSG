module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic

public section

namespace CFSG.ComponentClassification.Sol76T13.Hq4

open Subgroup

theorem eq_of_involution_of_isCyclic {C : Type*} [Group C] [Finite C] [IsCyclic C] {x y : C}
    (hx2 : x * x = 1) (hy2 : y * y = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  classical
  have := Fintype.ofFinite C
  by_contra hne
  have hle := IsCyclic.card_pow_eq_one_le (α := C) (n := 2) (by norm_num)
  have hsub : ({1, x, y} : Finset C) ⊆ Finset.univ.filter (fun a => a ^ 2 = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl
    · exact one_pow 2
    · rw [pow_two]; exact hx2
    · rw [pow_two]; exact hy2
  have h3 : ({1, x, y} : Finset C).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [Ne.symm hx1, Ne.symm hy1]),
      Finset.card_pair hne]
  have := Finset.card_le_card hsub
  omega

theorem mem_map_of_involution {M G : Type*} [Group M] [Finite M] [Group G] (h : M →* G)
    {C : Subgroup M} (h2 : ∀ m : M, (∃ k : ℕ, m ^ (2 ^ k) = 1) → m ∈ C) {z : G}
    (hz : z ∈ h.range) (hz2 : z * z = 1) : z ∈ C.map h := by
  obtain ⟨m, rfl⟩ := hz
  obtain ⟨k, r, hr, hmr⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos m).ne' 2 (by norm_num)
  have hm2 : (m ^ r) ^ (2 ^ k) = 1 := by
    rw [← pow_mul, mul_comm, ← hmr, pow_orderOf_eq_one]
  have hodd : Odd r := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hr)
  obtain ⟨s, rfl⟩ := hodd
  refine ⟨m ^ (2 * s + 1), h2 _ ⟨k, hm2⟩, ?_⟩
  rw [map_pow, pow_succ, pow_mul, pow_two, hz2, one_pow, one_mul]

theorem eq_of_involution_of_le_cyclic {M G : Type*} [Group M] [Finite M] [Group G] (h : M →* G)
    {C : Subgroup M} (hC : IsCyclic C) (h2 : ∀ m : M, (∃ k : ℕ, m ^ (2 ^ k) = 1) → m ∈ C)
    {x y : G} (hx : x ∈ h.range) (hy : y ∈ h.range) (hx2 : x * x = 1) (hy2 : y * y = 1)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  have : IsCyclic ↥(C.map h) := by
    have : IsCyclic ↥C := hC
    exact isCyclic_of_surjective (h.subgroupMap C) (MonoidHom.subgroupMap_surjective h C)
  have : Finite ↥(C.map h) := Finite.of_surjective _ (MonoidHom.subgroupMap_surjective h C)
  have e := eq_of_involution_of_isCyclic
    (x := (⟨x, mem_map_of_involution h h2 hx hx2⟩ : ↥(C.map h)))
    (y := ⟨y, mem_map_of_involution h h2 hy hy2⟩) (Subtype.ext hx2) (Subtype.ext hy2)
    (fun e => hx1 (congrArg Subtype.val e)) (fun e => hy1 (congrArg Subtype.val e))
  exact congrArg Subtype.val e

theorem eq_of_involution_of_le_range {A M G : Type*} [Group A] [IsCyclic A] [Group M] [Finite M]
    [Group G] (ι : A →* M) (h : M →* G) (h2 : ∀ m : M, (∃ k : ℕ, m ^ (2 ^ k) = 1) → m ∈ ι.range)
    {x y : G} (hx : x ∈ h.range) (hy : y ∈ h.range) (hx2 : x * x = 1) (hy2 : y * y = 1)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y :=
  eq_of_involution_of_le_cyclic h
    (isCyclic_of_surjective ι.rangeRestrict ι.rangeRestrict_surjective) h2 hx hy hx2 hy2 hx1 hy1

theorem eq_one_of_pow_two_pow_zmod {a : ℕ} (ha : ¬ 2 ∣ a) {x : Multiplicative (ZMod a)} {k : ℕ}
    (hx : x ^ (2 ^ k) = 1) : x = 1 := by
  have hu : IsUnit ((2 ^ k : ℕ) : ZMod a) := (ZMod.isUnit_iff_coprime _ _).mpr
    (Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr ha))
  have h1 : ((2 ^ k : ℕ) : ZMod a) * x.toAdd = 0 := by
    rw [← nsmul_eq_mul, ← toAdd_pow, hx, toAdd_one]
  exact Multiplicative.toAdd.injective ((hu.mul_right_eq_zero.mp h1).trans toAdd_one.symm)

theorem eq_of_involution_of_table {a b c d : ℕ} {G : Type*} [Group G]
    [Finite ((Multiplicative (ZMod a) × Multiplicative (ZMod b)) ×
      (Multiplicative (ZMod c) × Multiplicative (ZMod d)))]
    (h : (Multiplicative (ZMod a) × Multiplicative (ZMod b)) ×
      (Multiplicative (ZMod c) × Multiplicative (ZMod d)) →* G)
    (hb : ¬ 2 ∣ b) (hd : ¬ 2 ∣ d) (hac : ¬ 2 ∣ a ∨ ¬ 2 ∣ c) {x y : G} (hx : x ∈ h.range)
    (hy : y ∈ h.range) (hx2 : x * x = 1) (hy2 : y * y = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1) :
    x = y := by
  have hcomp : ∀ m : (Multiplicative (ZMod a) × Multiplicative (ZMod b)) ×
      (Multiplicative (ZMod c) × Multiplicative (ZMod d)), ∀ k : ℕ, m ^ (2 ^ k) = 1 →
      m.1.1 ^ (2 ^ k) = 1 ∧ m.1.2 ^ (2 ^ k) = 1 ∧ m.2.1 ^ (2 ^ k) = 1 ∧
        m.2.2 ^ (2 ^ k) = 1 := fun m k hm =>
    ⟨congrArg (fun m => m.1.1) hm, congrArg (fun m => m.1.2) hm,
      congrArg (fun m => m.2.1) hm, congrArg (fun m => m.2.2) hm⟩
  rcases hac with ha | hc
  · refine eq_of_involution_of_le_range
      ((MonoidHom.inr _ _).comp (MonoidHom.inl (Multiplicative (ZMod c))
        (Multiplicative (ZMod d)))) h ?_ hx hy hx2 hy2 hx1 hy1
    rintro ⟨⟨m₁, m₂⟩, ⟨m₃, m₄⟩⟩ ⟨k, hk⟩
    obtain ⟨h₁, h₂, -, h₄⟩ := hcomp _ k hk
    dsimp only at h₁ h₂ h₄
    refine ⟨m₃, ?_⟩
    simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inl_apply,
      MonoidHom.inr_apply]
    rw [eq_one_of_pow_two_pow_zmod ha h₁, eq_one_of_pow_two_pow_zmod hb h₂,
      eq_one_of_pow_two_pow_zmod hd h₄]
    rfl
  · refine eq_of_involution_of_le_range
      ((MonoidHom.inl _ _).comp (MonoidHom.inl (Multiplicative (ZMod a))
        (Multiplicative (ZMod b)))) h ?_ hx hy hx2 hy2 hx1 hy1
    rintro ⟨⟨m₁, m₂⟩, ⟨m₃, m₄⟩⟩ ⟨k, hk⟩
    obtain ⟨-, h₂, h₃, h₄⟩ := hcomp _ k hk
    dsimp only at h₂ h₃ h₄
    refine ⟨m₁, ?_⟩
    simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inl_apply]
    rw [eq_one_of_pow_two_pow_zmod hb h₂, eq_one_of_pow_two_pow_zmod hc h₃,
      eq_one_of_pow_two_pow_zmod hd h₄]
    rfl

end CFSG.ComponentClassification.Sol76T13.Hq4
