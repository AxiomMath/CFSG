module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.KFactsAbs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.KFacts

open CFSG.RankThree.PartTwo.Sec4.Item434AltPerm
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open Equiv Equiv.Perm

theorem sign_eq_one_of_pow {α : Type*} [DecidableEq α] [Fintype α] {x : Perm α} {k : ℕ}
    (h : x ^ 3 ^ k = 1) : sign x = 1 := by
  have h1 : sign x ^ 3 ^ k = 1 := by rw [← map_pow, h, map_one]
  rw [Int.units_pow_eq_pow_mod_two, Nat.odd_iff.1 (Odd.pow (by decide : Odd (3 : ℕ))),
    pow_one] at h1
  exact h1

theorem card3_alt12 : (Nat.card ↥(alternatingGroup (Fin 12))).factorization 3 = 5 := by
  have h := Subgroup.card_mul_index (alternatingGroup (Fin 12))
  rw [alternatingGroup.index_eq_two] at h
  have h2 := factorization_twelve
  rw [← h, Nat.factorization_mul Nat.card_pos.ne' (by norm_num), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 2), add_zero] at h2
  exact h2

theorem outer_alt12 : ¬ 3 ∣ Nat.card (Outer ↥(alternatingGroup (Fin 12))) :=
  CFSG.AGLEmbedding.not_dvd_card_outer_alternatingGroup 12 (by norm_num) 3 Nat.prime_three
    (by norm_num)

theorem W12_le_alt : W12 12 ≤ alternatingGroup (Fin 12) := by
  intro x hx
  obtain ⟨k, hk⟩ := isPGroup_W12 w12Facts ⟨x, hx⟩
  exact Perm.mem_alternatingGroup.2 (sign_eq_one_of_pow (k := k) (congrArg Subtype.val hk))

theorem tt_c1_ne : tt 12 * c1 12 ≠ c1 12 * tt 12 := by
  intro h
  have h1 := w12Facts.w.conj1
  have h2 : tt 12 * c1 12 * (tt 12)⁻¹ = c1 12 := by rw [h]; group
  have hne : c2 12 ≠ c1 12 := by decide +kernel
  exact hne (h1.symm.trans h2)

@[expose] def vecE (v : Fin 3 → ZMod 3) : Perm (Fin 12) :=
  c1 12 ^ (v 0).val * c3 12 ^ (v 1).val * dd 12 ^ (v 2).val

theorem vecE_add : ∀ v w : Fin 3 → ZMod 3, vecE (v + w) = vecE v * vecE w := by decide +kernel

theorem vecE_inj : ∀ v : Fin 3 → ZMod 3, vecE v = 1 → v = 0 := by decide +kernel

@[expose] def vecEHom : Multiplicative (Fin 3 → ZMod 3) →* Perm (Fin 12) where
  toFun v := vecE (Multiplicative.toAdd v)
  map_one' := by simp [vecE]
  map_mul' u v := vecE_add _ _

theorem vecEHom_injective : Function.Injective vecEHom := by
  rw [injective_iff_map_eq_one]
  intro v hv
  exact Multiplicative.toAdd.injective (vecE_inj _ hv)

theorem card_E0 : Nat.card vecEHom.range = 3 ^ 3 := card_range_three vecEHom vecEHom_injective

theorem E0_le_alt : vecEHom.range ≤ alternatingGroup (Fin 12) := by
  intro x hx
  exact Perm.mem_alternatingGroup.2 (sign_eq_one_of_pow (k := 1)
    (by simpa using (isElemAbelian_range_three vecEHom).2 x hx))

@[expose] def u1 : Perm (Fin 12) := swap 0 1 * swap 2 3

@[expose] def u2 : Perm (Fin 12) := swap 0 2 * swap 1 3

@[expose] def u3 : Perm (Fin 12) := swap 0 3 * swap 1 2

@[expose] def V4 : Subgroup (Perm (Fin 12)) where
  carrier := {x | x = 1 ∨ x = u1 ∨ x = u2 ∨ x = u3}
  mul_mem' := by
    rintro a b (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) <;> simp only [Set.mem_setOf_eq] <;>
      decide +kernel
  one_mem' := Or.inl rfl
  inv_mem' := by
    rintro a (rfl | rfl | rfl | rfl) <;> simp only [Set.mem_setOf_eq] <;> decide +kernel

theorem V4_sq : ∀ x ∈ V4, x ^ 2 = 1 := by
  rintro x (rfl | rfl | rfl | rfl) <;> decide +kernel

theorem isPGroup_V4 : IsPGroup 2 V4 := fun g => ⟨1, Subtype.ext (by simpa using V4_sq _ g.2)⟩

theorem V4_ne_bot : V4 ≠ ⊥ := by
  intro h
  have h1 : u1 ∈ V4 := Or.inr (Or.inl rfl)
  rw [h, Subgroup.mem_bot] at h1
  exact absurd h1 (by decide +kernel)

theorem V4_le_alt : V4 ≤ alternatingGroup (Fin 12) := by
  rintro x (rfl | rfl | rfl | rfl)
  · exact one_mem _
  all_goals (rw [Perm.mem_alternatingGroup]; decide +kernel)

theorem gen_conj {g u : Perm (Fin 12)} (hg : g = c1 12 ∨ g = c3 12 ∨ g = dd 12)
    (hu : u = u1 ∨ u = u2 ∨ u = u3) :
    (g * u * g⁻¹ = 1 ∨ g * u * g⁻¹ = u1 ∨ g * u * g⁻¹ = u2 ∨ g * u * g⁻¹ = u3) := by
  rcases hg with rfl | rfl | rfl <;> rcases hu with rfl | rfl | rfl <;> decide +kernel

theorem gen_mem_normalizer {g : Perm (Fin 12)} (hg : g = c1 12 ∨ g = c3 12 ∨ g = dd 12) :
    g ∈ Subgroup.normalizer (V4 : Set (Perm (Fin 12))) := by
  apply mem_normalizer_of_forall_conj_mem
  rintro y (rfl | rfl | rfl | rfl)
  · simpa using one_mem V4
  · exact gen_conj hg (Or.inl rfl)
  · exact gen_conj hg (Or.inr (Or.inl rfl))
  · exact gen_conj hg (Or.inr (Or.inr rfl))

theorem E0_le_normalizer : vecEHom.range ≤ Subgroup.normalizer (V4 : Set (Perm (Fin 12))) := by
  rintro _ ⟨v, rfl⟩
  exact mul_mem (mul_mem (pow_mem (gen_mem_normalizer (Or.inl rfl)) _)
    (pow_mem (gen_mem_normalizer (Or.inr (Or.inl rfl))) _))
    (pow_mem (gen_mem_normalizer (Or.inr (Or.inr rfl))) _)

theorem kProfile_alt12 : KProfile ↥(alternatingGroup (Fin 12)) :=
  KProfile.of_subgroup _ card3_alt12 outer_alt12 (P := W12 12) W12_le_alt
    (by rw [card_W12 w12Facts]; norm_num) (a := tt 12) (b := c1 12)
    (Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)))
    (Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_left
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)))))
    tt_c1_ne E0_le_alt V4_le_alt (isElemAbelian_range_three vecEHom) card_E0 isPGroup_V4
    V4_ne_bot E0_le_normalizer

end CFSG.LocalAnalysis.GLTheoremA.CatB.KFacts
