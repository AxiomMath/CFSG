module

public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporInputs
public import CFSG.Sporadic.Schreier.J4SOutOdd

public section

namespace CFSG.ComponentClassification.RestrictedStd.Spor

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Sporadic.Schreier (fixSub mem_fixSub)

theorem map_fixSub_congr {G H : Type*} [Group G] [Group H] (e : G ≃* H) (α : MulAut G) :
    (fixSub α).map (e : G →* H) = fixSub (MulAut.congr e α) := by
  ext x
  rw [Subgroup.mem_map, mem_fixSub, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_fixSub] at hy
    simp [hy]
  · intro h
    refine ⟨e.symm x, ?_, by simp⟩
    rw [mem_fixSub, ← e.symm_apply_apply (α (e.symm x)), h]

@[expose] noncomputable def fixSubCongr {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (α : MulAut G) : fixSub α ≃* fixSub (MulAut.congr e α) :=
  (e.subgroupMap (fixSub α)).trans (MulEquiv.subgroupCongr (map_fixSub_congr e α))

theorem congr_mem_inner_iff {G H : Type*} [Group G] [Group H] (e : G ≃* H) (α : MulAut G) :
    MulAut.congr e α ∈ inner H ↔ α ∈ inner G := by
  rw [← inner_map_congr e]
  constructor
  · rintro ⟨β, hβ, h⟩
    rwa [show β = α from (MulAut.congr e).injective h] at hβ
  · intro h
    exact ⟨α, h, rfl⟩

theorem mem_inner_of_J4 {S : Type*} [Group S] (e : S ≃* NativeSporadic.J4) (α : MulAut S)
    (hα : orderOf α = 2) : α ∈ inner S := by
  by_contra hout
  have hodd : Odd (Nat.card (Outer S)) := by
    rw [@Sporadic.J4Schreier.card_outer_congr S Sporadic.J4.J _ (Subgroup.toGroup _)
      (e.trans (Sporadic.J4.seedEquiv Sporadic.J4.j4Facts.mat))]
    exact Sporadic.J4Schreier.CTU_J4_outer_automorphism_group_odd_order
  have hq2 : (QuotientGroup.mk α : Outer S) ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow, ← hα, pow_orderOf_eq_one, QuotientGroup.mk_one]
  have hq1 : (QuotientGroup.mk α : Outer S) ≠ 1 := fun h =>
    hout ((QuotientGroup.eq_one_iff α).1 h)
  have hdvd : orderOf (QuotientGroup.mk α : Outer S) ∣ Nat.card (Outer S) :=
    orderOf_dvd_natCard _
  rw [orderOf_eq_prime hq2 hq1] at hdvd
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hdvd)

@[expose] def kleinPerm : Subgroup (Equiv.Perm (Fin 10)) where
  carrier := (({1, Equiv.swap 0 1, Equiv.swap 2 3, Equiv.swap 0 1 * Equiv.swap 2 3} :
    Finset (Equiv.Perm (Fin 10))) : Set (Equiv.Perm (Fin 10)))
  mul_mem' := by
    intro a b ha hb
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at ha hb ⊢
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;> decide
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at ha ⊢
    rcases ha with rfl | rfl | rfl | rfl <;> decide

theorem mem_kleinPerm {a : Equiv.Perm (Fin 10)} : a ∈ kleinPerm ↔
    a = 1 ∨ a = Equiv.swap 0 1 ∨ a = Equiv.swap 2 3 ∨ a = Equiv.swap 0 1 * Equiv.swap 2 3 := by
  change a ∈ ((({1, Equiv.swap 0 1, Equiv.swap 2 3, Equiv.swap 0 1 * Equiv.swap 2 3} :
    Finset (Equiv.Perm (Fin 10))) : Set (Equiv.Perm (Fin 10)))) ↔ _
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]

theorem card_kleinPerm : Nat.card kleinPerm = 4 := by
  change Nat.card ((({1, Equiv.swap 0 1, Equiv.swap 2 3, Equiv.swap 0 1 * Equiv.swap 2 3} :
    Finset (Equiv.Perm (Fin 10))) : Set (Equiv.Perm (Fin 10)))) = 4
  rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
  decide

instance : IsMulCommutative kleinPerm :=
  ⟨⟨fun a b => Subtype.ext (by
    rcases mem_kleinPerm.1 a.2 with h | h | h | h <;>
      rcases mem_kleinPerm.1 b.2 with k | k | k | k <;>
      simp only [Subgroup.coe_mul, h, k] <;> decide)⟩⟩

theorem sq_of_mem_kleinPerm {a : Equiv.Perm (Fin 10)} (ha : a ∈ kleinPerm) : a ^ 2 = 1 := by
  rcases mem_kleinPerm.1 ha with rfl | rfl | rfl | rfl <;> decide

theorem exists_four_of_equiv_perm {K : Type*} [Group K] (φ : K ≃* Equiv.Perm (Fin 10)) :
    ∃ E : Subgroup K, Assembly.IsElemAbelian 2 E ∧ Nat.card E = 4 := by
  refine ⟨kleinPerm.map (φ.symm : Equiv.Perm (Fin 10) →* K), ⟨inferInstance, ?_⟩, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, sq_of_mem_kleinPerm ha, map_one]
  · rw [Subgroup.card_map_of_injective φ.symm.injective, card_kleinPerm]

theorem two_pow_factorization_card_perm_ten : 2 ^ (3628800 : ℕ).factorization 2 = 256 := by
  have h : (3628800 : ℕ) = 2 ^ 8 * 14175 := by norm_num
  rw [h, Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (show ¬ 2 ∣ 14175 by norm_num)]
  norm_num

@[expose] def HNOuterFixInput : Prop :=
  ∀ (S : Type) [Group S], (S ≃* NativeSporadic.HN) → ∀ α : MulAut S, orderOf α = 2 →
    α ∉ inner S → Nonempty (fixSub α ≃* Equiv.Perm (Fin 10))

theorem fourExactOuterInput_of_parts (hHN : HNOuterFixInput)
    (hB : ∀ (S : Type) [Group S], Nonempty (S ≃* NativeSporadic.B) → ∀ α : MulAut S, α ∈ inner S)
    (hM : ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → Nonempty (S ≃* NativeSporadic.M) →
      ∀ α : MulAut S, α ∈ inner S) :
    FourExactOuterInput := by
  intro S _ _ hS _ hiso α hα hout
  have nJ4 : IsEmpty (S ≃* NativeSporadic.J4) := ⟨fun e => hout (mem_inner_of_J4 e α hα)⟩
  have nB : IsEmpty (S ≃* NativeSporadic.B) := ⟨fun e => hout (hB S ⟨e⟩ α)⟩
  have nM : IsEmpty (S ≃* NativeSporadic.M) := ⟨fun e => hout (hM S hS ⟨e⟩ α)⟩
  have hHN' : Nonempty (S ≃* NativeSporadic.HN) := by
    rcases hiso with h | h | h | h
    · exact (h.elim nJ4.false).elim
    · exact h
    · exact (h.elim nB.false).elim
    · exact (h.elim nM.false).elim
  obtain ⟨e⟩ := hHN'
  obtain ⟨φ⟩ := hHN S e α hα hout
  have hcard : Nat.card (fixSub α) = 3628800 := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_perm, Nat.card_fin]
    rfl
  refine ⟨⟨e⟩, nJ4, nB, nM, ⟨φ⟩, hcard, ?_, exists_four_of_equiv_perm φ⟩
  rw [hcard]
  exact two_pow_factorization_card_perm_ten

end CFSG.ComponentClassification.RestrictedStd.Spor
