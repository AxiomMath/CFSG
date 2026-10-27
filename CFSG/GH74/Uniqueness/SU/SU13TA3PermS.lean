module

public import CFSG.GH74.Uniqueness.SU.SU13TA3Perm
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.GH74.Uniqueness.SU.SU13.TA.L10

open Equiv Equiv.Perm Subgroup

abbrev Sub7 : Type := {x : Fin 10 // x ∉ ({6, 7, 8} : Finset (Fin 10))}

theorem card_sub7 : Fintype.card Sub7 = 7 := by decide

instance : Nontrivial Sub7 :=
  Fintype.one_lt_card_iff_nontrivial.mp (by rw [card_sub7]; norm_num)

@[expose] def iota7 : alternatingGroup Sub7 →* alternatingGroup (Fin 10) :=
  ((Perm.ofSubtype : Perm Sub7 →* Perm (Fin 10)).comp
    (alternatingGroup Sub7).subtype).codRestrict (alternatingGroup (Fin 10)) (fun x => by
      rw [Perm.mem_alternatingGroup]
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, Perm.sign_ofSubtype]
      exact Perm.mem_alternatingGroup.mp x.2)

theorem iota7_injective : Function.Injective iota7 := fun _ _ h =>
  Subtype.ext (Perm.ofSubtype_injective (congrArg Subtype.val h))

@[expose] def AS : Subgroup (alternatingGroup (Fin 10)) := iota7.range

theorem mem_AS_iff {σ : alternatingGroup (Fin 10)} :
    σ ∈ AS ↔ (σ : Perm (Fin 10)) 6 = 6 ∧ (σ : Perm (Fin 10)) 7 = 7 ∧ (σ : Perm (Fin 10)) 8 = 8 := by
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨?_, ?_, ?_⟩ <;>
      exact Perm.ofSubtype_apply_of_not_mem _ (by decide)
  · rintro ⟨h6, h7, h8⟩
    have hmem : ∀ x : Fin 10, (x ∉ ({6, 7, 8} : Finset (Fin 10))) ↔
        ((σ : Perm (Fin 10)) x ∉ ({6, 7, 8} : Finset (Fin 10))) := by
      intro x
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      constructor
      · rintro ⟨hx6, hx7, hx8⟩
        refine ⟨fun h => hx6 ?_, fun h => hx7 ?_, fun h => hx8 ?_⟩
        · exact (σ : Perm (Fin 10)).injective (h.trans h6.symm)
        · exact (σ : Perm (Fin 10)).injective (h.trans h7.symm)
        · exact (σ : Perm (Fin 10)).injective (h.trans h8.symm)
      · rintro ⟨hx6, hx7, hx8⟩
        refine ⟨fun h => hx6 ?_, fun h => hx7 ?_, fun h => hx8 ?_⟩
        · rw [h, h6]
        · rw [h, h7]
        · rw [h, h8]
    have hmoved : ∀ x : Fin 10, (σ : Perm (Fin 10)) x ≠ x → x ∉ ({6, 7, 8} : Finset (Fin 10)) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨fun h => hx ?_, fun h => hx ?_, fun h => hx ?_⟩
      · rw [h, h6]
      · rw [h, h7]
      · rw [h, h8]
    set τ : Perm Sub7 := (σ : Perm (Fin 10)).subtypePerm (fun x => (hmem x).symm) with hτ
    have hτσ : Perm.ofSubtype τ = (σ : Perm (Fin 10)) :=
      Perm.ofSubtype_subtypePerm (fun x => (hmem x).symm) hmoved
    have hτA : τ ∈ alternatingGroup Sub7 := by
      rw [Perm.mem_alternatingGroup, ← Perm.sign_ofSubtype, hτσ]
      exact Perm.mem_alternatingGroup.mp σ.2
    exact ⟨⟨τ, hτA⟩, Subtype.ext hτσ⟩

theorem card_AS : Nat.card AS = 2520 := by
  rw [AS, ← Nat.card_congr (MonoidHom.ofInjective iota7_injective).toEquiv,
    nat_card_alternatingGroup, Nat.card_eq_fintype_card, card_sub7]
  decide

theorem isSimpleGroup_AS : IsSimpleGroup AS := by
  have : IsSimpleGroup (alternatingGroup Sub7) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, card_sub7]; norm_num)
  exact (MonoidHom.ofInjective iota7_injective).symm.isSimpleGroup

theorem commute_ec_of_mem_AS {σ : alternatingGroup (Fin 10)} (hσ : σ ∈ AS) : Commute σ ec := by
  obtain ⟨h6, h7, h8⟩ := mem_AS_iff.mp hσ
  have hpc : ∀ x : Fin 10, x ∉ ({6, 7, 8} : Finset (Fin 10)) → pc x = x := by decide
  have hd : Equiv.Perm.Disjoint (σ : Perm (Fin 10)) pc := fun x => by
    by_cases hx : x ∈ ({6, 7, 8} : Finset (Fin 10))
    · left
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    · right
      exact hpc x hx
  exact Subtype.ext hd.commute.eq

theorem disjoint_zpowers_ec_AS : Disjoint (zpowers ec) AS := by
  rw [Subgroup.disjoint_def]
  intro x hx hxA
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h3 : ec ^ (3 : ℤ) = 1 := by exact_mod_cast ec_pow_three
  rw [zpow_eq_zpow_emod k h3] at hxA ⊢
  have hk : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hk with hk | hk | hk
  · rw [hk]; rfl
  · rw [hk] at hxA
    exact absurd (mem_AS_iff.mp hxA).1 (by decide)
  · rw [hk] at hxA
    exact absurd (mem_AS_iff.mp hxA).1 (by decide)

theorem cycleType_eq_of_sq_eq_one_of_mem_AS {σ : alternatingGroup (Fin 10)} (hσ : σ ∈ AS)
    (h2 : σ ^ 2 = 1) (h1 : σ ≠ 1) : (σ : Perm (Fin 10)).cycleType = {2, 2} := by
  have h2' : (σ : Perm (Fin 10)) ^ 2 = 1 := by rw [← Subgroup.coe_pow, h2, OneMemClass.coe_one]
  have h1' : (σ : Perm (Fin 10)) ≠ 1 := fun h => h1 (Subtype.ext h)
  have hsign : Perm.sign (σ : Perm (Fin 10)) = 1 := Perm.mem_alternatingGroup.mp σ.2
  obtain ⟨h6, h7, h8⟩ := mem_AS_iff.mp hσ
  obtain ⟨k, hk⟩ : ∃ k, (σ : Perm (Fin 10)).cycleType = Multiset.replicate k 2 :=
    ⟨_, Perm.cycleType_of_pow_prime_eq_one h2'⟩
  have hsupp : (σ : Perm (Fin 10)).support.card ≤ 7 := by
    have hsub : (σ : Perm (Fin 10)).support ⊆ ({6, 7, 8} : Finset (Fin 10))ᶜ := by
      intro x hx
      rw [Finset.mem_compl]
      simp only [Finset.mem_insert, Finset.mem_singleton, Perm.mem_support] at hx ⊢
      rintro (rfl | rfl | rfl) <;> contradiction
    calc (σ : Perm (Fin 10)).support.card ≤ (({6, 7, 8} : Finset (Fin 10))ᶜ).card :=
        Finset.card_le_card hsub
      _ = 7 := by decide
  have hsum := Perm.sum_cycleType (σ : Perm (Fin 10))
  rw [hk, Multiset.sum_replicate, smul_eq_mul] at hsum
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact h1' (Perm.cycleType_eq_zero.mp hk)
  rw [Perm.sign_of_cycleType, hk, Multiset.sum_replicate, Multiset.card_replicate,
    smul_eq_mul] at hsign
  have hk3 : k ≤ 3 := by omega
  have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk0
  rw [hk]
  interval_cases k
  · exact absurd hsign (by decide)
  · rfl
  · exact absurd hsign (by decide)

theorem pow_four_eq_one_of_pow_eight_of_mem_AS {σ : alternatingGroup (Fin 10)} (hσ : σ ∈ AS)
    (h8 : σ ^ 8 = 1) : σ ^ 4 = 1 := by
  have h8' : (σ : Perm (Fin 10)) ^ 8 = 1 := by rw [← Subgroup.coe_pow, h8, OneMemClass.coe_one]
  obtain ⟨h6, h7, h8x⟩ := mem_AS_iff.mp hσ
  have hsupp : (σ : Perm (Fin 10)).support.card ≤ 7 := by
    have hsub : (σ : Perm (Fin 10)).support ⊆ ({6, 7, 8} : Finset (Fin 10))ᶜ := by
      intro x hx
      rw [Finset.mem_compl]
      simp only [Finset.mem_insert, Finset.mem_singleton, Perm.mem_support] at hx ⊢
      rintro (rfl | rfl | rfl) <;> contradiction
    calc (σ : Perm (Fin 10)).support.card ≤ (({6, 7, 8} : Finset (Fin 10))ᶜ).card :=
        Finset.card_le_card hsub
      _ = 7 := by decide
  have hdvd8 : orderOf (σ : Perm (Fin 10)) ∣ 8 := orderOf_dvd_of_pow_eq_one h8'
  have hpart : ∀ c ∈ (σ : Perm (Fin 10)).cycleType, c ∣ 4 := by
    intro c hc
    have h1 : c ∣ 8 := by
      have := Multiset.dvd_lcm hc
      rw [Perm.lcm_cycleType] at this
      exact this.trans hdvd8
    have h2 : c ≤ 7 := (Perm.le_card_support_of_mem_cycleType hc).trans hsupp
    have h3 : 2 ≤ c := Perm.two_le_of_mem_cycleType hc
    interval_cases c <;> simp_all
  have hord : orderOf (σ : Perm (Fin 10)) ∣ 4 := by
    rw [← Perm.lcm_cycleType]
    exact Multiset.lcm_dvd.mpr hpart
  have h4' : (σ : Perm (Fin 10)) ^ 4 = 1 := orderOf_dvd_iff_pow_eq_one.mp hord
  exact Subtype.ext (by rw [Subgroup.coe_pow, OneMemClass.coe_one]; exact h4')

@[expose] def sig0 : alternatingGroup (Fin 10) :=
  ⟨swap 0 1 * swap 2 3, Perm.mem_alternatingGroup.mpr (by decide)⟩

theorem sig0_mem_AS : sig0 ∈ AS := mem_AS_iff.mpr ⟨by decide, by decide, by decide⟩

theorem cycleType_sig0 : (sig0 : Perm (Fin 10)).cycleType = {2, 2} :=
  cycleType_swap_mul_swap_of_nodup (by decide)

end CFSG.GH74.Uniqueness.SU.SU13.TA.L10
