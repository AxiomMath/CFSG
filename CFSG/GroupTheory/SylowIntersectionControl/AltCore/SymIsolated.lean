module

public import CFSG.GroupTheory.SylowIntersectionControl.IsolatedEmbedded
import CFSG.RankThree.PartOne.CTP.StrongPGlue

public section

namespace CFSG.GroupTheory.AltCore

open Equiv Equiv.Perm Subgroup CFSG.RankThree.PartOne.StrongP
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

section Swap

variable {α : Type*} [DecidableEq α]

private def CentClosed {γ : Type*} [Group γ] (Q : Subgroup γ) : Prop :=
  ∀ t ∈ Q, t ≠ 1 → t ^ 2 = 1 → ∀ s, Commute t s → s ∈ Q

private theorem commute_swap_of_fix {f : Perm α} {a b : α} (ha : f a = a) (hb : f b = b) :
    Commute f (swap a b) :=
  (mul_swap_eq_swap_mul f a b).trans (by rw [ha, hb])

private theorem commute_swap_swap {a b c d : α} (hca : c ≠ a) (hcb : c ≠ b) (hda : d ≠ a)
    (hdb : d ≠ b) : Commute (swap a b) (swap c d) :=
  commute_swap_of_fix (swap_apply_of_ne_of_ne hca hcb) (swap_apply_of_ne_of_ne hda hdb)

private theorem swap_sq (a b : α) : swap a b ^ 2 = 1 := by
  rw [sq, swap_mul_self]

private theorem swap_mul_swap_ne_one_sq {a b c d : α} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) :
    swap a b * swap c d ≠ 1 ∧ (swap a b * swap c d) ^ 2 = 1 := by
  refine ⟨fun h => hab ?_, ?_⟩
  · have := congrArg (fun f : Perm α => f a) h
    simp only [Perm.mul_apply, swap_apply_of_ne_of_ne hac had, swap_apply_left,
      Perm.one_apply] at this
    exact this.symm
  · rw [(commute_swap_swap hac.symm hbc.symm had.symm hbd.symm).mul_pow, swap_sq, swap_sq,
      one_mul]

private theorem swap_mem_of_disjoint {Q : Subgroup (Perm α)} (hQ : CentClosed Q) {a b c d : α}
    (hab : a ≠ b) (h : swap a b ∈ Q) (hca : c ≠ a) (hcb : c ≠ b) (hda : d ≠ a) (hdb : d ≠ b) :
    swap c d ∈ Q :=
  hQ _ h (swap_eq_one_iff.not.mpr hab) (swap_sq a b) _ (commute_swap_swap hca hcb hda hdb)

private theorem commute_swap_mul_swap {a b x y : α} (hab : a ≠ b) (hax : a ≠ x) (hay : a ≠ y)
    (hbx : b ≠ x) (hby : b ≠ y) (hxy : x ≠ y) :
    Commute (swap a b * swap x y) (swap a x * swap b y) := by
  refine Equiv.ext fun z => ?_
  simp only [Perm.mul_apply, swap_apply_def]
  grind

private theorem swap_mem_of_four {Q : Subgroup (Perm α)} (hQ : CentClosed Q) {a b x y : α}
    (hab : a ≠ b) (hax : a ≠ x) (hay : a ≠ y) (hbx : b ≠ x) (hby : b ≠ y) (hxy : x ≠ y)
    (h : swap a b ∈ Q) : swap a x ∈ Q := by
  have h1 : swap x y ∈ Q := swap_mem_of_disjoint hQ hab h hax.symm hbx.symm hay.symm hby.symm
  obtain ⟨hu1, hu2⟩ := swap_mul_swap_ne_one_sq hab hax hay hbx hby
  have hv : swap a x * swap b y ∈ Q :=
    hQ _ (Q.mul_mem h h1) hu1 hu2 _ (commute_swap_mul_swap hab hax hay hbx hby hxy)
  obtain ⟨hv1, hv2⟩ := swap_mul_swap_ne_one_sq hax hab hay hbx.symm hxy
  exact hQ _ hv hv1 hv2 _ ((Commute.refl _).mul_left (commute_swap_swap hab hay hbx.symm hxy))

private theorem eq_top_of_star [Finite α] {Q : Subgroup (Perm α)} {a : α}
    (h : ∀ x, swap a x ∈ Q) : Q = ⊤ := by
  refine eq_top_iff.mpr ?_
  rw [← Perm.closure_isSwap, closure_le]
  rintro _ ⟨x, y, -, rfl⟩
  have hx : swap x a ∈ Q := by
    rw [swap_comm]
    exact h x
  exact SubmonoidClass.swap_mem_trans Q hx (h y)

private theorem exists_ne_three [Fintype α] (h : 4 ≤ Fintype.card α) (a b x : α) :
    ∃ y : α, y ≠ a ∧ y ≠ b ∧ y ≠ x := by
  have h3 : ({a, b, x} : Finset α).card ≤ 3 := Finset.card_le_three
  obtain ⟨y, -, hy⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := ({a, b, x} : Finset α))
    (t := Finset.univ) (by rw [Finset.card_univ]; omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
  exact ⟨y, hy.1, hy.2.1, hy.2.2⟩

private theorem eq_top_of_swap_mem [Fintype α] {Q : Subgroup (Perm α)} (hQ : CentClosed Q)
    (h4 : 4 ≤ Fintype.card α) {a b : α} (hab : a ≠ b) (h : swap a b ∈ Q) : Q = ⊤ := by
  refine eq_top_of_star (a := a) fun x => ?_
  by_cases hxa : a = x
  · rw [← hxa, swap_self]
    exact Q.one_mem
  by_cases hxb : x = b
  · rw [hxb]
    exact h
  obtain ⟨y, hya, hyb, hyx⟩ := exists_ne_three h4 a b x
  exact swap_mem_of_four hQ hab hxa hya.symm (Ne.symm hxb) hyb.symm hyx.symm h

end Swap

section Embedded

private theorem not_isStronglyPEmbedded_of_card_le_two {β : Type*} [Fintype β] [DecidableEq β]
    (h2 : Fintype.card β ≤ 2) (M : Subgroup (Perm β)) : ¬ IsStronglyPEmbedded 2 M := by
  rintro ⟨hne, hdvd, -⟩
  have hcard : Nat.card (Perm β) ≤ 2 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card]
    calc (Fintype.card β).factorial ≤ (2 : ℕ).factorial := Nat.factorial_le h2
      _ = 2 := Nat.factorial_two
  have hle : Nat.card M ≤ Nat.card (Perm β) :=
    Nat.le_of_dvd Nat.card_pos (card_subgroup_dvd_card M)
  have h2le : 2 ≤ Nat.card M := Nat.le_of_dvd Nat.card_pos hdvd
  exact hne (eq_top_of_card_eq M (by omega))

private theorem centClosed_of_isStronglyPEmbedded {γ : Type*} [Group γ] {Q : Subgroup γ}
    (hQ : IsStronglyPEmbedded 2 Q) : CentClosed Q := fun _ ht ht1 ht2 _ hts =>
  hQ.centralizer_le ht1 ht2 ht (mem_centralizer_singleton_iff.mpr hts.eq.symm)

private theorem exists_conj_swap_mem {β : Type*} [Fintype β] [DecidableEq β]
    {M : Subgroup (Perm β)} (hM : IsStronglyPEmbedded 2 M) (a b : β) :
    ∃ g : Perm β, swap a b ∈ conjSub g M := by
  obtain ⟨S, hS⟩ := (isPGroup_zpowers_of_pow_eq_one (swap_sq a b)).exists_le_sylow
  obtain ⟨g, hg⟩ := hM.exists_conj_ge (P := (S : Subgroup (Perm β)))
    ⟨le_top, S.isPGroup', by rw [relIndex_top_right]; exact S.not_dvd_index⟩
  exact ⟨g, hg (hS (mem_zpowers _))⟩

end Embedded

theorem card_eq_three_of_isPIsolatedOver_perm {β : Type} [Fintype β] [DecidableEq β]
    (h : IsPIsolatedOver 2 (⊤ : Subgroup (Perm β)) ⊥) : Fintype.card β = 3 := by
  obtain ⟨M, hM⟩ := isPIsolatedOver_top_bot_iff.mp h
  by_contra hne
  rcases Nat.lt_or_ge (Fintype.card β) 3 with h3 | h3
  · exact not_isStronglyPEmbedded_of_card_le_two (by omega) M hM
  · obtain ⟨a, b, hab⟩ := Fintype.one_lt_card_iff.mp (by omega : 1 < Fintype.card β)
    obtain ⟨g, hg⟩ := exists_conj_swap_mem hM a b
    exact (hM.conj g).1
      (eq_top_of_swap_mem (centClosed_of_isStronglyPEmbedded (hM.conj g)) (by omega) hab hg)

end CFSG.GroupTheory.AltCore
