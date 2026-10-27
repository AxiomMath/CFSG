module

public import CFSG.GroupTheory.SylowIntersectionControl.IsolatedEmbedded
import CFSG.GroupTheory.SylowIntersectionControl.AltNotIsolated
import CFSG.GroupTheory.SylowIntersectionControl.IsolatedCore
import CFSG.RankThree.PartOne.CTP.StrongPGlue
import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCoverPerm

public section

namespace CFSG.GroupTheory.AltCore

open Equiv Equiv.Perm Subgroup CFSG.RankThree.PartOne.StrongP
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

section Small

private theorem not_isPIsolatedOver_of_odd {G : Type*} [Group G] {K : Subgroup G}
    (hK : Odd (Nat.card K)) (H : Subgroup G) : ¬ IsPIsolatedOver 2 K H := by
  rintro ⟨S, T, hS, hT, hST⟩
  have hbot : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ K → P = ⊥ := fun P hP hPK =>
    card_eq_one.mp <| hP.card_eq_or_dvd.resolve_right fun h2 =>
      (Nat.not_even_iff_odd.mpr hK) (even_iff_two_dvd.mpr (h2.trans (card_dvd_of_le hPK)))
  obtain rfl : S = T := (hbot S hS.isPGroup hS.le).trans (hbot T hT.isPGroup hT.le).symm
  exact hST (Relation.EqvGen.refl _)

private theorem odd_card_alternatingGroup_of_card_le_three {β : Type*} [Fintype β]
    [DecidableEq β] (h : Fintype.card β ≤ 3) : Odd (Nat.card (alternatingGroup β)) := by
  rcases subsingleton_or_nontrivial β with hs | hn
  · rw [Nat.card_unique]
    exact odd_one
  · rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card]
    have h2 : 2 ≤ Fintype.card β := Fintype.one_lt_card_iff_nontrivial.mpr hn
    interval_cases Fintype.card β <;> decide

private theorem isPIsolatedOver_top_of_alternatingGroup {γ : Type*} [Fintype γ] [DecidableEq γ]
    (h : IsPIsolatedOver 2 (alternatingGroup γ) (⊥ : Subgroup (Perm γ))) :
    IsPIsolatedOver 2 (⊤ : Subgroup (alternatingGroup γ)) ⊥ := by
  have := (isPIsolatedOver_subgroupOf_iff (p := 2) (bot_le : ⊥ ≤ alternatingGroup γ)
    le_rfl).mpr h
  rwa [subgroupOf_self, bot_subgroupOf] at this

private theorem not_isPIsolatedOver_alternatingGroup_four {γ : Type*} [Fintype γ]
    [DecidableEq γ] (h4 : Fintype.card γ = 4) :
    ¬ IsPIsolatedOver 2 (⊤ : Subgroup (alternatingGroup γ)) ⊥ := by
  intro h
  have hc : Nat.card γ = 4 := by rw [Nat.card_eq_fintype_card, h4]
  have hN := alternatingGroup.normal_kleinFour hc
  have hcard := alternatingGroup.kleinFour_card_of_card_eq_four hc
  have hle := h.le_of_normal (X := alternatingGroup.kleinFour γ) IsPGroup.of_bot bot_le
    (normalizer_eq_top_iff.mpr inferInstance).ge le_top
    (IsPGroup.of_card (n := 2) (by rw [hcard]; norm_num)) (normalizer_eq_top_iff.mpr hN).ge
  have := card_eq_one.mpr (le_bot_iff.mp hle)
  omega

end Small

section Six

private def CentClosed {α : Type*} [Fintype α] [DecidableEq α] (Q : Subgroup (Perm α)) : Prop :=
  ∀ t ∈ Q, t ≠ 1 → t ^ 2 = 1 → ∀ s ∈ alternatingGroup α, Commute t s → s ∈ Q

private theorem exists_centClosed_of_isStronglyPEmbedded {α : Type*} [Fintype α] [DecidableEq α]
    {M : Subgroup (alternatingGroup α)} (hM : IsStronglyPEmbedded 2 M) {u : Perm α}
    (hu : u ∈ alternatingGroup α) (hu2 : u ^ 2 = 1) :
    ∃ Q : Subgroup (Perm α), u ∈ Q ∧ CentClosed Q ∧ ¬ alternatingGroup α ≤ Q := by
  obtain ⟨S, hS⟩ := (isPGroup_zpowers_of_pow_eq_one (p := 2)
    (x := (⟨u, hu⟩ : alternatingGroup α)) (Subtype.ext hu2)).exists_le_sylow
  obtain ⟨g, hg⟩ := hM.exists_conj_ge (P := (S : Subgroup (alternatingGroup α)))
    ⟨le_top, S.isPGroup', by rw [relIndex_top_right]; exact S.not_dvd_index⟩
  have hM' := hM.conj g
  refine ⟨(conjSub g M).map (alternatingGroup α).subtype,
    ⟨⟨u, hu⟩, hg (hS (mem_zpowers _)), rfl⟩, ?_, fun hle => hM'.1 (eq_top_iff.mpr fun x _ => ?_)⟩
  · rintro _ ⟨t, htM, rfl⟩ ht1 ht2 s hs hts
    refine ⟨⟨s, hs⟩, hM'.centralizer_le (fun h => ht1 (by simp [h])) (Subtype.ext ht2) htM ?_,
      rfl⟩
    exact mem_centralizer_singleton_iff.mpr (Subtype.ext hts.eq.symm)
  · obtain ⟨y, hy, hyx⟩ := hle x.2
    rwa [show y = x from Subtype.ext hyx] at hy

private theorem swap_mul_swap_mem_ne_sq {α : Type*} [Fintype α] [DecidableEq α] {a b c d : α}
    (h : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d) :
    swap a b * swap c d ∈ alternatingGroup α ∧ swap a b * swap c d ≠ 1 ∧
      (swap a b * swap c d) ^ 2 = 1 := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := h
  refine ⟨mul_mem_alternatingGroup_of_isSwap (swap_isSwap_iff.mpr hab)
      (swap_isSwap_iff.mpr hcd), fun h => hab ?_,
    CFSG.LocalAnalysis.ComponentInitial.swap_mul_swap_sq_of_ne hac had hbc.symm hbd⟩
  have := congrArg (fun f : Perm α => f a) h
  simp only [Perm.mul_apply, swap_apply_of_ne_of_ne hac had, swap_apply_left,
    Perm.one_apply] at this
  exact this.symm

private theorem swap_mul_swap_mem_of_commute {α : Type*} [Fintype α] [DecidableEq α]
    {Q : Subgroup (Perm α)} (hQ : CentClosed Q) {a b c d a' b' c' d' : α}
    (ht : swap a b * swap c d ∈ Q) (h : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d)
    (h' : a' ≠ b' ∧ a' ≠ c' ∧ a' ≠ d' ∧ b' ≠ c' ∧ b' ≠ d' ∧ c' ≠ d')
    (hc : swap a b * swap c d * (swap a' b' * swap c' d') =
      swap a' b' * swap c' d' * (swap a b * swap c d)) : swap a' b' * swap c' d' ∈ Q :=
  hQ _ ht (swap_mul_swap_mem_ne_sq h).2.1 (swap_mul_swap_mem_ne_sq h).2.2 _
    (swap_mul_swap_mem_ne_sq h').1 hc

private theorem swap_mul_swap_mem_of_mul_swap {α : Type*} [DecidableEq α]
    {Q : Subgroup (Perm α)} {o j k a b : α} (hj : swap o j * swap a b ∈ Q)
    (hk : swap o k * swap a b ∈ Q) : swap o j * swap o k ∈ Q := by
  simpa [mul_assoc] using Q.mul_mem hj (Q.inv_mem hk)

private theorem alternatingGroup_six_le {Q : Subgroup (Perm (Fin 6))} (hQ : CentClosed Q)
    (hu : swap 0 1 * swap 2 3 ∈ Q) : alternatingGroup (Fin 6) ≤ Q := by
  have h01_45 : swap (0 : Fin 6) 1 * swap 4 5 ∈ Q :=
    swap_mul_swap_mem_of_commute hQ hu (by decide) (by decide) (by decide)
  have h02_13 : swap (0 : Fin 6) 2 * swap 1 3 ∈ Q :=
    swap_mul_swap_mem_of_commute hQ hu (by decide) (by decide) (by decide)
  have h03_12 : swap (0 : Fin 6) 3 * swap 1 2 ∈ Q :=
    swap_mul_swap_mem_of_commute hQ hu (by decide) (by decide) (by decide)
  have h02_45 : swap (0 : Fin 6) 2 * swap 4 5 ∈ Q :=
    swap_mul_swap_mem_of_commute hQ h02_13 (by decide) (by decide) (by decide)
  have h03_45 : swap (0 : Fin 6) 3 * swap 4 5 ∈ Q :=
    swap_mul_swap_mem_of_commute hQ h03_12 (by decide) (by decide) (by decide)
  have h04_15 : swap (0 : Fin 6) 4 * swap 1 5 ∈ Q :=
    swap_mul_swap_mem_of_commute hQ h01_45 (by decide) (by decide) (by decide)
  have h05_14 : swap (0 : Fin 6) 5 * swap 1 4 ∈ Q :=
    swap_mul_swap_mem_of_commute hQ h01_45 (by decide) (by decide) (by decide)
  have h04_23 : swap (0 : Fin 6) 4 * swap 2 3 ∈ Q :=
    swap_mul_swap_mem_of_commute hQ h04_15 (by decide) (by decide) (by decide)
  have h05_23 : swap (0 : Fin 6) 5 * swap 2 3 ∈ Q :=
    swap_mul_swap_mem_of_commute hQ h05_14 (by decide) (by decide) (by decide)
  rw [← CFSG.LocalAnalysis.ComponentInitial.closure_altThreeCyclePerm (n := 4), closure_le]
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact swap_mul_swap_mem_of_mul_swap h02_45 h01_45
  · exact swap_mul_swap_mem_of_mul_swap h03_45 h01_45
  · exact swap_mul_swap_mem_of_mul_swap h04_23 hu
  · exact swap_mul_swap_mem_of_mul_swap h05_23 hu

end Six

theorem not_isPIsolatedOver_alternatingGroup_six :
    ¬ IsPIsolatedOver 2 (⊤ : Subgroup (alternatingGroup (Fin 6))) ⊥ := by
  intro h
  obtain ⟨M, hM⟩ := isPIsolatedOver_top_bot_iff.mp h
  have hu := swap_mul_swap_mem_ne_sq (a := (0 : Fin 6)) (b := 1) (c := 2) (d := 3) (by decide)
  obtain ⟨Q, hQu, hQ, hnot⟩ := exists_centClosed_of_isStronglyPEmbedded hM hu.1 hu.2.2
  exact hnot (alternatingGroup_six_le hQ hQu)

theorem card_eq_five_of_isPIsolatedOver_alternatingGroup {β : Type} [Fintype β] [DecidableEq β]
    (h : IsPIsolatedOver 2 (alternatingGroup β) (⊥ : Subgroup (Equiv.Perm β))) :
    Fintype.card β = 5 := by
  by_contra hne
  rcases Nat.lt_or_ge (Fintype.card β) 4 with h3 | h4
  · exact not_isPIsolatedOver_of_odd (odd_card_alternatingGroup_of_card_le_three (by omega)) _ h
  have hTop := isPIsolatedOver_top_of_alternatingGroup h
  rcases h4.eq_or_lt with h4 | h5
  · exact not_isPIsolatedOver_alternatingGroup_four h4.symm hTop
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card β = m := ⟨_, rfl⟩
  have hFin : IsPIsolatedOver 2 (⊤ : Subgroup (alternatingGroup (Fin m))) ⊥ := by
    subst hm
    set e := (Fintype.equivFin β).altCongrHom
    have hker : e.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr e.injective
    have key := isPIsolatedOver_map_iff (p := 2) (f := e.toMonoidHom) e.surjective
      (by rw [hker]; exact IsPGroup.of_bot) (H := ⊥) (K := ⊤) (by rw [hker])
      (by rw [hker]; exact bot_le)
    rw [map_top_of_surjective _ e.surjective, Subgroup.map_bot] at key
    exact key.mpr hTop
  rcases (show m = 6 ∨ 7 ≤ m by omega) with rfl | h7
  · exact not_isPIsolatedOver_alternatingGroup_six hFin
  · exact CFSG.GroupTheory.not_isPIsolatedOver_alternatingGroup h7 hFin

end CFSG.GroupTheory.AltCore
