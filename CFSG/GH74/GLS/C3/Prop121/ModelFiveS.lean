module

public import CFSG.GH74.GLS.C3.Prop121.ModelFive
public import CFSG.GH74.GLS.C3.Layer2.FinModelFactsGeneric
public import Mathlib.GroupTheory.Sylow
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public import CFSG.GH74.GLS.C3.Prop121.ModelFiveSInputs
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFiveSInputs
public import Certificates.Certificate5092

public section

namespace CFSG.GH74.GLS.C3.Prop121

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model
  CFSG.GH74.GLS.C3.Layer2.Model.Facts

@[expose] def R5 : Subgroup (Perm (Fin 9)) := T5.map (emb 5)

theorem mem_R5 {p : Perm (Fin 9)} : p ∈ R5 ↔ ∃ t ∈ T5, emb 5 t = p := by
  simp only [R5, Subgroup.mem_map]

@[expose] def S0 : Subgroup (Perm (Fin 9)) := R5 ⊔ Subgroup.zpowers (a0perm 5)

theorem a0_sq : a0perm 5 * a0perm 5 = 1 :=
  Certificates.certificate5092.1

theorem a0_inv :
    (a0perm 5)⁻¹ = a0perm 5 := inv_eq_of_mul_eq_one_right a0_sq

theorem sign_a0 : sign (a0perm 5) = 1 :=
  Certificates.certificate5092.2.1

theorem a0_norm_T5 :
    ∀ t ∈ allT5, ∃ t' ∈ allT5, a0perm 5 * emb 5 t * (a0perm 5)⁻¹ = emb 5 t' :=
  Certificates.certificate5092.2.2.1

theorem a0_notin_T5 :
    ∀ t ∈ allT5, emb 5 t ≠ a0perm 5 :=
  Certificates.certificate5092.2.2.2.1

theorem a0_f1 :
    a0perm 5 * emb 5 f1 * (a0perm 5)⁻¹ = emb 5 e1 :=
  Certificates.certificate5092.2.2.2.2.1

theorem a0_e1 : a0perm 5 * emb 5 e1 * (a0perm 5)⁻¹ = emb 5 f1 := by
  rw [← a0_f1, a0_inv, mul_assoc, mul_assoc, a0_sq, mul_one, ← mul_assoc, a0_sq, one_mul]

theorem a0_norm_R5 : ∀ r ∈ R5, a0perm 5 * r * (a0perm 5)⁻¹ ∈ R5 := by
  intro r hr
  obtain ⟨t, ht, rfl⟩ := mem_R5.1 hr
  obtain ⟨t', ht', h⟩ := a0_norm_T5 t (mem_allT5.2 ht)
  exact mem_R5.2 ⟨t', mem_allT5.1 ht', h.symm⟩

theorem a0_notin_R5 : a0perm 5 ∉ R5 := by
  intro h
  obtain ⟨t, ht, h⟩ := mem_R5.1 h
  exact a0_notin_T5 t (mem_allT5.2 ht) h

theorem mem_S0
    {p : Perm (Fin 9)} : p ∈ S0 ↔ p ∈ R5 ∨ p * a0perm 5 ∈ R5 :=
  mem_sup_zpowers_iff_mul_self R5 (a0perm 5) a0_sq a0_norm_R5 p

theorem a0_mem_S0 : a0perm 5 ∈ S0 := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

theorem R5_le_S0 : R5 ≤ S0 := le_sup_left

theorem mem_S0l {p : Perm (Fin 9)} : p ∈ S0l ↔ p ∈ S0 := by
  rw [mem_S0, S0l, List.mem_flatMap]
  constructor
  · rintro ⟨t, ht, hp⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact Or.inl (mem_R5.2 ⟨t, mem_allT5.1 ht, rfl⟩)
    · right
      rw [mul_assoc, a0_sq, mul_one]
      exact mem_R5.2 ⟨t, mem_allT5.1 ht, rfl⟩
  · rintro (h | h)
    · obtain ⟨t, ht, rfl⟩ := mem_R5.1 h
      exact ⟨t, mem_allT5.2 ht, by simp⟩
    · obtain ⟨t, ht, e⟩ := mem_R5.1 h
      refine ⟨t, mem_allT5.2 ht, ?_⟩
      have : p = emb 5 t * a0perm 5 := by rw [e, mul_assoc, a0_sq, mul_one]
      simp [this]

theorem S0l_facts : S0l.length = 64 ∧ S0l.Nodup :=
  Certificates.certificate5092.2.2.2.2.2.1

theorem sign_S0 {p : Perm (Fin 9)} (hp : p ∈ S0) : sign p = 1 := by
  have hR : ∀ r ∈ R5, sign r = 1 := by
    intro r hr
    obtain ⟨t, ht, rfl⟩ := mem_R5.1 hr
    exact mem_alternatingGroup.1 (emb_mem_alternating 5 (T5_le_Fgrp ht))
  rcases mem_S0.1 hp with h | h
  · exact hR p h
  · have := hR _ h
    rw [map_mul, sign_a0] at this
    simpa using this

theorem S0_le_alt :
    S0 ≤ alternatingGroup (Fin 9) := fun _ hp => mem_alternatingGroup.2 (sign_S0 hp)

theorem card_S0 : Nat.card S0 = 64 := by
  have hnd : S0l.Nodup := S0l_facts.2
  have : Nat.card S0 = S0l.length := by
    classical
    exact natCard_eq_length S0 S0l hnd (fun p => mem_S0l.symm)
  rw [this, S0l_facts.1]

theorem class_check : classAll S0l = true :=
  Certificates.certificate5092.2.2.2.2.2.2.1

theorem classPair_sound {L : List (Perm (Fin 9))} {y y' : Perm (Fin 9)}
    (h : classPair L y y' = true) (hne : y ≠ y') (hsq : y * y = 1) (hnm : numMoved y = 4)
    (hcl : ∀ s ∈ L, (s * y * s⁻¹ = y ∨ s * y * s⁻¹ = y') ∧
      (s * y' * s⁻¹ = y ∨ s * y' * s⁻¹ = y')) :
    y = emb 5 f1 ∨ y = emb 5 e1 := by
  by_contra hcon
  push Not at hcon
  have hP : (decide (y ≠ y') && decide (y * y = 1) && decide (numMoved y = 4) &&
      L.all fun s => (decide (s * y * s⁻¹ = y) || decide (s * y * s⁻¹ = y')) &&
        (decide (s * y' * s⁻¹ = y) || decide (s * y' * s⁻¹ = y'))) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true]
    exact ⟨⟨⟨hne, hsq⟩, hnm⟩, fun s hs => hcl s hs⟩
  unfold classPair at h
  rw [hP] at h
  simp [hcon.1, hcon.2] at h

theorem class_two
    {y y' : Perm (Fin 9)} (hy : y ∈ S0) (hy' : y' ∈ S0) (hne : y ≠ y')
    (hsq : y * y = 1) (hnm : numMoved y = 4)
    (hcl : ∀ s ∈ S0, (s * y * s⁻¹ = y ∨ s * y * s⁻¹ = y') ∧
      (s * y' * s⁻¹ = y ∨ s * y' * s⁻¹ = y')) :
    y = emb 5 f1 ∨ y = emb 5 e1 := by
  have h := class_check
  simp only [classAll, List.all_eq_true] at h
  exact classPair_sound (h y (mem_S0l.2 hy) y' (mem_S0l.2 hy')) hne hsq hnm
    (fun s hs => hcl s (mem_S0l.1 hs))

theorem cent_check : centAll S0l allT5 = true :=
  Certificates.certificate5092.2.2.2.2.2.2.2

theorem cent_S0 {p : Perm (Fin 9)} (hp : p ∈ S0) :
    p * emb 5 f1 = emb 5 f1 * p ↔ p ∈ R5 := by
  constructor
  · intro h
    have hc := cent_check
    simp only [centAll, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
      List.any_eq_true, decide_eq_true_eq] at hc
    rcases hc p (mem_S0l.2 hp) with hc | ⟨t, ht, e⟩
    · exact absurd h hc
    · exact mem_R5.2 ⟨t, mem_allT5.1 ht, e⟩
  · intro h
    obtain ⟨t, ht, rfl⟩ := mem_R5.1 h
    rw [← map_mul, ← map_mul]
    congr 1
    exact x0_central_aux 5 (T5_le_Fgrp ht)

@[expose] def S0A : Subgroup (alternatingGroup (Fin 9)) := S0.subgroupOf (alternatingGroup (Fin 9))

theorem mem_S0A {z : alternatingGroup (Fin 9)} : z ∈ S0A ↔ (z : Perm (Fin 9)) ∈ S0 := Iff.rfl

theorem card_S0A : Nat.card S0A = 64 := by
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe S0_le_alt).toEquiv).trans card_S0

theorem card_A9 : Nat.card (alternatingGroup (Fin 9)) = 181440 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card (α := Fin 9), Fintype.card_fin]
  decide

theorem isSylowOf_S0A : CFSG.ABGLocalTools.IsSylowOf 2 S0A ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.ABGLocalTools.isSylowOf_of_card le_top ?_
  rw [card_S0A, Subgroup.card_top, card_A9, Nat.factorization_def _ Nat.prime_two]
  decide +kernel

end CFSG.GH74.GLS.C3.Prop121
