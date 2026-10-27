module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1W16Components

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open Subgroup

variable {Y : Type*} [Group Y] [Finite Y]

theorem ncard_conj_le_relIndex (R N : Subgroup Y) {a : Y} (ha : a ∈ R) :
    {x : Y | ∃ n ∈ N, n * a * n⁻¹ = x}.ncard ≤ (centralizer (R : Set Y)).relIndex N := by
  let f : N ⧸ (centralizer (R : Set Y)).subgroupOf N → Y :=
    Quotient.lift (fun n : N => (n : Y) * a * (n : Y)⁻¹) (fun n m hnm => by
      have h : ((n⁻¹ * m : N) : Y) ∈ centralizer (R : Set Y) :=
        mem_subgroupOf.mp (QuotientGroup.leftRel_apply.mp hnm)
      have hc := mem_centralizer_iff.mp h a ha
      simp only [coe_mul, coe_inv] at hc
      calc (n : Y) * a * (n : Y)⁻¹ = (n : Y) * (a * ((n : Y)⁻¹ * m)) * (m : Y)⁻¹ := by group
        _ = (n : Y) * (((n : Y)⁻¹ * m) * a) * (m : Y)⁻¹ := by rw [hc]
        _ = (m : Y) * a * (m : Y)⁻¹ := by group)
  have hsub : {x : Y | ∃ n ∈ N, n * a * n⁻¹ = x} ⊆ Set.range f := by
    rintro x ⟨n, hn, rfl⟩
    exact ⟨(QuotientGroup.mk ⟨n, hn⟩ : N ⧸ (centralizer (R : Set Y)).subgroupOf N), rfl⟩
  calc {x : Y | ∃ n ∈ N, n * a * n⁻¹ = x}.ncard ≤ (Set.range f).ncard := Set.ncard_le_ncard hsub
    _ = Nat.card (Set.range f) := (Nat.card_coe_set_eq _).symm
    _ ≤ Nat.card (N ⧸ (centralizer (R : Set Y)).subgroupOf N) := Finite.card_range_le f
    _ = (centralizer (R : Set Y)).relIndex N := (index_eq_card _).symm

theorem exists_not_conj_of_card_eq_sixteen (R : Sylow 2 Y)
    (hexp : ∀ a ∈ (R : Subgroup Y), a * a = 1) (hcard : Nat.card (R : Subgroup Y) = 16)
    (horb : ∀ a ∈ (R : Subgroup Y),
      {x : Y | ∃ n ∈ normalizer ((R : Subgroup Y) : Set Y), n * a * n⁻¹ = x}.ncard ≤ 3) :
    ∃ a ∈ (R : Subgroup Y), ∃ b ∈ (R : Subgroup Y), orderOf a = 2 ∧ orderOf b = 2 ∧
      ∀ n ∈ normalizer ((R : Subgroup Y) : Set Y), n * a * n⁻¹ ≠ b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : ∀ x ∈ (R : Subgroup Y), x ≠ 1 → orderOf x = 2 := fun x hx hx1 =>
    orderOf_eq_prime (by rw [pow_two, hexp x hx]) hx1
  have hne : (R : Subgroup Y) ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hcard
    norm_num at hcard
  obtain ⟨⟨a, ha⟩, ha1⟩ := ne_bot_iff_exists_ne_one.mp hne
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  obtain ⟨b, hb, hb1, hbn⟩ : ∃ b ∈ (R : Subgroup Y), b ≠ 1 ∧
      ∀ n ∈ normalizer ((R : Subgroup Y) : Set Y), n * a * n⁻¹ ≠ b := by
    by_contra hcon
    push Not at hcon
    have hsub : ((R : Subgroup Y) : Set Y) ⊆
        insert 1 {x : Y | ∃ n ∈ normalizer ((R : Subgroup Y) : Set Y), n * a * n⁻¹ = x} := by
      intro x hx
      by_cases hx1 : x = 1
      · exact Or.inl hx1
      · exact Or.inr (hcon x hx hx1)
    have h16 : 16 ≤ 3 + 1 := by
      calc 16 = ((R : Subgroup Y) : Set Y).ncard := by rw [← Nat.card_coe_set_eq]; exact hcard.symm
        _ ≤ _ := Set.ncard_le_ncard hsub
        _ ≤ _ := Set.ncard_insert_le _ _
        _ ≤ 3 + 1 := Nat.add_le_add_right (horb a ha) 1
    omega
  exact ⟨a, ha, b, hb, hord a ha ha1', hord b hb hb1, hbn⟩

theorem normal_of_abelian_sylow_E16_of_relIndex
    (hO : oddCore Y = ⊥) (R : Sylow 2 Y)
    (hab : ∀ a ∈ (R : Subgroup Y), ∀ b ∈ (R : Subgroup Y), a * b = b * a)
    (hexp : ∀ a ∈ (R : Subgroup Y), a * a = 1) (hcard : Nat.card (R : Subgroup Y) = 16)
    (hidx : (centralizer ((R : Subgroup Y) : Set Y)).relIndex
      (normalizer ((R : Subgroup Y) : Set Y)) ≤ 3)
    (hfpf : ∀ n ∈ normalizer ((R : Subgroup Y) : Set Y),
      n ∉ centralizer ((R : Subgroup Y) : Set Y) →
      ∀ a ∈ (R : Subgroup Y), a ≠ 1 → n * a * n⁻¹ ≠ a) :
    (R : Subgroup Y).Normal := by
  obtain ⟨a, ha, b, hb, ha2, hb2, hnc⟩ := exists_not_conj_of_card_eq_sixteen R hexp hcard
    fun a ha => (ncard_conj_le_relIndex _ _ ha).trans hidx
  exact sylow_normal_of_fpf_of_not_conj_of_oddCore hO R
    ⟨⟨fun x y => Subtype.ext (hab x x.2 y y.2)⟩⟩
    (fun n hn hnC a ha h => by_contra fun ha1 => hfpf n hn hnC a ha ha1 h) ha hb ha2 hb2 hnc

theorem normal_of_abelian_sylow_E16_of_relIndex_of_pPrimeCore
    (hO : pPrimeCore 2 Y = ⊥)
    (R : Sylow 2 Y) (hab : ∀ a ∈ (R : Subgroup Y), ∀ b ∈ (R : Subgroup Y), a * b = b * a)
    (hexp : ∀ a ∈ (R : Subgroup Y), a * a = 1) (hcard : Nat.card (R : Subgroup Y) = 16)
    (hidx : (centralizer ((R : Subgroup Y) : Set Y)).relIndex
      (normalizer ((R : Subgroup Y) : Set Y)) ≤ 3)
    (hfpf : ∀ n ∈ normalizer ((R : Subgroup Y) : Set Y),
      n ∉ centralizer ((R : Subgroup Y) : Set Y) →
      ∀ a ∈ (R : Subgroup Y), a ≠ 1 → n * a * n⁻¹ ≠ a) :
    (R : Subgroup Y).Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact normal_of_abelian_sylow_E16_of_relIndex
    (((oddCore_eq_piCore Y).trans (pPrimeCore_eq_piCore Y 2).symm).trans hO) R hab hexp hcard
    hidx hfpf

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
