module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.C3.Layer1.Th2Struct
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GH74.GLS.Th2.Obs

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

@[expose] def cosetSub (O : Subgroup G) {x : G} (hx2 : x * x = 1)
    (hn : ∀ o ∈ O, x * o * x⁻¹ ∈ O) : Subgroup G where
  carrier := {g | ∃ o ∈ O, g = o ∨ g = o * x}
  one_mem' := ⟨1, O.one_mem, Or.inl rfl⟩
  mul_mem' := by
    have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
    rintro a b ⟨o₁, ho₁, h₁⟩ ⟨o₂, ho₂, h₂⟩
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    · exact ⟨o₁ * o₂, O.mul_mem ho₁ ho₂, Or.inl (by rw [h₁, h₂])⟩
    · exact ⟨o₁ * o₂, O.mul_mem ho₁ ho₂, Or.inr (by rw [h₁, h₂]; group)⟩
    · refine ⟨o₁ * (x * o₂ * x⁻¹), O.mul_mem ho₁ (hn o₂ ho₂), Or.inr ?_⟩
      rw [h₁, h₂]; group
    · refine ⟨o₁ * (x * o₂ * x⁻¹), O.mul_mem ho₁ (hn o₂ ho₂), Or.inl ?_⟩
      rw [h₁, h₂]
      calc o₁ * x * (o₂ * x) = o₁ * (x * o₂ * x⁻¹) * (x * x) := by group
        _ = o₁ * (x * o₂ * x⁻¹) := by rw [hx2, mul_one]
  inv_mem' := by
    have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
    rintro a ⟨o, ho, h⟩
    rcases h with h | h
    · exact ⟨o⁻¹, O.inv_mem ho, Or.inl (by rw [h])⟩
    · refine ⟨x * o⁻¹ * x⁻¹, hn _ (O.inv_mem ho), Or.inr ?_⟩
      calc a⁻¹ = (o * x)⁻¹ := by rw [h]
        _ = x⁻¹ * o⁻¹ := mul_inv_rev _ _
        _ = x * o⁻¹ := by rw [hxi]
        _ = x * o⁻¹ * x⁻¹ * x := by group

omit [Finite G] in
theorem le_cosetSub (O : Subgroup G) {x : G} (hx2 : x * x = 1) (hn : ∀ o ∈ O, x * o * x⁻¹ ∈ O) :
    O ≤ cosetSub O hx2 hn := fun o ho => ⟨o, ho, Or.inl rfl⟩

omit [Finite G] in
theorem x_mem_cosetSub (O : Subgroup G) {x : G} (hx2 : x * x = 1) (hn : ∀ o ∈ O, x * o * x⁻¹ ∈ O) :
    x ∈ cosetSub O hx2 hn := ⟨1, O.one_mem, Or.inr (by simp)⟩

theorem card_cosetSub (O : Subgroup G) {x : G} (hx2 : x * x = 1) (hn : ∀ o ∈ O, x * o * x⁻¹ ∈ O)
    (hx1 : x ≠ 1) (hO : Odd (Nat.card O)) : Nat.card (cosetSub O hx2 hn) = 2 * Nat.card O := by
  have hx2' : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact hx2) hx1
  have hle : Nat.card (cosetSub O hx2 hn) ≤ 2 * Nat.card O := by
    let f : O × Bool → cosetSub O hx2 hn := fun p =>
      if p.2 then ⟨p.1 * x, p.1.1, p.1.2, Or.inr rfl⟩ else ⟨p.1, p.1.1, p.1.2, Or.inl rfl⟩
    have hf : Function.Surjective f := by
      rintro ⟨g, o, ho, h | h⟩
      · exact ⟨(⟨o, ho⟩, false), by simp [f, h]⟩
      · exact ⟨(⟨o, ho⟩, true), by simp [f, h]⟩
    have := Nat.card_le_card_of_surjective f hf
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this
    omega
  have hd2 : 2 ∣ Nat.card (cosetSub O hx2 hn) := by
    have h1 : Nat.card (zpowers x) ∣ Nat.card (cosetSub O hx2 hn) :=
      Subgroup.card_dvd_of_le (zpowers_le.2 (x_mem_cosetSub O hx2 hn))
    rwa [Nat.card_zpowers, hx2'] at h1
  have hdO : Nat.card O ∣ Nat.card (cosetSub O hx2 hn) := Subgroup.card_dvd_of_le (le_cosetSub O hx2 hn)
  have hcop : Nat.Coprime 2 (Nat.card O) := (Nat.coprime_two_left.2 hO)
  have hdiv := hcop.mul_dvd_of_dvd_of_dvd hd2 hdO
  have hpos : 0 < Nat.card (cosetSub O hx2 hn) := Nat.card_pos
  exact le_antisymm hle (Nat.le_of_dvd hpos hdiv)

theorem exists_conj_of_inv_mul_mem {O : Subgroup G} (hO : Odd (Nat.card O)) {x x' : G}
    (hx2 : x * x = 1) (hx1 : x ≠ 1) (hx'2 : x' * x' = 1) (hx'1 : x' ≠ 1)
    (hn : ∀ o ∈ O, x * o * x⁻¹ ∈ O) (h : x⁻¹ * x' ∈ O) : ∃ o ∈ O, x' = o * x * o⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact hx2) hx1
  have hx'o : orderOf x' = 2 := orderOf_eq_prime (by rw [sq]; exact hx'2) hx'1
  set H := cosetSub O hx2 hn with hHdef
  have hxH : x ∈ H := x_mem_cosetSub O hx2 hn
  have hx'H : x' ∈ H := by
    have : x' = x * (x⁻¹ * x') := by group
    rw [this]
    exact H.mul_mem hxH (le_cosetSub O hx2 hn h)
  have hcardH : Nat.card H = 2 * Nat.card O := card_cosetSub O hx2 hn hx1 hO
  have hv : (Nat.card H).factorization 2 = 1 := by
    rw [hcardH, Nat.factorization_mul (by norm_num) (Nat.card_pos).ne']
    have : (Nat.card O).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by simpa [even_iff_two_dvd] using Nat.not_even_iff_odd.2 hO)
    simp [this, Nat.Prime.factorization_self Nat.prime_two]
  have hS : IsSylowOf 2 (zpowers x) H :=
    isSylowOf_of_card (zpowers_le.2 hxH) (by rw [Nat.card_zpowers, hxo, hv]; simp)
  have hS' : IsSylowOf 2 (zpowers x') H :=
    isSylowOf_of_card (zpowers_le.2 hx'H) (by rw [Nat.card_zpowers, hx'o, hv]; simp)
  obtain ⟨k, hkH, hconj⟩ := hS.exists_mem_conj hS'
  have h1 : k⁻¹ * x' * k ∈ zpowers x := (hconj x').1 (mem_zpowers x')
  have h2 : k⁻¹ * x' * k = x := by
    rcases mem_zpowers_two hxo h1 with h0 | h0
    · exfalso
      apply hx'1
      have : x' = k * 1 * k⁻¹ := by rw [← h0]; group
      rw [this]; group
    · exact h0
  have h3 : x' = k * x * k⁻¹ := by rw [← h2]; group
  obtain ⟨o, ho, hk | hk⟩ := hkH
  · exact ⟨o, ho, by rw [h3, hk]⟩
  · refine ⟨o, ho, ?_⟩
    rw [h3, hk]
    calc o * x * x * (o * x)⁻¹ = o * (x * x) * x⁻¹ * o⁻¹ := by group
      _ = o * x * o⁻¹ := by rw [hx2, inv_eq_of_mul_eq_one_right hx2]; group

theorem exists_centralizer_lift {J : Subgroup G} {x : G} (hxJ : x ∈ normalizer (J : Set G))
    (hx2 : x * x = 1) (hx1 : x ≠ 1) {j : G} (hj : j ∈ J)
    (h : x⁻¹ * (j * x * j⁻¹) ∈ pPrimeCoreOf 2 J) :
    ∃ y ∈ J, x * y = y * x ∧ j * y⁻¹ ∈ pPrimeCoreOf 2 J := by
  have hxN := TwoThin.mem_normalizer_pPrimeCoreOf hxJ
  have hn : ∀ o ∈ pPrimeCoreOf 2 J, x * o * x⁻¹ ∈ pPrimeCoreOf 2 J := fun o ho =>
    (Subgroup.mem_normalizer_iff.1 hxN o).1 ho
  have hx'2 : (j * x * j⁻¹) * (j * x * j⁻¹) = 1 := by
    calc (j * x * j⁻¹) * (j * x * j⁻¹) = j * (x * x) * j⁻¹ := by group
      _ = 1 := by rw [hx2]; group
  have hx'1 : j * x * j⁻¹ ≠ 1 := by
    intro h1
    apply hx1
    calc x = j⁻¹ * (j * x * j⁻¹) * j := by group
      _ = 1 := by rw [h1]; group
  obtain ⟨o, ho, hoeq⟩ := exists_conj_of_inv_mul_mem (TwoThin.card_pPrimeCoreOf_odd J) hx2 hx1 hx'2
    hx'1 hn h
  have hoJ : o ∈ J := TwoThin.pPrimeCoreOf_le J ho
  refine ⟨o⁻¹ * j, J.mul_mem (J.inv_mem hoJ) hj, ?_, ?_⟩
  · calc x * (o⁻¹ * j) = o⁻¹ * (o * x * o⁻¹) * j := by group
      _ = o⁻¹ * (j * x * j⁻¹) * j := by rw [← hoeq]
      _ = o⁻¹ * j * x := by group
  · have : j * (o⁻¹ * j)⁻¹ = o := by group
    rw [this]; exact ho

end CFSG.GH74.GLS.Th2.Obs
