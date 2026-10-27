module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.Basic
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Basic

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.B

open Subgroup

variable {G : Type*} [Group G]

theorem relIndex_le_two_of_cover {H S : Subgroup G} {y : G} (hy : y ∈ S)
    (hcov : ∀ x ∈ S, x ∈ H ∨ x * y⁻¹ ∈ H) : H.relIndex S ≤ 2 := by
  by_cases hyH : y ∈ H
  · have hSH : S ≤ H := fun x hx => (hcov x hx).elim id (fun h => by
      have := H.mul_mem h hyH
      simpa using this)
    rw [Subgroup.relIndex_eq_one.2 hSH]
    norm_num
  · have h2 : (H.subgroupOf S).index = 2 := by
      rw [Subgroup.index_eq_two_iff]
      refine ⟨⟨y⁻¹, S.inv_mem hy⟩, fun b => ?_⟩
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
      rcases hcov b b.2 with h1 | h1
      · right
        refine ⟨h1, fun h3 => hyH ?_⟩
        have := H.mul_mem (H.inv_mem h1) h3
        simpa using H.inv_mem this
      · left
        refine ⟨h1, fun h3 => hyH ?_⟩
        have := H.mul_mem (H.inv_mem h3) h1
        simpa using this
    rw [Subgroup.relIndex, h2]

theorem sq_mem_of_relIndex_le_two [Finite G] {P X : Subgroup G} (hidx : P.relIndex X ≤ 2) {x : G}
    (hx : x ∈ X) : x * x ∈ P := by
  by_cases hxP : x ∈ P
  · exact P.mul_mem hxP hxP
  · rcases mem_or_mul_inv_mem hidx hx hxP (X.mul_mem hx hx) with h | h
    · exact h
    · exact absurd (by simpa using h) hxP

theorem relIndex_sup_le_two [Finite G] {A B C : Subgroup G} (hidx : B.relIndex C ≤ 2)
    (hcomm : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a) : (A ⊔ B).relIndex (A ⊔ C) ≤ 2 := by
  by_cases hCB : C ≤ B
  · have : A ⊔ C ≤ A ⊔ B := sup_le_sup_left hCB A
    rw [Subgroup.relIndex_eq_one.2 this]
    norm_num
  · obtain ⟨y, hyC, hyB⟩ : ∃ y ∈ C, y ∉ B := by
      by_contra hcon
      push Not at hcon
      exact hCB hcon
    refine relIndex_le_two_of_cover (y := y) (mem_sup_right hyC) (fun x hx => ?_)
    obtain ⟨a, ha, c, hc, rfl⟩ := Sec4.M.mem_sup_of_commute hcomm hx
    rcases mem_or_mul_inv_mem hidx hyC hyB hc with h | h
    · exact Or.inl (mul_mem (mem_sup_left ha) (mem_sup_right h))
    · refine Or.inr ?_
      have e : a * c * y⁻¹ = a * (c * y⁻¹) := by group
      rw [e]
      exact mul_mem (mem_sup_left ha) (mem_sup_right h)

theorem eq_of_le_of_relIndex_eq [Finite G] {X Y S : Subgroup G} (hXY : X ≤ Y) (hYS : Y ≤ S)
    (h : X.relIndex S = Y.relIndex S) : X = Y := by
  have h1 := Subgroup.relIndex_mul_relIndex X Y S hXY hYS
  have h0 : Y.relIndex S ≠ 0 := relIndex_ne_zero'
  have h2 : X.relIndex Y = 1 := by
    rw [h] at h1
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero h0) (by simpa using h1)
  exact le_antisymm hXY (Subgroup.relIndex_eq_one.1 h2)

theorem klein_of_two_index_two [Finite G] {P X₁ X₂ S₁ : Subgroup G} (h1 : P ≤ X₁) (h2 : P ≤ X₂)
    (h1' : X₁ ≤ S₁) (h2' : X₂ ≤ S₁) (i1 : P.relIndex X₁ = 2) (i1' : X₁.relIndex S₁ = 2)
    (i2 : P.relIndex X₂ = 2) (i2' : X₂.relIndex S₁ = 2) (hne : X₁ ≠ X₂) :
    S₁ = X₁ ⊔ X₂ ∧ ∃ _ : (P.subgroupOf S₁).Normal,
      Nonempty ((↥S₁ ⧸ P.subgroupOf S₁) ≃* Multiplicative (ZMod 2 × ZMod 2)) := by
  have hD : X₁ ⊓ X₂ = P := by
    have hPD : P ≤ X₁ ⊓ X₂ := le_inf h1 h2
    have hm := Subgroup.relIndex_mul_relIndex P (X₁ ⊓ X₂) X₁ hPD inf_le_left
    rw [i1] at hm
    have hdvd : P.relIndex (X₁ ⊓ X₂) ∣ 2 := ⟨_, hm.symm⟩
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact le_antisymm (Subgroup.relIndex_eq_one.1 h) hPD
    · exfalso
      rw [h] at hm
      have h3 : (X₁ ⊓ X₂).relIndex X₁ = 1 := by omega
      have hX12 : X₁ ≤ X₂ := (Subgroup.relIndex_eq_one.1 h3).trans inf_le_right
      exact hne (eq_of_le_of_relIndex_eq hX12 h2' (by rw [i1', i2']))
  have hS : S₁ = X₁ ⊔ X₂ := by
    have hle : X₁ ⊔ X₂ ≤ S₁ := sup_le h1' h2'
    have hm := Subgroup.relIndex_mul_relIndex X₁ (X₁ ⊔ X₂) S₁ le_sup_left hle
    rw [i1'] at hm
    have hdvd : (X₁ ⊔ X₂).relIndex S₁ ∣ 2 := ⟨X₁.relIndex (X₁ ⊔ X₂), by rw [mul_comm]; exact hm.symm⟩
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact (le_antisymm hle (Subgroup.relIndex_eq_one.1 h)).symm
    · exfalso
      rw [h] at hm
      have h3 : X₁.relIndex (X₁ ⊔ X₂) = 1 := by omega
      have hX21 : X₂ ≤ X₁ := le_sup_right.trans (Subgroup.relIndex_eq_one.1 h3)
      exact hne (eq_of_le_of_relIndex_eq hX21 h1' (by rw [i1', i2'])).symm
  refine ⟨hS, ?_⟩
  have hnormX : ∀ X : Subgroup G, P ≤ X → P.relIndex X = 2 → ∀ g ∈ X, ∀ p ∈ P, g * p * g⁻¹ ∈ P := by
    intro X hPX hi g hg p hp
    have hn : (P.subgroupOf X).Normal := Subgroup.normal_of_index_eq_two hi
    have := hn.conj_mem ⟨p, hPX hp⟩ (by simpa [Subgroup.mem_subgroupOf] using hp) ⟨g, hg⟩
    simpa [Subgroup.mem_subgroupOf] using this
  have hXN : ∀ X : Subgroup G, P ≤ X → P.relIndex X = 2 → X ≤ normalizer (P : Set G) := by
    intro X hPX hi g hg
    exact Sec4.M.mem_normalizer_of_both (fun x hx => hnormX X hPX hi g hg x hx)
      (fun x hx => by simpa using hnormX X hPX hi g⁻¹ (X.inv_mem hg) x hx)
  have hSN : S₁ ≤ normalizer (P : Set G) := by
    rw [hS]
    exact sup_le (hXN X₁ h1 i1) (hXN X₂ h2 i2)
  have hnorm : (P.subgroupOf S₁).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := Subgroup.mem_normalizer_iff.1 (hSN g.2) n
    simpa using this.1 hn
  refine ⟨hnorm, ?_⟩
  have : (P.subgroupOf S₁).Normal := hnorm
  have h4 : P.relIndex S₁ = 4 := by
    rw [← Subgroup.relIndex_mul_relIndex P X₁ S₁ h1 h1', i1, i1']
  have hcard : Nat.card (↥S₁ ⧸ P.subgroupOf S₁) = 4 := h4
  have hcomm : IsMulCommutative (↥S₁ ⧸ P.subgroupOf S₁) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by rw [hcard]; norm_num)
  obtain ⟨a, haX, haP⟩ : ∃ a ∈ X₁, a ∉ P := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.relIndex_eq_one.2 hcon
    omega
  obtain ⟨b, hbX, hbP⟩ : ∃ b ∈ X₂, b ∉ P := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.relIndex_eq_one.2 hcon
    omega
  have hbX1 : b ∉ X₁ := fun hb => hbP (hD ▸ ⟨hb, hbX⟩)
  have hcX1 : ∀ x ∈ X₁, x ∈ P ∨ x * a⁻¹ ∈ P := fun x hx =>
    mem_or_mul_inv_mem (le_of_eq i1) haX haP hx
  have hcS : ∀ x ∈ S₁, x ∈ X₁ ∨ x * b⁻¹ ∈ X₁ := fun x hx =>
    mem_or_mul_inv_mem (le_of_eq i1') (h2' hbX) hbX1 hx
  let a' : ↥S₁ := ⟨a, h1' haX⟩
  let b' : ↥S₁ := ⟨b, h2' hbX⟩
  obtain ⟨mk, hmk⟩ : ∃ mk : ↥S₁ →* ↥S₁ ⧸ P.subgroupOf S₁,
      ∀ u, mk u = (u : ↥S₁ ⧸ P.subgroupOf S₁) := ⟨QuotientGroup.mk' _, fun u => rfl⟩
  have hmk_one : ∀ u : ↥S₁, mk u = 1 ↔ (u : G) ∈ P := by
    intro u
    rw [hmk, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hmk_eq : ∀ u v : ↥S₁, mk u = mk v ↔ (u : G) * (v : G)⁻¹ ∈ P := by
    intro u v
    rw [hmk, hmk, QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]
    simp [div_eq_mul_inv]
  have hmk_surj : ∀ g : ↥S₁ ⧸ P.subgroupOf S₁, ∃ u, mk u = g := by
    intro g
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective g
    exact ⟨u, hmk u⟩
  have hsa : mk a' * mk a' = 1 := by
    rw [← map_mul, hmk_one]
    exact sq_mem_of_relIndex_le_two (le_of_eq i1) haX
  have hsb : mk b' * mk b' = 1 := by
    rw [← map_mul, hmk_one]
    exact sq_mem_of_relIndex_le_two (le_of_eq i2) hbX
  have hX1mk : ∀ x : ↥S₁, (x : G) ∈ X₁ → mk x = 1 ∨ mk x = mk a' := by
    intro x hx
    rcases hcX1 x hx with h | h
    · exact Or.inl ((hmk_one x).2 h)
    · exact Or.inr ((hmk_eq x a').2 h)
  have hsq : ∀ g : ↥S₁ ⧸ P.subgroupOf S₁, g * g = 1 := by
    intro g
    obtain ⟨x, rfl⟩ := hmk_surj g
    rcases hcS x x.2 with hx | hx
    · rcases hX1mk x hx with h | h
      · rw [h, one_mul]
      · rw [h]; exact hsa
    · let w : ↥S₁ := ⟨x * b⁻¹, h1' hx⟩
      have hw : x = w * b' := by
        apply Subtype.ext
        simp [w, b']
      rw [hw, map_mul]
      rcases hX1mk w hx with h | h
      · rw [h, one_mul]; exact hsb
      · rw [h]
        have hc := hcomm.is_comm.comm (mk b') (mk a')
        calc (mk a' * mk b') * (mk a' * mk b') = mk a' * (mk b' * mk a') * mk b' := by
              simp only [mul_assoc]
          _ = mk a' * (mk a' * mk b') * mk b' := by rw [hc]
          _ = (mk a' * mk a') * (mk b' * mk b') := by simp only [mul_assoc]
          _ = 1 := by rw [hsa, hsb, one_mul]
  have hnt : Nontrivial (↥S₁ ⧸ P.subgroupOf S₁) :=
    Finite.one_lt_card_iff_nontrivial.1 (by omega)
  have : IsKleinFour (↥S₁ ⧸ P.subgroupOf S₁) := by
    refine ⟨hcard, ?_⟩
    rw [Monoid.exponent_eq_prime_iff Nat.prime_two]
    intro g hg
    exact orderOf_eq_prime (by simpa [sq] using hsq g) hg
  exact IsKleinFour.nonempty_mulEquiv

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.B
