module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.ComponentClassification.GS82PumpInputs.P10

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

theorem mem_normalizer_of_conj_mem {g : G} {S : Subgroup G}
    (h1 : ∀ x ∈ S, g * x * g⁻¹ ∈ S) (h2 : ∀ x ∈ S, g⁻¹ * x * g ∈ S) :
    g ∈ normalizer (S : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  refine ⟨h1 x, fun hx => ?_⟩
  have := h2 _ hx
  rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at this

theorem commutator_le_left_of_le_normalizer {A B : Subgroup G}
    (hAN : B ≤ normalizer (A : Set G)) : ⁅A, B⁆ ≤ A := by
  rw [commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  have h1 : b * a⁻¹ * b⁻¹ ∈ A := (mem_normalizer_iff.mp (hAN hb) _).mp (inv_mem ha)
  have h2 : a * (b * a⁻¹ * b⁻¹) ∈ A := mul_mem ha h1
  rwa [← mul_assoc, ← mul_assoc] at h2

theorem commutator_ne_of_isNilpotent {A B : Subgroup G} (hB : Group.IsNilpotent ↥B)
    (hAB : A ≤ B) (hA : A ≠ ⊥) : ⁅A, B⁆ ≠ A := by
  intro h
  obtain ⟨n, hn⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries B).mp hB
  have key : ∀ k, A ≤ B.lowerCentralSeries k := by
    intro k
    induction k with
    | zero => exact hAB
    | succ k ih =>
      rw [Subgroup.lowerCentralSeries_succ, ← h]
      exact commutator_mono ih le_rfl
  exact hA (eq_bot_iff.mpr (hn ▸ key n))

variable [Finite G]

theorem exists_index_two_normalized {A B : Subgroup G} (hB : IsPGroup 2 B) (hAB : A ≤ B)
    (hAN : B ≤ normalizer (A : Set G)) (hA : A ≠ ⊥) :
    ∃ A₁ : Subgroup ↥A, A₁.index = 2 ∧
      B ≤ normalizer ((A₁.map A.subtype : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup G := ⁅A, B⁆ with hNdef
  have hNA : N ≤ A := commutator_le_left_of_le_normalizer hAN
  have hNne : N ≠ A := commutator_ne_of_isNilpotent hB.isNilpotent hAB hA
  have hNnorm : A ≤ normalizer (N : Set G) := by
    intro a ha
    have hcj : ∀ g ∈ B, N.map (MulAut.conj g).toMonoidHom ≤ N := by
      intro g hg
      rw [hNdef, Subgroup.map_commutator]
      refine commutator_mono ?_ ?_
      · rintro _ ⟨x, hx, rfl⟩
        exact (mem_normalizer_iff.mp (hAN hg) x).mp hx
      · rintro _ ⟨x, hx, rfl⟩
        exact mul_mem (mul_mem hg hx) (inv_mem hg)
    refine mem_normalizer_of_conj_mem (fun x hx => hcj a (hAB ha) ⟨x, hx, rfl⟩) fun x hx => ?_
    have h1 := hcj a⁻¹ (inv_mem (hAB ha)) ⟨x, hx, rfl⟩
    simpa using h1
  set NA := N.subgroupOf A with hNAdef
  have : NA.Normal := normal_subgroupOf_of_le_normalizer hNnorm
  have hQ2 : IsPGroup 2 (↥A ⧸ NA) := (hB.to_le hAB).to_quotient NA
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ2
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hNne
    have h1 : Nat.card (↥A ⧸ NA) = 1 := by rw [hk, pow_zero]
    have h2 : NA = ⊤ := by
      rw [← Subgroup.index_eq_one, Subgroup.index, h1]
    apply le_antisymm hNA
    intro x hx
    have : (⟨x, hx⟩ : ↥A) ∈ NA := h2 ▸ mem_top _
    exact mem_subgroupOf.mp this
  obtain ⟨Q₁, hQ₁⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥A ⧸ NA) 2 (n := k - 1)
    (by rw [hk]; exact pow_dvd_pow 2 (Nat.sub_le k 1))
  have hQ₁idx : Q₁.index = 2 := by
    have h := Q₁.card_mul_index
    rw [hQ₁, hk] at h
    have : 2 ^ k = 2 ^ (k - 1) * 2 := by rw [← pow_succ]; congr 1; omega
    rw [this] at h
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h
  set A₁ := Q₁.comap (QuotientGroup.mk' NA) with hA₁def
  have hA₁idx : A₁.index = 2 := by
    rw [hA₁def, Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective NA)]
    exact hQ₁idx
  have hNA₁ : NA ≤ A₁ := by
    intro x hx
    have h1 : QuotientGroup.mk' NA x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    change QuotientGroup.mk' NA x ∈ Q₁
    rw [h1]
    exact one_mem _
  refine ⟨A₁, hA₁idx, fun g hg => ?_⟩
  have key : ∀ g ∈ B, ∀ x ∈ A₁.map A.subtype, g * x * g⁻¹ ∈ A₁.map A.subtype := by
    intro g hg x hx
    obtain ⟨a, ha, rfl⟩ := hx
    have hc : ⁅(a : G), g⁆ ∈ N := commutator_mem_commutator a.2 hg
    have hcA : ⁅(a : G), g⁆ ∈ A := hNA hc
    have hcA₁ : (⟨_, hcA⟩ : ↥A) ∈ A₁ := hNA₁ (mem_subgroupOf.mpr hc)
    have h1 : g * (a : G) * g⁻¹ = (⟨_, hcA⟩ : ↥A)⁻¹ * a := by
      simp only [commutatorElement_def, coe_inv]
      group
    change g * (a : G) * g⁻¹ ∈ _
    rw [h1]
    exact ⟨_, mul_mem (inv_mem hcA₁) ha, rfl⟩
  exact mem_normalizer_of_conj_mem (key g hg) (by
    intro x hx
    have := key g⁻¹ (inv_mem hg) x hx
    rwa [inv_inv] at this)

end CFSG.ComponentClassification.GS82PumpInputs.P10
