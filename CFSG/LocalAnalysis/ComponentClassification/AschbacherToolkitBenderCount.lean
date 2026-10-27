module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderBasic

public section

namespace CFSG.ComponentClassification.AschbacherToolkit

namespace Bender

open CFSG.Open
open scoped commutatorElement

variable {X : Type*} [Group X]

theorem commutator_le_of_card_lt [Finite X] {T A : Subgroup X} (hAT : A ≤ T)
    (hT : IsPGroup 2 T) (hcard : Nat.card T < 4 * Nat.card A) : ⁅T, T⁆ ≤ A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let A' : Subgroup T := A.subgroupOf T
  have hA'card : Nat.card A' = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAT).toEquiv
  have hidx := Subgroup.index_mul_card A'
  rw [hA'card] at hidx
  have hApos : 0 < Nat.card A := Nat.card_pos
  have hidx4 : A'.index < 4 := by
    by_contra h
    push Not at h
    have : 4 * Nat.card A ≤ A'.index * Nat.card A := Nat.mul_le_mul_right _ h
    omega
  have hidx2 : A'.index = 1 ∨ A'.index = 2 := by
    obtain ⟨k, hk⟩ := hT.index A'
    rw [hk] at hidx4 ⊢
    have hk2 : k < 2 := by
      by_contra h
      push Not at h
      have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h
      omega
    interval_cases k <;> simp
  rw [Subgroup.commutator_le]
  intro t ht t' ht'
  rcases hidx2 with h1 | h2
  · have htop : A' = ⊤ := Subgroup.index_eq_one.mp h1
    have htt : ⁅t, t'⁆ ∈ T := by
      rw [commutatorElement_def]
      exact T.mul_mem (T.mul_mem (T.mul_mem ht ht') (T.inv_mem ht)) (T.inv_mem ht')
    have hmem : (⟨⁅t, t'⁆, htt⟩ : T) ∈ A' := by
      rw [htop]
      exact Subgroup.mem_top _
    exact hmem
  · have hP : ∀ u v : T, u * v ∈ A' ↔ (u ∈ A' ↔ v ∈ A') := fun u v =>
      Subgroup.mul_mem_iff_of_index_two h2
    have hinv : ∀ u : T, u⁻¹ ∈ A' ↔ u ∈ A' := fun u => A'.inv_mem_iff
    let u : T := ⟨t, ht⟩
    let v : T := ⟨t', ht'⟩
    have hmem : u * v * u⁻¹ * v⁻¹ ∈ A' := by
      rw [hP, hP, hP, hinv, hinv]
      tauto
    exact hmem

theorem conj_mem_sylowCenter {T : Subgroup X} {n : X}
    (hn : n ∈ Subgroup.normalizer (T : Set X)) {z : X} (hz : z ∈ sylowCenter T) :
    n⁻¹ * z * n ∈ sylowCenter T := by
  obtain ⟨hzT, hzc⟩ := mem_sylowCenter.mp hz
  have hn' := Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn)
  refine mem_sylowCenter.mpr ⟨?_, fun t ht => ?_⟩
  · have := (hn' z).mp hzT
    simpa using this
  · have htn : n * t * n⁻¹ ∈ T := by
      have := (hn' t).mpr
      have h2 := (Subgroup.mem_normalizer_iff.mp hn t).mp ht
      exact h2
    have h1 := hzc _ htn
    calc t * (n⁻¹ * z * n) = n⁻¹ * ((n * t * n⁻¹) * z) * n := by group
      _ = n⁻¹ * (z * (n * t * n⁻¹)) * n := by rw [h1]
      _ = n⁻¹ * z * n * t := by group

theorem nestedAt_of_counting [Finite X] {T : Subgroup X}
    (hSE : fusionStronglyEmbedded (Subgroup.normalizer (T : Set X)))
    (hZ : ∀ z ∈ sylowCenter T, z ^ 2 = 1) (hZT : sylowCenter T ≤ ⁅T, T⁆)
    (hT2 : IsPGroup 2 T) {c o : ℕ}
    (hcent : ∀ x ∈ T, x ∉ sylowCenter T →
      Nat.card (T ⊓ Subgroup.centralizer ({x} : Set X) : Subgroup X) ≤ c)
    (horbit : ∀ x ∈ T, x ∉ sylowCenter T →
      o ≤ Set.ncard {y : X | ∃ n ∈ Subgroup.normalizer (T : Set X), y = n⁻¹ * x * n})
    (hco : 2 * c < o) (hoT : Nat.card T < 4 * o) : NestedAt T := by
  intro A₁ A₂ h₁ h₂ hc hcl
  by_cases hcen : A₁ ≤ sylowCenter T ∧ A₂ ≤ sylowCenter T
  · exact nested_of_le_center hSE hZ hcen.1 hcen.2 hcl
  obtain ⟨x, hxU, hxZ⟩ : ∃ x ∈ (A₁ : Set X) ∪ A₂, x ∉ sylowCenter T := by
    by_contra hcon
    push Not at hcon
    exact hcen ⟨fun y hy => hcon y (Or.inl hy), fun y hy => hcon y (Or.inr hy)⟩
  have hxT : x ∈ T := by
    rcases hxU with h | h
    · exact h₁ h
    · exact h₂ h
  set O : Set X := {y : X | ∃ n ∈ Subgroup.normalizer (T : Set X), y = n⁻¹ * x * n} with hO
  have hOU : O ⊆ (A₁ : Set X) ∪ A₂ := by
    rintro y ⟨n, hn, rfl⟩
    apply hcl x hxU n
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn)) x
    simpa using this.mp hxT
  have hOZ : ∀ y ∈ O, y ∉ sylowCenter T := by
    rintro y ⟨n, hn, rfl⟩ hy
    apply hxZ
    have := conj_mem_sylowCenter (Subgroup.inv_mem _ hn) hy
    simpa [mul_assoc] using this
  have hoO : o ≤ O.ncard := horbit x hxT hxZ
  have hcomm : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a := by
    intro a ha b hb
    have := Subgroup.commutator_mem_commutator ha hb
    rw [hc, Subgroup.mem_bot] at this
    exact commutatorElement_eq_one_iff_mul_comm.mp this
  by_cases hA₁ : A₁ ≤ sylowCenter T
  ·
    left
    have hOA₂ : O ⊆ A₂ := fun y hy => (hOU hy).resolve_left fun h => hOZ y hy (hA₁ h)
    have hcard : Nat.card T < 4 * Nat.card A₂ := by
      have : O.ncard ≤ Nat.card A₂ := by
        have hc' : Nat.card A₂ = (A₂ : Set X).ncard := Nat.card_coe_set_eq (A₂ : Set X)
        rw [hc']
        exact Set.ncard_le_ncard hOA₂ (Set.toFinite _)
      omega
    exact hA₁.trans (hZT.trans (commutator_le_of_card_lt h₂ hT2 hcard))
  by_cases hA₂ : A₂ ≤ sylowCenter T
  · right
    have hOA₁ : O ⊆ A₁ := fun y hy => (hOU hy).resolve_right fun h => hOZ y hy (hA₂ h)
    have hcard : Nat.card T < 4 * Nat.card A₁ := by
      have : O.ncard ≤ Nat.card A₁ := by
        have hc' : Nat.card A₁ = (A₁ : Set X).ncard := Nat.card_coe_set_eq (A₁ : Set X)
        rw [hc']
        exact Set.ncard_le_ncard hOA₁ (Set.toFinite _)
      omega
    exact hA₂.trans (hZT.trans (commutator_le_of_card_lt h₁ hT2 hcard))
  exfalso
  obtain ⟨x₁, hx₁, hx₁Z⟩ := Set.not_subset.mp hA₁
  obtain ⟨x₂, hx₂, hx₂Z⟩ := Set.not_subset.mp hA₂
  have hA₁C : A₁ ≤ T ⊓ Subgroup.centralizer ({x₂} : Set X) := fun a ha =>
    ⟨h₁ ha, Subgroup.mem_centralizer_singleton_iff.mpr (hcomm a ha x₂ hx₂)⟩
  have hA₂C : A₂ ≤ T ⊓ Subgroup.centralizer ({x₁} : Set X) := fun b hb =>
    ⟨h₂ hb, Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x₁ hx₁ b hb).symm⟩
  have hc₁ : Nat.card A₁ ≤ c :=
    (Subgroup.card_le_of_le hA₁C).trans (hcent x₂ (h₂ hx₂) hx₂Z)
  have hc₂ : Nat.card A₂ ≤ c :=
    (Subgroup.card_le_of_le hA₂C).trans (hcent x₁ (h₁ hx₁) hx₁Z)
  have hOle : O.ncard ≤ Nat.card A₁ + Nat.card A₂ := by
    calc O.ncard ≤ ((A₁ : Set X) ∪ A₂).ncard := Set.ncard_le_ncard hOU (Set.toFinite _)
      _ ≤ (A₁ : Set X).ncard + (A₂ : Set X).ncard := Set.ncard_union_le _ _
      _ = Nat.card A₁ + Nat.card A₂ := by
        rw [(Nat.card_coe_set_eq (A₁ : Set X)).symm, (Nat.card_coe_set_eq (A₂ : Set X)).symm]
        rfl
  omega

end Bender

end CFSG.ComponentClassification.AschbacherToolkit
