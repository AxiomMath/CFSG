module

public import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Group

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup

private lemma zpow_eq_one_or_self_of_mul_self {G : Type*} [Group G] {t : G} (ht : t * t = 1)
    (k : ℤ) : t ^ k = 1 ∨ t ^ k = t := by
  have hk : t ^ k = t ^ (k % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 2]
    rw [zpow_add, zpow_mul, zpow_two, ht, one_zpow, mul_one]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · exact Or.inl (by rw [hk, h, zpow_zero])
  · exact Or.inr (by rw [hk, h, zpow_one])

private lemma goldH_arith {k r n b m i₁ i₂ : ℕ} (E1 : k * r = n) (E2 : m * i₂ = n)
    (E3 : i₁ * b = k) (E4 : i₂ ≤ i₁) (hi : i₁ ≠ 0) (hkm : k ≤ m) :
    r * b ≤ m ∧ n * b ≤ m ^ 2 := by
  refine ⟨?_, ?_⟩
  · refine Nat.le_of_mul_le_mul_left (c := i₁) ?_ (Nat.pos_of_ne_zero hi)
    calc i₁ * (r * b) = (i₁ * b) * r := by ring
      _ = n := by rw [E3, E1]
      _ = m * i₂ := E2.symm
      _ ≤ m * i₁ := Nat.mul_le_mul_left m E4
      _ = i₁ * m := by ring
  · calc n * b = m * i₂ * b := by rw [E2]
      _ ≤ m * i₁ * b := Nat.mul_le_mul_right b (Nat.mul_le_mul_left m E4)
      _ = m * (i₁ * b) := by ring
      _ = m * k := by rw [E3]
      _ ≤ m * m := Nat.mul_le_mul_left m hkm
      _ = m ^ 2 := by ring

theorem goldH_count {G : Type*} [Group G] [Finite G] {A B₁ : Subgroup G} {t : G}
    (hab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hsq : ∀ a ∈ A, a * a = 1)
    (ht : t * t = 1) (hnorm : ∀ a ∈ A, t * a * t⁻¹ ∈ A)
    (hB₁A : B₁ ≤ A) (hB₁t : ∀ b ∈ B₁, t * b * t⁻¹ = b) :
    ∃ B₂ : Subgroup G, B₁ ≤ B₂ ∧ B₂ ≤ A ∧ (∀ x ∈ B₂, t * x * t⁻¹ * x⁻¹ ∈ B₁) ∧
      Nat.card (⁅A, zpowers t⁆ : Subgroup G) * Nat.card B₁ ≤ Nat.card B₂ ∧
      Nat.card A * Nat.card B₁ ≤ Nat.card B₂ ^ 2 := by
  have hinv : ∀ a ∈ A, a⁻¹ = a := fun a ha => inv_eq_of_mul_eq_one_right (hsq a ha)
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  obtain ⟨φ, hφ⟩ : ∃ φ : A →* G, ∀ x : A, φ x = (x : G) * (t * x * t⁻¹) := by
    refine ⟨MonoidHom.mk' (fun x : A => (x : G) * (t * x * t⁻¹)) ?_, fun _ => rfl⟩
    intro x y
    have h := hab y y.2 (t * x * t⁻¹) (hnorm x x.2)
    change ((x * y : A) : G) * (t * ((x * y : A) : G) * t⁻¹) =
      ((x : G) * (t * x * t⁻¹)) * ((y : G) * (t * y * t⁻¹))
    calc ((x * y : A) : G) * (t * ((x * y : A) : G) * t⁻¹)
        = (x : G) * ((y : G) * (t * x * t⁻¹)) * (t * y * t⁻¹) := by
          simp only [Subgroup.coe_mul]; group
      _ = (x : G) * ((t * x * t⁻¹) * (y : G)) * (t * y * t⁻¹) := by rw [h]
      _ = ((x : G) * (t * x * t⁻¹)) * ((y : G) * (t * y * t⁻¹)) := by group
  have hφA : ∀ x : A, φ x ∈ A := fun x => by
    rw [hφ]
    exact A.mul_mem x.2 (hnorm x x.2)
  have hcomm : ∀ x : A, t * (x : G) * t⁻¹ * (x : G)⁻¹ = φ x := fun x => by
    rw [hφ, hinv x x.2]
    exact hab _ (hnorm x x.2) x x.2
  have hφb : ∀ b (hb : b ∈ B₁), φ ⟨b, hB₁A hb⟩ = 1 := fun b hb => by
    rw [hφ]
    change b * (t * b * t⁻¹) = 1
    rw [hB₁t b hb]
    exact hsq b (hB₁A hb)
  have hφφ : ∀ x : A, φ ⟨φ x, hφA x⟩ = 1 := fun x => by
    have hu : t * (x : G) * t⁻¹ ∈ A := hnorm x x.2
    have h1 : t * (t * (x : G) * t⁻¹) * t⁻¹ = x := by
      rw [htinv]
      calc t * (t * (x : G) * t) * t = (t * t) * x * (t * t) := by group
        _ = x := by rw [ht]; group
    have h2 : t * ((x : G) * (t * x * t⁻¹)) * t⁻¹ = (t * x * t⁻¹) * x := by
      calc t * ((x : G) * (t * x * t⁻¹)) * t⁻¹
          = (t * x * t⁻¹) * (t * (t * x * t⁻¹) * t⁻¹) := by group
        _ = (t * x * t⁻¹) * x := by rw [h1]
    rw [hφ]
    change φ x * (t * φ x * t⁻¹) = 1
    rw [hφ x, h2]
    calc (x : G) * (t * x * t⁻¹) * ((t * x * t⁻¹) * x)
        = x * ((t * x * t⁻¹) * (t * x * t⁻¹)) * x := by group
      _ = 1 := by rw [hsq _ hu, mul_one]; exact hsq x x.2
  have hcomm_le : ⁅A, zpowers t⁆ ≤ φ.range := by
    rw [Subgroup.commutator_le]
    intro a ha s hs
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
    rcases zpow_eq_one_or_self_of_mul_self ht k with h | h
    · rw [h, commutatorElement_one_right]
      exact one_mem _
    · rw [h]
      refine MonoidHom.mem_range.2 ⟨⟨a, ha⟩, ?_⟩
      rw [hφ, commutatorElement_def, hinv a ha]
      change a * (t * a * t⁻¹) = a * t * a * t⁻¹
      group
  set K : Subgroup G := φ.ker.map A.subtype with hK
  set B₂ : Subgroup G := (B₁.comap φ).map A.subtype with hB₂
  have hB₁K : B₁ ≤ K := fun b hb =>
    Subgroup.mem_map.2 ⟨⟨b, hB₁A hb⟩, MonoidHom.mem_ker.2 (hφb b hb), rfl⟩
  have hRK : φ.range ≤ K := by
    intro y hy
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hy
    exact Subgroup.mem_map.2 ⟨⟨φ x, hφA x⟩, MonoidHom.mem_ker.2 (hφφ x), rfl⟩
  have hKB : K ≤ B₂ := by
    refine Subgroup.map_mono fun z hz => ?_
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 hz]
    exact B₁.one_mem
  have hi0 : B₁.relIndex K ≠ 0 := by
    change (B₁.subgroupOf K).index ≠ 0
    exact Subgroup.index_ne_zero_of_finite
  have hk : Nat.card K = Nat.card φ.ker := Subgroup.card_map_of_injective A.subtype_injective
  have hm : Nat.card B₂ = Nat.card (B₁.comap φ) :=
    Subgroup.card_map_of_injective A.subtype_injective
  have E1 : Nat.card φ.ker * Nat.card φ.range = Nat.card A :=
    Subgroup.card_ker_mul_card_range φ
  have E2 : Nat.card B₂ * B₁.relIndex φ.range = Nat.card A := by
    rw [hm, ← Subgroup.index_comap]
    exact Subgroup.card_mul_index _
  have E3 : B₁.relIndex K * Nat.card B₁ = Nat.card φ.ker := by
    have := Subgroup.relIndex_mul_card B₁ K
    rwa [inf_eq_left.2 hB₁K, hk] at this
  have E4 : B₁.relIndex φ.range ≤ B₁.relIndex K := Subgroup.relIndex_le_of_le_right hRK hi0
  have hkm : Nat.card φ.ker ≤ Nat.card B₂ := hk ▸ Subgroup.card_le_of_le hKB
  obtain ⟨ha, hb⟩ := goldH_arith E1 E2 E3 E4 hi0 hkm
  refine ⟨B₂, hB₁K.trans hKB, ?_, ?_, ?_, hb⟩
  · rintro _ ⟨z, -, rfl⟩
    exact z.2
  · rintro _ ⟨z, hz, rfl⟩
    change t * (z : G) * t⁻¹ * (z : G)⁻¹ ∈ B₁
    rw [hcomm z]
    exact hz
  · exact (Nat.mul_le_mul_right _ (Subgroup.card_le_of_le hcomm_le)).trans ha

end CFSG.EvenSporadicStandard.M24Std
