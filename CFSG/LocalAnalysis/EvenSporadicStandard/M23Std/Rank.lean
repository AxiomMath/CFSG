module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.Fusion

public section

namespace CFSG.EvenSporadicStandard.M23Std

open Subgroup

variable {G : Type} [Group G]

@[expose] def RankFour (L : Subgroup G) : Prop :=
  ∀ B : Subgroup G, B ≤ L → (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
    Nat.card B ≤ 16

variable [Finite G] {L : Subgroup G} {z t : G}

omit [Finite G] in
theorem elemAb_sup_zpowers (h : OneClassData L z t) {A : Subgroup G}
    (hA : A ≤ centralizer ({z} : Set G)) (hc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hs : ∀ x ∈ A, x * x = 1) :
    (∀ x ∈ A ⊔ zpowers z, ∀ y ∈ A ⊔ zpowers z, x * y = y * x) ∧
      ∀ x ∈ A ⊔ zpowers z, x * x = 1 := by
  have hz : zpowers z ≤ centralizer (A : Set G) := by
    rw [Subgroup.zpowers_le]
    exact mem_centralizer_iff.2 fun a ha => mem_centralizer_singleton_iff.1 (hA ha)
  have hbc : ∀ b ∈ zpowers z, ∀ a ∈ A, a * b = b * a := fun b hb a ha =>
    mem_centralizer_iff.1 (hz hb) a ha
  have hbb : ∀ b ∈ zpowers z, b = 1 ∨ b = z := fun b hb => mem_zpowers_involution h.z_mul_self hb
  have hcom : ∀ b ∈ zpowers z, ∀ b' ∈ zpowers z, b * b' = b' * b := fun b hb b' hb' => by
    rcases hbb b hb with rfl | rfl <;> rcases hbb b' hb' with rfl | rfl <;> simp
  have hsq : ∀ b ∈ zpowers z, b * b = 1 := fun b hb => by
    rcases hbb b hb with rfl | rfl
    · simp
    · exact h.z_mul_self
  constructor
  · intro x hx y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hz hx
    obtain ⟨a', ha', b', hb', rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hz hy
    calc a * b * (a' * b') = a * (b * a') * b' := by simp only [mul_assoc]
      _ = a * (a' * b) * b' := by rw [hbc b hb a' ha']
      _ = (a * a') * (b * b') := by simp only [mul_assoc]
      _ = (a' * a) * (b' * b) := by rw [hc a ha a' ha', hcom b hb b' hb']
      _ = a' * (a * b') * b := by simp only [mul_assoc]
      _ = a' * (b' * a) * b := by rw [hbc b' hb' a ha]
      _ = a' * b' * (a * b) := by simp only [mul_assoc]
  · intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hz hx
    calc a * b * (a * b) = a * (b * a) * b := by simp only [mul_assoc]
      _ = a * (a * b) * b := by rw [hbc b hb a ha]
      _ = (a * a) * (b * b) := by simp only [mul_assoc]
      _ = 1 := by rw [hs a ha, hsq b hb, mul_one]

theorem exists_elemAb_le_of_le_centralizer (h : OneClassData L z t) {A : Subgroup G}
    (hA : A ≤ centralizer ({z} : Set G)) (hc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hs : ∀ x ∈ A, x * x = 1) :
    ∃ B : Subgroup G, B ≤ L ∧ (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) ∧ (∀ x ∈ B, x * x = 1) ∧
      Nat.card A ≤ 2 * Nat.card B := by
  obtain ⟨hc', hs'⟩ := elemAb_sup_zpowers h hA hc hs
  have hzS : z ∈ A ⊔ zpowers z := Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  refine ⟨(A ⊔ zpowers z) ⊓ L, inf_le_right,
    fun x hx y hy => hc' x hx.1 y hy.1, fun x hx => hs' x hx.1, ?_⟩
  have hBL : (A ⊔ zpowers z) ⊓ L ≤ L := inf_le_right
  have hle : A ≤ ((A ⊔ zpowers z) ⊓ L) ⊔ zpowers z := by
    intro a ha
    have haz : z * a = a * z := (mem_centralizer_singleton_iff.1 (hA ha)).symm
    obtain ⟨l, hl, hcases⟩ := h.centralizer_z a haz
    have haS : a ∈ A ⊔ zpowers z := Subgroup.mem_sup_left ha
    rcases hcases with rfl | rfl
    · exact Subgroup.mem_sup_left ⟨haS, hl⟩
    · have hlS : l ∈ A ⊔ zpowers z := by
        have : l = l * z * z := by rw [mul_assoc, h.z_mul_self, mul_one]
        rw [this]
        exact Subgroup.mul_mem _ haS hzS
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hlS, hl⟩)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
  have h1 := Subgroup.card_le_of_le hle
  rw [card_sup_zpowers h hBL] at h1
  omega

theorem card_le_of_le_centralizer (h : OneClassData L z t) (hR : RankFour L) {A : Subgroup G}
    (hA : A ≤ centralizer ({z} : Set G)) (hc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hs : ∀ x ∈ A, x * x = 1) : Nat.card A ≤ 32 := by
  obtain ⟨B, hBL, hBc, hBs, hcard⟩ := exists_elemAb_le_of_le_centralizer h hA hc hs
  have := hR B hBL hBc hBs
  omega

theorem not_isConj_of_elemAb (h : OneClassData L z t) (hR : RankFour L) {A : Subgroup G}
    (hc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hs : ∀ x ∈ A, x * x = 1)
    (hcard : 32 < Nat.card A) {u : G} (hu : u ∈ A) : ¬ IsConj z u := by
  intro hconj
  obtain ⟨c, hcu⟩ := isConj_iff.1 hconj
  let φ : G ≃* G := MulAut.conj c⁻¹
  have hφ : ∀ x, φ x = c⁻¹ * x * c := fun x => by simp [φ]
  have hA' : A.map φ.toMonoidHom ≤ centralizer ({z} : Set G) := by
    rintro _ ⟨a, ha, rfl⟩
    refine mem_centralizer_singleton_iff.2 ?_
    have h1 := hc a ha u hu
    show φ a * z = z * φ a
    rw [hφ]
    calc c⁻¹ * a * c * z = c⁻¹ * a * (c * z * c⁻¹) * c := by group
      _ = c⁻¹ * (a * u) * c := by rw [hcu]; group
      _ = c⁻¹ * (u * a) * c := by rw [h1]
      _ = c⁻¹ * ((c * z * c⁻¹) * a) * c := by rw [hcu]
      _ = z * (c⁻¹ * a * c) := by group
  have hc' : ∀ x ∈ A.map φ.toMonoidHom, ∀ y ∈ A.map φ.toMonoidHom, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    show φ a * φ b = φ b * φ a
    rw [← map_mul, ← map_mul, hc a ha b hb]
  have hs' : ∀ x ∈ A.map φ.toMonoidHom, x * x = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    show φ a * φ a = 1
    rw [← map_mul, hs a ha, map_one]
  have hcard' : Nat.card (A.map φ.toMonoidHom) = Nat.card A :=
    Subgroup.card_map_of_injective φ.injective
  have := card_le_of_le_centralizer h hR hA' hc' hs'
  omega

end CFSG.EvenSporadicStandard.M23Std
