module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutNOne
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.Rank

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.EvenSporadicStandard.M23Std

variable {G : Type} [Group G]

@[expose] def CentRank (z : G) : Prop :=
  ∀ B : Subgroup G, B ≤ centralizer ({z} : Set G) → (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
    (∀ x ∈ B, x * x = 1) → Nat.card B ≤ 64

theorem not_isConj_of_elemAb {z : G} (hC : CentRank z) {A : Subgroup G}
    (hc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hs : ∀ x ∈ A, x * x = 1)
    (hcard : 64 < Nat.card A) {u : G} (hu : u ∈ A) : ¬ IsConj z u := by
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
  have := hC _ hA' hc' hs'
  omega

namespace OutOne

variable [Finite G] {L : Subgroup G} {z : G} {F : Subgroup G} (h : OutOne L z F)

omit [Finite G] in
include h in
theorem elemAb_sup_zpowers {A : Subgroup G} (hA : A ≤ centralizer ({z} : Set G))
    (hc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hs : ∀ x ∈ A, x * x = 1) :
    (∀ x ∈ A ⊔ zpowers z, ∀ y ∈ A ⊔ zpowers z, x * y = y * x) ∧
      ∀ x ∈ A ⊔ zpowers z, x * x = 1 := by
  have hz : zpowers z ≤ centralizer (A : Set G) := by
    rw [Subgroup.zpowers_le]
    exact mem_centralizer_iff.2 fun a ha => mem_centralizer_singleton_iff.1 (hA ha)
  have hbc : ∀ b ∈ zpowers z, ∀ a ∈ A, a * b = b * a := fun b hb a ha =>
    mem_centralizer_iff.1 (hz hb) a ha
  have hcom : ∀ b ∈ zpowers z, ∀ b' ∈ zpowers z, b * b' = b' * b := fun b hb b' hb' => by
    rcases h.mem_zpowers_cases hb with rfl | rfl <;> rcases h.mem_zpowers_cases hb' with rfl | rfl
      <;> simp
  have hsq : ∀ b ∈ zpowers z, b * b = 1 := fun b hb => by
    rcases h.mem_zpowers_cases hb with rfl | rfl
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

include h in
theorem exists_elemAb_le_of_le_sup {A : Subgroup G} (hA : A ≤ L ⊔ zpowers z)
    (hc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hs : ∀ x ∈ A, x * x = 1) :
    ∃ B : Subgroup G, B ≤ L ∧ (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) ∧ (∀ x ∈ B, x * x = 1) ∧
      Nat.card A ≤ 2 * Nat.card B := by
  have hzL : zpowers z ≤ centralizer (L : Set G) := h.zpowers_le_cent le_rfl
  have hAz : A ≤ centralizer ({z} : Set G) := by
    intro a ha
    obtain ⟨l, hl, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hzL (hA ha)
    refine mem_centralizer_singleton_iff.2 ?_
    have hbz : b * z = z * b := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      exact ((Commute.refl z).zpow_left k).eq
    calc l * b * z = l * (b * z) := by rw [mul_assoc]
      _ = l * (z * b) := by rw [hbz]
      _ = (l * z) * b := by rw [mul_assoc]
      _ = (z * l) * b := by rw [h.z_comm l hl]
      _ = z * (l * b) := by rw [mul_assoc]
  obtain ⟨hc', hs'⟩ := h.elemAb_sup_zpowers hAz hc hs
  have hzS : z ∈ A ⊔ zpowers z := Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  refine ⟨(A ⊔ zpowers z) ⊓ L, inf_le_right,
    fun x hx y hy => hc' x hx.1 y hy.1, fun x hx => hs' x hx.1, ?_⟩
  have hBL : (A ⊔ zpowers z) ⊓ L ≤ L := inf_le_right
  have hle : A ≤ ((A ⊔ zpowers z) ⊓ L) ⊔ zpowers z := by
    intro a ha
    obtain ⟨l, hl, b, hb, hab⟩ := exists_mul_of_mem_sup_of_le_centralizer hzL (hA ha)
    have haS : a ∈ A ⊔ zpowers z := Subgroup.mem_sup_left ha
    rcases h.mem_zpowers_cases hb with hb1 | hbz
    · rw [hb1, mul_one] at hab
      have hlS : l ∈ A ⊔ zpowers z := hab ▸ haS
      rw [hab]
      exact Subgroup.mem_sup_left ⟨hlS, hl⟩
    · rw [hbz] at hab
      have hlS : l ∈ A ⊔ zpowers z := by
        have : l = a * z := by rw [hab, mul_assoc, h.z_mul_self, mul_one]
        rw [this]
        exact Subgroup.mul_mem _ haS hzS
      rw [hab]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hlS, hl⟩)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
  have h1 := Subgroup.card_le_of_le hle
  rw [h.card_sup_zpowers hBL] at h1
  omega

include h in
theorem centRank_of_rankFour (hR : RankFour L)
    (hidx : (L ⊔ zpowers z).relIndex (centralizer ({z} : Set G)) = 2) : CentRank z := by
  intro B hBC hc hs
  have hA : (L ⊔ zpowers z) ⊓ B ≤ L ⊔ zpowers z := inf_le_left
  obtain ⟨B₀, hB₀L, hB₀c, hB₀s, hcard⟩ := h.exists_elemAb_le_of_le_sup hA
    (fun x hx y hy => hc x hx.2 y hy.2) (fun x hx => hs x hx.2)
  have h16 := hR B₀ hB₀L hB₀c hB₀s
  have hne : (L ⊔ zpowers z).relIndex (centralizer ({z} : Set G)) ≠ 0 := by
    rw [hidx]
    norm_num
  have hrel : (L ⊔ zpowers z).relIndex B ≤ 2 := by
    rw [← hidx]
    exact Subgroup.relIndex_le_of_le_right hBC hne
  have hmul := Subgroup.relIndex_mul_card (H := L ⊔ zpowers z) (K := B)
  have hB : Nat.card B ≤ 2 * Nat.card ((L ⊔ zpowers z) ⊓ B : Subgroup G) := by
    rw [← hmul]
    exact Nat.mul_le_mul_right _ hrel
  omega

end OutOne

end CFSG.EvenSporadicStandard.M22Std
