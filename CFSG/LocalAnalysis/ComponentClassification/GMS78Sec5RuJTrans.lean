module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuTrans
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuGammaDual

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools

namespace Sec3.SzR.MaskCoords

variable {G : Type} [Group G] [Finite G] {L T R : Subgroup G} {μ : G → ℕ} {ν : G → Fin 8}
  (hM : MaskCoords L T R μ ν)
include hM

theorem exists_conj_mem_centralizer_plane (hRp : IsPGroup 2 R)
    (hNC : normalizer (R : Set G) ⊓ centralizer (gmsA L T : Set G) = R)
    (hidx : R.relIndex (normalizer (R : Set G)) = 168)
    (hNA : normalizer (gmsA L T : Set G) = normalizer (R : Set G))
    (h216 : ∀ F₁ : Subgroup G, F₁ ≤ gmsA L T → Nat.card F₁ = 4 →
      normalizer (F₁ : Set G) ≤ normalizer (R : Set G))
    {S : Subgroup G} (hSN : IsSylowOf 2 S (normalizer (R : Set G))) (hRS : R ≤ S) {f : G}
    (hfA : f ∈ gmsA L T) (hf1 : f ≠ 1) (hfS : ∀ s ∈ S, s * f * s⁻¹ = f)
    (h210 : ∀ g ∈ S, g ∉ R → g ^ 2 ∈ R → ∃ y ∈ S, y ^ 2 = 1 ∧ g⁻¹ * y ∈ R)
    {X : Subgroup G} (hX : ∀ x, x ∈ X ↔ x ∈ R ∧ μ x ∈ 0 :: RuQCode.ppOf (ν f))
    {J : Subgroup G} (hJ : ∀ v, v ∈ J ↔ v ∈ S ∧ ∀ x ∈ X,
      v * x * v⁻¹ * x⁻¹ = 1 ∨ v * x * v⁻¹ * x⁻¹ = f)
    (hXH : centralizer ({f} : Set G) ≤ normalizer (X : Set G))
    (hnot : ¬ centralizer ({f} : Set G) ≤ normalizer (gmsA L T : Set G)) {j j' : G}
    (hj : j ∈ J) (hj' : j' ∈ J) (hjX : j ∉ centralizer (X : Set G))
    (hj'X : j' ∉ centralizer (X : Set G)) :
    ∃ h ∈ centralizer ({f} : Set G), h * j * h⁻¹ * j'⁻¹ ∈ J ⊓ centralizer (X : Set G) := by
  classical
  have hXel := hM.isElemAbelian_plane hX
  have hcardX := hM.card_plane hX hfA hf1
  have hfX : f ∈ X := hM.gmsA_le_plane hX hfA
  have hof : orderOf f = 2 := orderOf_eq_prime (hXel.2 f hfX) hf1
  have hZ : ∀ x : G, x ∈ zpowers f ↔ x = 1 ∨ x = f := by
    intro x
    rw [mem_zpowers_iff_mem_range_orderOf, hof]
    constructor
    · intro hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
      rw [Finset.mem_range] at ha
      interval_cases a
      · exact Or.inl (pow_zero f)
      · exact Or.inr (pow_one f)
    · rintro (h | h)
      · exact Finset.mem_image.2 ⟨0, by simp, by rw [h, pow_zero]⟩
      · exact Finset.mem_image.2 ⟨1, by simp, by rw [h, pow_one]⟩
  have hcardZ : Nat.card (zpowers f) = 2 := by rw [Nat.card_zpowers, hof]
  have hHZ : ∀ h ∈ centralizer ({f} : Set G), ∀ z ∈ zpowers f, h * z * h⁻¹ = z := by
    intro h hh z hz
    rcases (hZ z).1 hz with rfl | rfl
    · group
    · rw [mem_centralizer_singleton_iff.1 hh]
      group
  have hHX : ∀ h ∈ centralizer ({f} : Set G), ∀ x ∈ X, h * x * h⁻¹ ∈ X :=
    fun h hh x hx => (mem_normalizer_iff.1 (hXH hh) x).1 hx
  have hJ' : ∀ h, h ∈ J ↔ h ∈ centralizer ({f} : Set G) ∧
      ∀ x ∈ X, h * x * h⁻¹ * x⁻¹ ∈ zpowers f := by
    intro h
    rw [hM.mem_J_iff_of_mem_centralizer hNC hidx hNA hRp hSN hRS hfA hf1 hfS hX hJ h]
    simp only [hZ]
  have hidx120 := hM.relIndex_J_eq hRp hNC hidx h216 hSN hRS hfA hf1 hfS h210 hX hJ hXH hnot
  have htr : ∀ x ∈ X, x ∉ zpowers f → ∀ x' ∈ X, x' ∉ zpowers f →
      ∃ h ∈ centralizer ({f} : Set G), h * x * h⁻¹ * x'⁻¹ ∈ zpowers f := by
    intro x hx hxZ x' hx' hx'Z
    have hne : ∀ y, y ∉ zpowers f → y ≠ 1 ∧ y ≠ f := fun y hy =>
      ⟨fun h => hy ((hZ y).2 (Or.inl h)), fun h => hy ((hZ y).2 (Or.inr h))⟩
    obtain ⟨hx1, hxf⟩ := hne x hxZ
    obtain ⟨hx'1, hx'f⟩ := hne x' hx'Z
    obtain ⟨h, hh, hhx⟩ :=
      hM.exists_conj_eq_of_mem_plane hNC hidx hfA hf1 hX hXH hnot hx hx1 hxf hx' hx'1 hx'f
    refine ⟨h, hh, ?_⟩
    rw [hhx, mul_inv_cancel]
    exact one_mem _
  exact RuGamma.exists_conj_mul_inv_mem_centralizer hXel hcardX (zpowers_le.2 hfX) hcardZ hHZ hHX
    hJ' hidx120 htr hj hj' hjX hj'X

end Sec3.SzR.MaskCoords

end CFSG.ComponentClassification.GMS78
