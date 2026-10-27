module

public import CFSG.ClassicalInvolution.Asc77.AscP1ThompsonBasic

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Disconnected

namespace Thompson

variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {W : Subgroup G}

theorem isStar_muDeltaE [Finite G]
    (hmul : ∀ {a : ↥(muGroup Ω W)}, a ∈ muDelta Ω W → a * a = 1)
    (hstar : ∀ R ∈ DSet Ω W, ∀ T ∈ DSet Ω W, ∀ S ∈ DSet Ω W, ∀ r ∈ R, ∀ t ∈ T, ∀ s ∈ S,
      r ∉ W → t ∉ W → s ∉ W → r * t * r⁻¹ * t⁻¹ ∉ W ⊔ OCW W →
        s * r * s⁻¹ * r⁻¹ ∈ W ⊔ OCW W ∨ s * t * s⁻¹ * t⁻¹ ∈ W ⊔ OCW W ∨
          s * (r * t * r⁻¹) * s⁻¹ * (r * t * r⁻¹)⁻¹ ∈ W ⊔ OCW W) :
    Star3T.IsStar (muDelta Ω W) := by
  rintro a ha b hb hab c hc
  have haa := hmul ha
  obtain ⟨R, hR, r, hr, hrW, hra⟩ := ha
  obtain ⟨T, hT, t, ht, htW, htb⟩ := hb
  obtain ⟨S, hS, s, hs, hsW, hsc⟩ := hc
  have hrN := hR.2 hr
  have htN := hT.2 ht
  have hsN := hS.2 hs
  have hnc : r * t * r⁻¹ * t⁻¹ ∉ W ⊔ OCW W := fun h => hab (by
    apply Subtype.ext
    show (a : NQuot (W ⊔ OCW W)) * b = b * a
    rw [hra, htb]
    exact (piG_comm_iff hrN htN).mpr h)
  rcases hstar R hR T hT S hS r hr t ht s hs hrW htW hsW hnc with h | h | h
  · left
    apply Subtype.ext
    show (c : NQuot (W ⊔ OCW W)) * a = a * c
    rw [hra, hsc]
    exact (piG_comm_iff hsN hrN).mpr h
  · right
    left
    apply Subtype.ext
    show (c : NQuot (W ⊔ OCW W)) * b = b * c
    rw [htb, hsc]
    exact (piG_comm_iff hsN htN).mpr h
  · right
    right
    apply Subtype.ext
    have hrtr : r * t * r⁻¹ ∈ Subgroup.normalizer (W : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hrN htN) (Subgroup.inv_mem _ hrN)
    have hinv : (piG W r)⁻¹ = piG W r := by
      have : (a : NQuot (W ⊔ OCW W)) * a = 1 := congrArg Subtype.val haa
      rw [hra] at this
      exact inv_eq_of_mul_eq_one_left this
    have e : (a : NQuot (W ⊔ OCW W)) * b * a = piG W (r * t * r⁻¹) := by
      rw [hra, htb, piG_mul (Subgroup.mul_mem _ hrN htN) (Subgroup.inv_mem _ hrN),
        piG_mul hrN htN, piG_inv hrN, hinv]
    show (c : NQuot (W ⊔ OCW W)) * ((a : NQuot (W ⊔ OCW W)) * b * a) =
      ((a : NQuot (W ⊔ OCW W)) * b * a) * c
    rw [e, hsc]
    exact (piG_comm_iff hsN hrtr).mpr h

end Thompson

end CFSG.ClassicalInvolution.Asc77
