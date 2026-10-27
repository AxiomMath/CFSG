module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.MatchingEquiv
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm

namespace Classif

variable {Ω : Type*} [DecidableEq Ω]

@[expose] def commOmega (ω : Perm Ω) : Subgroup (Perm Ω) where
  carrier := {w | ∀ z, ω (w z) = w (ω z)}
  mul_mem' := by
    intro a b ha hb z
    simp only [Perm.mul_apply]
    rw [ha, hb]
  one_mem' := fun z => rfl
  inv_mem' := by
    intro w hw z
    have h1 : w (ω (w⁻¹ z)) = ω z := by
      rw [← hw]; simp
    have := congrArg (⇑w⁻¹) h1
    simpa using this

theorem mem_commOmega {ω : Perm Ω} {w : Perm Ω} :
    w ∈ commOmega ω ↔ ∀ z, ω (w z) = w (ω z) := Iff.rfl

@[expose] def Cst (ω : Perm Ω) (hωω : ∀ x, ω (ω x) = x) (𝒞 : Set (Finset Ω))
    (hωC : ∀ F ∈ 𝒞, ∀ z ∈ F, ω z ∈ F) : Subgroup (Perm Ω) where
  carrier := {w | (∀ z, ω (w z) = w (ω z)) ∧ (∀ F ∈ 𝒞, ∀ z ∈ F, w z ∈ F) ∧
    (∀ z, (∀ F ∈ 𝒞, z ∉ F) → w z = z ∨ w z = ω z)}
  mul_mem' := by
    rintro a b ⟨ha1, ha2, ha3⟩ ⟨hb1, hb2, hb3⟩
    refine ⟨fun z => ?_, fun F hF z hz => ?_, fun z hz => ?_⟩
    · simp only [Perm.mul_apply]; rw [ha1, hb1]
    · exact ha2 F hF _ (hb2 F hF z hz)
    · simp only [Perm.mul_apply]
      have hωz : ∀ F ∈ 𝒞, ω z ∉ F := fun F hF h => hz F hF (by simpa [hωω] using hωC F hF _ h)
      rcases hb3 z hz with h | h
      · rw [h]; exact ha3 z hz
      · rw [h]
        rcases ha3 (ω z) hωz with h' | h'
        · exact Or.inr h'
        · exact Or.inl (by rw [h', hωω])
  one_mem' := by
    refine ⟨fun z => rfl, fun F _ z hz => hz, fun z _ => Or.inl rfl⟩
  inv_mem' := by
    rintro w ⟨h1, h2, h3⟩
    refine ⟨fun z => ?_, fun F hF z hz => ?_, fun z hz => ?_⟩
    · have h4 : w (ω (w⁻¹ z)) = ω z := by rw [← h1]; simp
      have := congrArg (⇑w⁻¹) h4
      simpa using this
    ·
      have hsub : F.image w ⊆ F := by
        intro t ht
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 ht
        exact h2 F hF y hy
      have heq : F.image w = F :=
        Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_image_of_injective _ w.injective])
      have : z ∈ F.image w := by rw [heq]; exact hz
      obtain ⟨y, hy, hyz⟩ := Finset.mem_image.1 this
      have : w⁻¹ z = y := by rw [← hyz]; simp
      rw [this]; exact hy
    · have hu : ∀ F ∈ 𝒞, w⁻¹ z ∉ F := by
        intro F hF h
        exact hz F hF (by simpa using h2 F hF _ h)
      have hww : w (w⁻¹ z) = z := by simp
      rcases h3 (w⁻¹ z) hu with h | h
      · left
        rw [hww] at h
        exact h.symm
      · right
        rw [hww] at h
        have := congrArg ω h
        rw [hωω] at this
        exact this.symm

end Classif

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
