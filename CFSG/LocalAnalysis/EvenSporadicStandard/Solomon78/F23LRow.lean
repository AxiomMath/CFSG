module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Finkelstein77.Lemma25

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Open CFSG.Blueprint.NativeSporadic

theorem mem_normalizer_of_weaklyClosedInNormalizer {G : Type*} [Group G] {W : Subgroup G}
    (hW : Finkelstein77.WeaklyClosedInNormalizer W) (c : G)
    (hc : ∀ w ∈ W, c⁻¹ * w * c ∈ normalizer (W : Set G)) : c ∈ normalizer (W : Set G) := by
  have hle : W.map (MulAut.conj c⁻¹).toMonoidHom ≤ normalizer (W : Set G) := by
    rintro _ ⟨w, hw, rfl⟩
    simpa [MulAut.conj_apply] using hc w hw
  have heq := hW c⁻¹ hle
  rw [mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    rw [← heq] at hn
    obtain ⟨w, hw, hwn⟩ := hn
    have : c * n * c⁻¹ = w := by
      rw [← hwn]
      simp [mul_assoc]
    rwa [this]
  · intro hn
    rw [← heq]
    exact ⟨c * n * c⁻¹, hn, by simp [mul_assoc]⟩

end CFSG.EvenSporadicStandard.Solomon78
