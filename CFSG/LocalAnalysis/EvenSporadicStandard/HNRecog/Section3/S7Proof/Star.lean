module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.S7Proof.Orbit
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.S7Proof.StarPair

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

theorem s7_star {a z x d : G} (H : S7Hyps a z) (hx : x ∈ orb3A a a)
    (hd : d ∈ orb2A a a ∩ orb2A a x) :
    ∃ t ∈ orb2A a a ∩ orb2A a x, t ≠ d ∧ d * t = t * d := by
  obtain ⟨x₀, d₀, t₀, hx₀, hd₀, ht₀, hne₀, hcomm₀⟩ := s7_exists_pair H
  obtain ⟨k, hk, hkx⟩ := (s7_orbit H).transitive x₀ hx₀ x hx
  have hd₁ : k * d₀ * k⁻¹ ∈ orb2A a a ∩ orb2A a x :=
    ⟨perp_conj_mem_orb2A hk hd₀.1, by
      have h := s7_conj_orb2A k hd₀.2
      rwa [hkx] at h⟩
  have ht₁ : k * t₀ * k⁻¹ ∈ orb2A a a ∩ orb2A a x :=
    ⟨perp_conj_mem_orb2A hk ht₀.1, by
      have h := s7_conj_orb2A k ht₀.2
      rwa [hkx] at h⟩
  have hne₁ : k * d₀ * k⁻¹ ≠ k * t₀ * k⁻¹ := by
    intro h
    exact hne₀ (mul_left_cancel (mul_right_cancel h))
  have hsSet : x ∈ sSet a z d 4 := s7_mem_sSet_four H hx.1 hx.2.1 hd
  have horbit := H.perp.self.class_3A d hd.1 x hsSet
  obtain ⟨k', hk', hk'eq⟩ := horbit.transitive (k * d₀ * k⁻¹) hd₁ d hd
  refine ⟨k' * (k * t₀ * k⁻¹) * k'⁻¹,
    horbit.conj_mem k' hk' (k * t₀ * k⁻¹) ht₁, ?_, ?_⟩
  · intro h
    rw [← hk'eq] at h
    exact hne₁ (mul_left_cancel (mul_right_cancel h)).symm
  · rw [← hk'eq]
    calc (k' * (k * d₀ * k⁻¹) * k'⁻¹) * (k' * (k * t₀ * k⁻¹) * k'⁻¹)
        = k' * (k * (d₀ * t₀) * k⁻¹) * k'⁻¹ := by group
      _ = k' * (k * (t₀ * d₀) * k⁻¹) * k'⁻¹ := by rw [hcomm₀]
      _ = (k' * (k * t₀ * k⁻¹) * k'⁻¹) * (k' * (k * d₀ * k⁻¹) * k'⁻¹) := by group

end CFSG.EvenSporadicStandard.HNRecog.Section3
