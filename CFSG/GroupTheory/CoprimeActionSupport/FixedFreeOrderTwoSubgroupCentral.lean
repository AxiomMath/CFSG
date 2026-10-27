module


public import Mathlib.RepresentationTheory.Invariants
public import CFSG.GroupTheory.CoprimeActionSupport.InvolutionNoInvariantsNegativeIdentity

public section

namespace CFSG.GroupTheory.CoprimeActionSupport.FixedFreeOrderTwoSubgroupCentral

theorem le_center {F G V : Type*} [Field F] [Group G] [AddCommGroup V] [Module F V]
    (h2 : (2 : F) ≠ 0) (ρ : Representation F G V) (hρ : Function.Injective ρ)
    (D : Subgroup G) (hD : Nat.card D = 2)
    (hfix : Representation.invariants (ρ.comp D.subtype) = ⊥) :
    D ≤ Subgroup.center G := by
  obtain ⟨z, hz1⟩ : ∃ z : D, z ≠ 1 := by
    by_contra h
    push Not at h
    have : Nat.card D = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => by rw [h a, h b]⟩, ⟨1⟩⟩
    omega
  have hall : ∀ d : D, d = 1 ∨ d = z := by
    intro d
    have := Nat.card_eq_two_iff' (1 : D) |>.mp hD
    obtain ⟨y, _, hy⟩ := this
    by_cases hd : d = 1
    · exact Or.inl hd
    · exact Or.inr (by rw [hy d hd, hy z hz1])
  have hzz : z * z = 1 := by
    rcases hall (z * z) with h | h
    · exact h
    · exact absurd (mul_eq_right.mp h) hz1
  have hzzG : ((z : G)) * z = 1 := by
    have := congrArg Subtype.val hzz
    simpa using this
  have hneg : ρ (z : G) = -LinearMap.id := by
    apply CFSG.GroupTheory.CoprimeActionSupport.InvolutionNoInvariantsNegativeIdentity.eq_neg_id h2
    · rw [← map_mul, hzzG, map_one]
    · rw [eq_bot_iff]
      intro v hv
      have hv' : ρ (z : G) v = v := by
        have := LinearMap.mem_ker.mp hv
        simpa [sub_eq_zero] using this
      have : v ∈ Representation.invariants (ρ.comp D.subtype) := by
        rw [Representation.mem_invariants]
        intro d
        rcases hall d with h | h
        · subst h; simp
        · subst h; simpa using hv'
      rw [hfix] at this
      exact this
  have hzc : (z : G) ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply hρ
    rw [map_mul, map_mul, hneg]
    ext v
    simp
  intro d hd
  rcases hall ⟨d, hd⟩ with h | h
  · have : d = 1 := congrArg Subtype.val h
    rw [this]; exact one_mem _
  · have : d = z := congrArg Subtype.val h
    rw [this]; exact hzc

end CFSG.GroupTheory.CoprimeActionSupport.FixedFreeOrderTwoSubgroupCentral
