module

public import CFSG.ClassicalInvolution.SmallCases.Sporadic.Basic
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.Sylow

public section

namespace CFSG.ClassicalInvolution

variable {M : Type*} [Group M]

theorem noNonsolvableClassical_of_sylow_cover_at (H S : Subgroup M) [Finite H]
    (hS : IsPGroup 2 S) (hidx : ¬ 2 ∣ (S.subgroupOf H).index) {z : M} (hz : z ∈ H)
    (hSz : ∀ s ∈ S, orderOf s = 2 → ∃ c ∈ H, s = c * z * c⁻¹)
    (hgood : NoNonsolvableClassicalAt (⟨z, hz⟩ : H)) : NoNonsolvableClassical H := by
  refine NoNonsolvableClassical.of_conj_reps {x : H | (x : M) = z} ?_ ?_
  · intro u hu
    have hu' : orderOf (u : M) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact hu
    obtain ⟨c, hc, he⟩ := cover_of_sylow H S hS hidx z hSz u u.2 hu'
    refine ⟨⟨z, hz⟩, rfl, ?_⟩
    rw [isConj_iff]
    refine ⟨⟨c, hc⟩, ?_⟩
    apply Subtype.ext
    simp [he]
  · rintro s hs
    have : s = ⟨z, hz⟩ := Subtype.ext hs
    rw [this]
    exact hgood

theorem noNonsolvableClassical_of_sylow_cover (H S : Subgroup M) [Finite H] (hS : IsPGroup 2 S)
    (hidx : ¬ 2 ∣ (S.subgroupOf H).index) {z : M} (hz : z ∈ H)
    (hSz : ∀ s ∈ S, orderOf s = 2 → ∃ c ∈ H, s = c * z * c⁻¹) (hgood : CentralizerGood H z) :
    NoNonsolvableClassical H :=
  noNonsolvableClassical_of_sylow_cover_at H S hS hidx hz hSz
    (NoNonsolvableClassicalAt.of_centralizerGood H ⟨z, hz⟩ hgood)

end CFSG.ClassicalInvolution
