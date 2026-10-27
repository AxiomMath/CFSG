module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.IndexTwoCosets
public import CFSG.Dihedral.DisconnectedInvolutionGraph.QuaternionCoordinateHom

public section

namespace CFSG.DisconnectedInvolutionGraph.Helpers

variable {G : Type*} [Group G]

theorem quaternionCoordinateHom_bijective (size : ℕ)
    (coordinates : Multiplicative (ZMod (2 * size)) →* G) (outside : G)
    (hsquare : outside ^ 2 = coordinates (Multiplicative.ofAdd (size : ZMod (2 * size))))
    (hinversion : ∀ coordinate, outside * coordinates coordinate * outside⁻¹ =
      (coordinates coordinate)⁻¹)
    (hinjective : Function.Injective coordinates) (hindex : coordinates.range.index = 2)
    (houtside : outside ∉ coordinates.range) :
    Function.Bijective (quaternionCoordinateHom size coordinates outside hsquare hinversion) := by
  have htypesDistinct : ∀ first second : ZMod (2 * size),
      coordinates (Multiplicative.ofAdd first) ≠
        outside * coordinates (Multiplicative.ofAdd second) := by
    intro first second hequal
    have hmem := coordinates.range.mul_mem
      (show coordinates (Multiplicative.ofAdd first) ∈ coordinates.range from ⟨_, rfl⟩)
      (coordinates.range.inv_mem
        (show coordinates (Multiplicative.ofAdd second) ∈ coordinates.range from ⟨_, rfl⟩))
    rw [hequal, mul_assoc, mul_inv_cancel, mul_one] at hmem
    exact houtside hmem
  constructor
  · intro first second hequal
    cases first with
    | a first =>
      cases second with
      | a second =>
        change coordinates (Multiplicative.ofAdd first) =
          coordinates (Multiplicative.ofAdd second) at hequal
        have hcoordinates := hinjective hequal
        exact congrArg QuaternionGroup.a (congrArg Multiplicative.toAdd hcoordinates)
      | xa second =>
        exact (htypesDistinct first second hequal).elim
    | xa first =>
      cases second with
      | a second =>
        exact (htypesDistinct second first hequal.symm).elim
      | xa second =>
        change outside * coordinates (Multiplicative.ofAdd first) =
          outside * coordinates (Multiplicative.ofAdd second) at hequal
        have hcoordinates := hinjective (mul_left_cancel hequal)
        exact congrArg QuaternionGroup.xa (congrArg Multiplicative.toAdd hcoordinates)
  · intro target
    by_cases hmem : target ∈ coordinates.range
    · obtain ⟨coordinate, rfl⟩ := hmem
      exact ⟨QuaternionGroup.a (Multiplicative.toAdd coordinate), rfl⟩
    · have houtsideInverse : outside⁻¹ ∉ coordinates.range := by
        intro hmem
        exact houtside (by simpa only [inv_inv] using coordinates.range.inv_mem hmem)
      have htargetInverse : target⁻¹ ∉ coordinates.range := by
        intro hmemInverse
        exact hmem (by simpa only [inv_inv] using coordinates.range.inv_mem hmemInverse)
      have hdifference : outside⁻¹ * target ∈ coordinates.range := by
        simpa only [inv_inv] using index_two_outside_quotient_equal coordinates.range
          hindex outside⁻¹ target⁻¹ houtsideInverse htargetInverse
      obtain ⟨coordinate, hcoordinate⟩ := hdifference
      refine ⟨QuaternionGroup.xa (Multiplicative.toAdd coordinate), ?_⟩
      change outside * coordinates coordinate = target
      rw [hcoordinate, mul_inv_cancel_left]

@[expose] noncomputable def quaternionCoordinateEquiv (size : ℕ)
    (coordinates : Multiplicative (ZMod (2 * size)) →* G) (outside : G)
    (hsquare : outside ^ 2 = coordinates (Multiplicative.ofAdd (size : ZMod (2 * size))))
    (hinversion : ∀ coordinate, outside * coordinates coordinate * outside⁻¹ =
      (coordinates coordinate)⁻¹)
    (hinjective : Function.Injective coordinates) (hindex : coordinates.range.index = 2)
    (houtside : outside ∉ coordinates.range) : QuaternionGroup size ≃* G :=
  MulEquiv.ofBijective (quaternionCoordinateHom size coordinates outside hsquare hinversion)
    (quaternionCoordinateHom_bijective size coordinates outside hsquare hinversion
      hinjective hindex houtside)

end CFSG.DisconnectedInvolutionGraph.Helpers
