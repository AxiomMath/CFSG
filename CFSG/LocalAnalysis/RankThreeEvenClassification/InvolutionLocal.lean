module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

def involutionSubgroup {G : Type u} [Group G] (involution : G) (hsquare : involution ^ 2 = 1) :
    Subgroup G where
  carrier := {element | element = 1 ∨ element = involution}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro first second (hfirst | hfirst) (hsecond | hsecond)
    · exact Or.inl (by rw [hfirst, hsecond, one_mul])
    · exact Or.inr (by rw [hfirst, hsecond, one_mul])
    · exact Or.inr (by rw [hfirst, hsecond, mul_one])
    · exact Or.inl (by rw [hfirst, hsecond]; simpa only [pow_two] using hsquare)
  inv_mem' := by
    rintro element (helement | helement)
    · exact Or.inl (by rw [helement, inv_one])
    · rw [helement]
      exact Or.inr (inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hsquare))

theorem involutionSubgroup_isPGroup {G : Type u} [Group G]
    (involution : G) (hsquare : involution ^ 2 = 1) :
    IsPGroup 2 (involutionSubgroup involution hsquare) := by
  apply IsPGroup.of_exponent_dvd_pow (n := 1)
  rw [pow_one]
  apply Monoid.exponent_dvd_of_forall_pow_eq_one
  intro element
  apply Subtype.ext
  rcases element.property with hone | hinvolution
  · simp only [Subgroup.coe_pow, Subgroup.coe_one, hone, one_pow]
  · simpa only [Subgroup.coe_pow, Subgroup.coe_one, hinvolution] using hsquare

theorem involutionSubgroup_ne_bot {G : Type u} [Group G]
    (involution : G) (hne : involution ≠ 1) (hsquare : involution ^ 2 = 1) :
    involutionSubgroup involution hsquare ≠ ⊥ := by
  intro hbot
  have hmem : involution ∈ involutionSubgroup involution hsquare := Or.inr rfl
  exact hne (Subgroup.mem_bot.mp (hbot ▸ hmem))

theorem normalizer_involutionSubgroup {G : Type u} [Group G]
    (involution : G) (hne : involution ≠ 1) (hsquare : involution ^ 2 = 1) :
    Subgroup.normalizer (involutionSubgroup involution hsquare : Set G) =
      Subgroup.centralizer ({involution} : Set G) := by
  apply le_antisymm
  · intro element hnormalizer
    have hconjugate := (Subgroup.mem_normalizer_iff.mp hnormalizer involution).mp
      (show involution ∈ involutionSubgroup involution hsquare from Or.inr rfl)
    have hfixed : element * involution * element⁻¹ = involution := by
      rcases hconjugate with hone | hinvolution
      · exact False.elim (hne ((map_eq_one_iff (MulAut.conj element)
          (MulAut.conj element).injective).mp hone))
      · exact hinvolution
    apply Subgroup.mem_centralizer_iff.mpr
    intro other hother
    have hotherEq : other = involution := Set.mem_singleton_iff.mp hother
    subst other
    have hcommute := congrArg (fun value : G => value * element) hfixed
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hcommute.symm
  · apply Subgroup.le_normalizer_iff.mpr
    intro element hcentral other hother
    rcases hother with hone | hinvolution
    · rw [hone]
      exact Or.inl (by simp)
    · rw [hinvolution]
      have hcommute := Subgroup.mem_centralizer_iff.mp hcentral involution
        (Set.mem_singleton involution)
      exact Or.inr (by rw [← hcommute, mul_assoc, mul_inv_cancel, mul_one])

theorem involution_centralizer_isTwoLocal {G : Type u} [Group G]
    (involution : G) (hne : involution ≠ 1) (hsquare : involution ^ 2 = 1) :
    IsTwoLocal (Subgroup.centralizer ({involution} : Set G)) := by
  exact ⟨involutionSubgroup involution hsquare, involutionSubgroup_ne_bot involution hne hsquare,
    involutionSubgroup_isPGroup involution hsquare,
    (normalizer_involutionSubgroup involution hne hsquare).symm⟩

theorem charTwoType_no_involution_component {G : Type u} [Group G] [Finite G]
    (hchar : IsCharTwoType G) : ¬HasInvolutionComponent G := by
  rintro ⟨involution, subgroup, hne, hsquare, hcomponent⟩
  exact charTwoType_no_local_component hchar (Subgroup.centralizer ({involution} : Set G))
    (involution_centralizer_isTwoLocal involution hne hsquare) subgroup hcomponent

end CFSG.RankThreeEvenClassification.Helpers
