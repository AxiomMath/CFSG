module

public import Mathlib.GroupTheory.FixedPointFree

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem conj_eq_inv_of_inf_centralizer_eq_bot {U : Subgroup G} {s : G} (hs : s * s = 1)
    (hU : ∀ u ∈ U, s * u * s⁻¹ ∈ U) (hfix : U ⊓ centralizer ({s} : Set G) = ⊥) :
    ∀ u ∈ U, s * u * s⁻¹ = u⁻¹ := by
  let φ : U →* U :=
    { toFun := fun a => ⟨s * (a : G) * s⁻¹, hU a a.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp [mul_assoc] }
  have hφ : MonoidHom.FixedPointFree φ := by
    intro a ha
    have h : s * (a : G) * s⁻¹ = a := congrArg Subtype.val ha
    have hmem : (a : G) ∈ U ⊓ centralizer ({s} : Set G) := by
      refine ⟨a.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc (a : G) * s = s * (a : G) * s⁻¹ * s := by rw [h]
        _ = s * (a : G) := by group
    rw [hfix, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hinv : Function.Involutive φ := by
    intro a
    apply Subtype.ext
    change s * (s * (a : G) * s⁻¹) * s⁻¹ = a
    have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
    rw [hs']
    calc s * (s * (a : G) * s) * s = (s * s) * (a : G) * (s * s) := by group
      _ = a := by rw [hs]; group
  have h := MonoidHom.FixedPointFree.coe_eq_inv_of_involutive hφ hinv
  intro u hu
  exact congrArg Subtype.val (congrFun h ⟨u, hu⟩)

end CFSG.EvenSporadicStandard.HNRecog.Harada
