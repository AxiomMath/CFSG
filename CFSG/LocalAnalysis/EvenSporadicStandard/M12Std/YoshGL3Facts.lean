module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import CFSG.Adapters.SpecialLinearPerfect
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open scoped commutatorElement

theorem card_gl32 : Nat.card (GL (Fin 3) (ZMod 2)) = 168 := by
  rw [Matrix.card_GL_field, ZMod.card]
  decide

theorem commutator_gl32 : commutator (GL (Fin 3) (ZMod 2)) = ⊤ := by
  haveI : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le le_rfl
  have hsurj : Function.Surjective
      (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) →* GL (Fin 3) (ZMod 2)) := fun g => by
    have hdet : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).det = 1 := by
      have hu : IsUnit (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).det :=
        g.isUnit.map Matrix.detMonoidHom
      obtain ⟨u, hu⟩ := hu
      rw [← hu, Subsingleton.elim u 1, Units.val_one]
    exact ⟨⟨g, hdet⟩, Units.ext rfl⟩
  haveI := Group.IsPerfect.ofSurjective hsurj
  exact Group.IsPerfect.commutator_eq_top

theorem center_gl32 : Subgroup.center (GL (Fin 3) (ZMod 2)) = ⊥ := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar, eq_bot_iff]
  rintro _ ⟨r, rfl⟩
  rw [Subsingleton.elim r 1, map_one]
  exact Subgroup.one_mem _

theorem commutator_eq_top_of_quotient_perfect {L : Type*} [Group L] [Finite L]
    (E : Subgroup L) [E.Normal] (hE : E ≤ commutator L) (hq : commutator (L ⧸ E) = ⊤) :
    commutator L = ⊤ := by
  have himg : (commutator L).map (QuotientGroup.mk' E) = ⊤ := by
    rw [map_commutator_eq, QuotientGroup.range_mk', ← commutator_def, hq]
  have h := Subgroup.comap_map_eq (QuotientGroup.mk' E) (commutator L)
  rw [himg, Subgroup.comap_top, QuotientGroup.ker_mk', sup_eq_left.2 hE] at h
  exact h.symm

private theorem ker_eq_subgroupOf {G H : Type*} [Group G] [Group H] (L E : Subgroup G)
    (ρ : ↥L →* H) (hker : ∀ ℓ : ↥L, ρ ℓ = 1 ↔ (ℓ : G) ∈ E) : ρ.ker = E.subgroupOf L := by
  ext ℓ
  rw [MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]

theorem surjective_of_card_gl3 {G : Type*} [Group G] [Finite G] (L E : Subgroup G) (hEL : E ≤ L)
    (ρ : ↥L →* GL (Fin 3) (ZMod 2)) (hker : ∀ ℓ : ↥L, ρ ℓ = 1 ↔ (ℓ : G) ∈ E)
    (hcard : Nat.card L = 168 * Nat.card E) :
    Function.Surjective ρ := by
  have h := Subgroup.card_ker_mul_card_range ρ
  rw [ker_eq_subgroupOf L E ρ hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv,
    hcard] at h
  have hpos : 0 < Nat.card E := Nat.card_pos
  have hrange : Nat.card ρ.range = 168 :=
    Nat.eq_of_mul_eq_mul_left hpos (h.trans (mul_comm _ _))
  exact MonoidHom.range_eq_top.1 (Subgroup.eq_top_of_card_eq _ (hrange.trans card_gl32.symm))

theorem quotient_equiv_gl3 {G : Type*} [Group G] [Finite G] (L E : Subgroup G) (hEL : E ≤ L)
    [(E.subgroupOf L).Normal]
    (ρ : ↥L →* GL (Fin 3) (ZMod 2)) (hker : ∀ ℓ : ↥L, ρ ℓ = 1 ↔ (ℓ : G) ∈ E)
    (hcard : Nat.card L = 168 * Nat.card E) :
    Nonempty (↥L ⧸ E.subgroupOf L ≃* GL (Fin 3) (ZMod 2)) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq (ker_eq_subgroupOf L E ρ hker).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ρ (surjective_of_card_gl3 L E hEL ρ hker hcard))⟩

theorem center_quotient_trivial {G : Type*} [Group G] [Finite G] (L E : Subgroup G) (hEL : E ≤ L)
    (ρ : ↥L →* GL (Fin 3) (ZMod 2)) (hker : ∀ ℓ : ↥L, ρ ℓ = 1 ↔ (ℓ : G) ∈ E)
    (hcard : Nat.card L = 168 * Nat.card E) :
    ∀ z ∈ L, (∀ ℓ ∈ L, ⁅z, ℓ⁆ ∈ E) → z ∈ E := by
  intro z hz hcomm
  have hsurj := surjective_of_card_gl3 L E hEL ρ hker hcard
  have hcentral : ρ ⟨z, hz⟩ ∈ Subgroup.center (GL (Fin 3) (ZMod 2)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨ℓ, rfl⟩ := hsurj g
    have h1 : ρ ⁅(⟨z, hz⟩ : ↥L), ℓ⁆ = 1 := (hker _).2 (hcomm ℓ ℓ.2)
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  rw [center_gl32, Subgroup.mem_bot] at hcentral
  exact (hker _).1 hcentral

end CFSG.EvenSporadicStandard.M12Std.Yosh
