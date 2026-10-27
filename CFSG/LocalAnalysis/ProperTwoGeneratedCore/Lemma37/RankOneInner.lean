module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankOneFour

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly
open CFSG.ComponentClassification CFSG.ComponentClassification.OuterAutomorphisms
open Equiv

abbrev permOf {K : Type*} [Group K] (e : K ≃* alternatingGroup (Fin 5)) (y : K) : Perm (Fin 5) :=
  ((e y : alternatingGroup (Fin 5)) : Perm (Fin 5))

theorem permOf_injective {K : Type*} [Group K] (e : K ≃* alternatingGroup (Fin 5)) :
    Function.Injective (permOf e) :=
  fun _ _ hy => e.injective (Subtype.ext hy)

theorem permOf_mul {K : Type*} [Group K] (e : K ≃* alternatingGroup (Fin 5)) (y y' : K) :
    permOf e (y * y') = permOf e y * permOf e y' := by
  simp [permOf]

theorem permOf_inv {K : Type*} [Group K] (e : K ≃* alternatingGroup (Fin 5)) (y : K) :
    permOf e y⁻¹ = (permOf e y)⁻¹ := by
  simp [permOf]

theorem permOf_one {K : Type*} [Group K] (e : K ≃* alternatingGroup (Fin 5)) :
    permOf e 1 = 1 := by
  simp [permOf]

theorem sign_permOf {K : Type*} [Group K] (e : K ≃* alternatingGroup (Fin 5)) (y : K) :
    Perm.sign (permOf e y) = 1 :=
  Perm.mem_alternatingGroup.mp (e y).2

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {H : Subgroup G} {z : G}
  {J : Subgroup (EscapingQuotient z)}

namespace RankOneSetting

variable (h : RankOneSetting G S H z J) (P : Sylow 2 J)
  (hP : (P : Subgroup J).map J.subtype = escapingSylowImage S z ⊓ J)
  (eP : (P : Subgroup J) ≃* QuaternionGroup 2)
  (e : J ⧸ Subgroup.center J ≃* alternatingGroup (Fin 5))
include h

abbrev InFour (y : J ⧸ Subgroup.center J) : Prop :=
  y = 1 ∨ y = quaternionMap P eP (.a 1) ∨ y = quaternionMap P eP (.xa 0) ∨
    y = quaternionMap P eP (.a 1) * quaternionMap P eP (.xa 0)

theorem fourGroup :
    (Perm.sign (permOf e (quaternionMap P eP (.a 1))) = 1 ∧
      permOf e (quaternionMap P eP (.a 1)) * permOf e (quaternionMap P eP (.a 1)) = 1 ∧
      permOf e (quaternionMap P eP (.a 1)) ≠ 1) ∧
    (Perm.sign (permOf e (quaternionMap P eP (.xa 0))) = 1 ∧
      permOf e (quaternionMap P eP (.xa 0)) * permOf e (quaternionMap P eP (.xa 0)) = 1 ∧
      permOf e (quaternionMap P eP (.xa 0)) ≠ 1 ∧
      permOf e (quaternionMap P eP (.a 1)) ≠ permOf e (quaternionMap P eP (.xa 0)) ∧
      permOf e (quaternionMap P eP (.a 1)) * permOf e (quaternionMap P eP (.xa 0)) =
        permOf e (quaternionMap P eP (.xa 0)) * permOf e (quaternionMap P eP (.a 1))) := by
  obtain ⟨hA1, hB1, hAB⟩ := h.quaternionMap_ne P eP
  refine ⟨⟨sign_permOf e _, ?_, ?_⟩, sign_permOf e _, ?_, ?_, ?_, ?_⟩
  · rw [← permOf_mul, h.quaternionMap_sq P eP, permOf_one]
  · rw [← permOf_one e]
    exact fun h1 => hA1 (permOf_injective e h1)
  · rw [← permOf_mul, h.quaternionMap_sq P eP, permOf_one]
  · rw [← permOf_one e]
    exact fun h1 => hB1 (permOf_injective e h1)
  · exact fun h1 => hAB (permOf_injective e h1)
  · rw [← permOf_mul, ← permOf_mul, h.quaternionMap_commute P eP]

theorem inFour_iff (y : J ⧸ Subgroup.center J) :
    InFour P eP y ↔ ∃ g, quaternionMap P eP g = y := by
  constructor
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨1, map_one _⟩
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
    · exact ⟨.a 1 * .xa 0, map_mul _ _ _⟩
  · rintro ⟨g, rfl⟩
    exact h.quaternionMap_mem P eP g

theorem inFour_mul {y y' : J ⧸ Subgroup.center J} (hy : InFour P eP y) (hy' : InFour P eP y') :
    InFour P eP (y * y') := by
  obtain ⟨g, rfl⟩ := (h.inFour_iff P eP y).mp hy
  obtain ⟨g', rfl⟩ := (h.inFour_iff P eP _).mp hy'
  exact (h.inFour_iff P eP _).mpr ⟨g * g', map_mul _ _ _⟩

omit [Finite G] h in
theorem inFour_of_permOf {w : J ⧸ Subgroup.center J}
    (hw : permOf e w = permOf e (quaternionMap P eP (.a 1)) ∨
      permOf e w = permOf e (quaternionMap P eP (.xa 0)) ∨
      permOf e w = permOf e (quaternionMap P eP (.a 1)) * permOf e (quaternionMap P eP (.xa 0))) :
    InFour P eP w := by
  rcases hw with hw | hw | hw
  · exact Or.inr (Or.inl (permOf_injective e hw))
  · exact Or.inr (Or.inr (Or.inl (permOf_injective e hw)))
  · rw [← permOf_mul] at hw
    exact Or.inr (Or.inr (Or.inr (permOf_injective e hw)))

omit [Finite G] h in
theorem permOf_of_inFour {w : J ⧸ Subgroup.center J} (hw : InFour P eP w) (hw1 : w ≠ 1) :
    permOf e w = permOf e (quaternionMap P eP (.a 1)) ∨
      permOf e w = permOf e (quaternionMap P eP (.xa 0)) ∨
      permOf e w =
        permOf e (quaternionMap P eP (.a 1)) * permOf e (quaternionMap P eP (.xa 0)) := by
  rcases hw with hw | hw | hw | hw
  · exact absurd hw hw1
  · exact Or.inl (by rw [hw])
  · exact Or.inr (Or.inl (by rw [hw]))
  · exact Or.inr (Or.inr (by rw [hw, permOf_mul]))

theorem inFour_conj_of_normalizes {c' : J ⧸ Subgroup.center J}
    (hA : permOf e c' * permOf e (quaternionMap P eP (.a 1)) * (permOf e c')⁻¹ =
        permOf e (quaternionMap P eP (.a 1)) ∨
      permOf e c' * permOf e (quaternionMap P eP (.a 1)) * (permOf e c')⁻¹ =
        permOf e (quaternionMap P eP (.xa 0)) ∨
      permOf e c' * permOf e (quaternionMap P eP (.a 1)) * (permOf e c')⁻¹ =
        permOf e (quaternionMap P eP (.a 1)) * permOf e (quaternionMap P eP (.xa 0)))
    (hB : permOf e c' * permOf e (quaternionMap P eP (.xa 0)) * (permOf e c')⁻¹ =
        permOf e (quaternionMap P eP (.a 1)) ∨
      permOf e c' * permOf e (quaternionMap P eP (.xa 0)) * (permOf e c')⁻¹ =
        permOf e (quaternionMap P eP (.xa 0)) ∨
      permOf e c' * permOf e (quaternionMap P eP (.xa 0)) * (permOf e c')⁻¹ =
        permOf e (quaternionMap P eP (.a 1)) * permOf e (quaternionMap P eP (.xa 0)))
    {y : J ⧸ Subgroup.center J} (hy : InFour P eP y) : InFour P eP (c' * y * c'⁻¹) := by
  have hA' : InFour P eP (c' * quaternionMap P eP (.a 1) * c'⁻¹) :=
    inFour_of_permOf P eP e (by rwa [permOf_mul, permOf_mul, permOf_inv])
  have hB' : InFour P eP (c' * quaternionMap P eP (.xa 0) * c'⁻¹) :=
    inFour_of_permOf P eP e (by rwa [permOf_mul, permOf_mul, permOf_inv])
  rcases hy with rfl | rfl | rfl | rfl
  · left
    group
  · exact hA'
  · exact hB'
  · have := h.inFour_mul P eP hA' hB'
    rwa [show c' * quaternionMap P eP (.a 1) * c'⁻¹ * (c' * quaternionMap P eP (.xa 0) * c'⁻¹) =
      c' * (quaternionMap P eP (.a 1) * quaternionMap P eP (.xa 0)) * c'⁻¹ by group] at this

end RankOneSetting

end CFSG.ProperTwoGeneratedCore.Lemma37
