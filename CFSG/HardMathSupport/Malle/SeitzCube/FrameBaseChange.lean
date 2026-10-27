module

public import CFSG.LieType.Chevalley.CoordinateFieldBaseChange
public import CFSG.LieType.Steinberg.Classical.SpecialLinear
public import CFSG.LinearAlgebra.LinearGroups.Generation

public noncomputable section

namespace CFSG.HardMathSupport.Malle.SeitzCube

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped MatrixGroups

local notation "RA2" => CFSG.LieType.RootSystem.roots
  (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A 2) (∅ : Set (Fin 2))

section Main

variable {K L : Type} [Field K] [Field L]

theorem mem_RA2_of_toStd {γ : Fin 2 → ℤ} {i j : Fin 3} (hij : i ≠ j)
    (h : CFSG.LieType.Universal.SpecialLinear.toStd 2 γ = Pi.single i 1 - Pi.single j 1) :
    γ ∈ RA2 := by
  rw [CFSG.LieType.Universal.SpecialLinear.roots_eq]
  exact ⟨i, j, hij, h⟩

theorem map_x_sl3 (f : K →+* L) (γ : Fin 2 → ℤ) (c : K) :
    Matrix.SpecialLinearGroup.map (n := Fin 3) f (CFSG.LieType.Steinberg.SL.x 2 K γ c) =
      CFSG.LieType.Steinberg.SL.x 2 L γ (f c) := by
  unfold CFSG.LieType.Steinberg.SL.x
  split_ifs with h
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.map_apply_coe]
    ext a b
    by_cases hab : a = b
    · subst hab
      by_cases hp : (LieType.Steinberg.SL.pairOf 2 γ).1 = a ∧ (LieType.Steinberg.SL.pairOf 2 γ).2 = a
      · simp [Matrix.SpecialLinearGroup.transvection, Matrix.transvection, hp]
      · simp [Matrix.SpecialLinearGroup.transvection, Matrix.transvection, hp]
    · simp [Matrix.SpecialLinearGroup.transvection, Matrix.transvection, Matrix.single_apply, hab]
      split_ifs <;> simp_all
  · simp

end Main

section Frame

variable {τ : Tag} {K L : Type} [Field K] [Field L]

theorem sl3Hom_map_eq_of_pinnedX
    (f : K →+* L)
    (δ : (Fin 2 → ℤ) → Fin τ.rank → ℤ) (s : (Fin 2 → ℤ) → ℤ)
    (ψK : SL(3, K) →* ModGL τ K) (ψL : SL(3, L) →* ModGL τ L)
    (hK : ∀ γ ∈ RA2, ∀ c : K,
      ψK (CFSG.LieType.Steinberg.SL.x 2 K γ c) = pinnedX τ K (δ γ) ((s γ : K) * c))
    (hL : ∀ γ ∈ RA2, ∀ c : L,
      ψL (CFSG.LieType.Steinberg.SL.x 2 L γ c) = pinnedX τ L (δ γ) ((s γ : L) * c))
    (A : SL(3, K)) :
    ψL (Matrix.SpecialLinearGroup.map (n := Fin 3) f A) = baseChangeGL f (ψK A) := by
  have hgen : ∀ γ ∈ RA2, ∀ c : K,
      ψL (Matrix.SpecialLinearGroup.map (n := Fin 3) f (CFSG.LieType.Steinberg.SL.x 2 K γ c)) =
        baseChangeGL f (ψK (CFSG.LieType.Steinberg.SL.x 2 K γ c)) := by
    intro γ hγ c
    rw [map_x_sl3, hL γ hγ, hK γ hγ, baseChangeGL_pinnedX]
    rw [map_mul, map_intCast]
  have hT : ∀ X ∈ CFSG.LinearGroups.elementarySet 3 K, X ∈ Subgroup.closure
      {B : SL(3, K) | ∃ γ ∈ RA2, ∃ c : K, B = CFSG.LieType.Steinberg.SL.x 2 K γ c} := by
    rintro _ ⟨a, b, hab, t, rfl⟩
    fin_cases a <;> fin_cases b
    · exact absurd rfl hab
    · exact Subgroup.subset_closure ⟨![1, 0], mem_RA2_of_toStd hab (by decide), t,
        (CFSG.LieType.Steinberg.SL.x_eq hab (by decide) t).symm⟩
    · exact Subgroup.subset_closure ⟨![1, 1], mem_RA2_of_toStd hab (by decide), t,
        (CFSG.LieType.Steinberg.SL.x_eq hab (by decide) t).symm⟩
    · exact Subgroup.subset_closure ⟨![-1, 0], mem_RA2_of_toStd hab (by decide), t,
        (CFSG.LieType.Steinberg.SL.x_eq hab (by decide) t).symm⟩
    · exact absurd rfl hab
    · exact Subgroup.subset_closure ⟨![0, 1], mem_RA2_of_toStd hab (by decide), t,
        (CFSG.LieType.Steinberg.SL.x_eq hab (by decide) t).symm⟩
    · exact Subgroup.subset_closure ⟨![-1, -1], mem_RA2_of_toStd hab (by decide), t,
        (CFSG.LieType.Steinberg.SL.x_eq hab (by decide) t).symm⟩
    · exact Subgroup.subset_closure ⟨![0, -1], mem_RA2_of_toStd hab (by decide), t,
        (CFSG.LieType.Steinberg.SL.x_eq hab (by decide) t).symm⟩
    · exact absurd rfl hab
  have hall : ∀ X : SL(3, K), X ∈ Subgroup.closure
      {B : SL(3, K) | ∃ γ ∈ RA2, ∃ c : K, B = CFSG.LieType.Steinberg.SL.x 2 K γ c} := by
    intro X
    have hle : Subgroup.closure (CFSG.LinearGroups.elementarySet 3 K) ≤ Subgroup.closure
        {B : SL(3, K) | ∃ γ ∈ RA2, ∃ c : K, B = CFSG.LieType.Steinberg.SL.x 2 K γ c} :=
      (Subgroup.closure_le _).2 (fun X hX => hT X hX)
    exact hle (by rw [CFSG.LinearGroups.special_linear_elementary_generation]; trivial)
  have key : ∀ X ∈ Subgroup.closure
      {B : SL(3, K) | ∃ γ ∈ RA2, ∃ c : K, B = CFSG.LieType.Steinberg.SL.x 2 K γ c},
      ψL (Matrix.SpecialLinearGroup.map (n := Fin 3) f X) = baseChangeGL f (ψK X) := by
    intro X hX
    induction hX using Subgroup.closure_induction with
    | mem B hB =>
      obtain ⟨γ, hγ, c, rfl⟩ := hB
      exact hgen γ hγ c
    | one => simp only [map_one]
    | mul X Y _ _ hX hY => simp only [map_mul, hX, hY]
    | inv X _ hX => simp only [map_inv, hX]
  exact key A (hall A)

end Frame

end CFSG.HardMathSupport.Malle.SeitzCube
