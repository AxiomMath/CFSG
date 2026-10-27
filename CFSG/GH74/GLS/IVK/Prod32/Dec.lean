module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.CharacterTheory.Semidihedral.SemilinearOuterQuotient

public section

namespace CFSG.GH74.GLS.IVK.Prod3

open Subgroup CFSG

section Dec

variable {Q C : Type} [Group Q] [Group C] [IsCyclic C]

theorem exists_YA_decomp (hQ : Nat.card Q = 2) (X : Subgroup (Q × C)) {s : Q × C} (hsX : s ∈ X)
    (hs1 : s.1 = 1) :
    ∃ Yx Ax : Subgroup (Q × C), Yx ≤ X ∧ Ax ≤ X ∧ Yx ⊓ Ax = ⊥ ∧ Yx ⊔ Ax = X ∧ Nat.card Yx ≤ 2 ∧
      IsCyclic ↥Ax ∧ s ∈ Ax ∧ (∀ p ∈ Ax, p.2 = 1 → p = 1) ∧
      (Yx ≠ ⊥ → (∃ y ∈ X, Yx = zpowers y ∧ y.2 = 1 ∧ y.1 ≠ 1) ∧ ∀ p ∈ Ax, p.1 = 1) := by
  classical
  have hQfin : Finite Q := Nat.finite_of_card_ne_zero (by rw [hQ]; norm_num)
  set Y₀ : Subgroup (Q × C) := X ⊓ (MonoidHom.snd Q C).ker with hY₀
  set A₀ : Subgroup (Q × C) := X ⊓ (MonoidHom.fst Q C).ker with hA₀
  have hmemY : ∀ p, p ∈ Y₀ ↔ p ∈ X ∧ p.2 = 1 := fun p => by
    rw [hY₀, Subgroup.mem_inf, MonoidHom.mem_ker]; rfl
  have hmemA : ∀ p, p ∈ A₀ ↔ p ∈ X ∧ p.1 = 1 := fun p => by
    rw [hA₀, Subgroup.mem_inf, MonoidHom.mem_ker]; rfl
  have hinter : Y₀ ⊓ A₀ = ⊥ := by
    rw [eq_bot_iff]
    intro p hp
    rw [Subgroup.mem_inf, hmemY, hmemA] at hp
    rw [Subgroup.mem_bot]
    exact Prod.ext hp.2.2 hp.1.2
  have hcardY : Nat.card Y₀ ≤ 2 := by
    rw [← hQ]
    apply Nat.card_le_card_of_injective (fun p : Y₀ => (p : Q × C).1)
    intro p p' h
    apply Subtype.ext
    exact Prod.ext h (by rw [((hmemY p).mp p.2).2, ((hmemY p').mp p'.2).2])
  by_cases hY0 : Y₀ = ⊥
  ·
    have hinj : Function.Injective ((MonoidHom.snd Q C).comp X.subtype) := by
      rw [injective_iff_map_eq_one]
      intro p hp
      have h1 : (p : Q × C) ∈ Y₀ := (hmemY _).mpr ⟨p.2, hp⟩
      rw [hY0, Subgroup.mem_bot] at h1
      exact Subtype.ext h1
    refine ⟨⊥, X, bot_le, le_rfl, bot_inf_eq _, by simp, by simp, isCyclic_of_injective _ hinj, hsX,
      fun p hp hp2 => ?_, fun h => (h rfl).elim⟩
    have h1 : p ∈ Y₀ := (hmemY _).mpr ⟨hp, hp2⟩
    rw [hY0, Subgroup.mem_bot] at h1
    exact h1
  · obtain ⟨⟨y, hyY⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hY0
    have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
    have hyX : y ∈ X := ((hmemY y).mp hyY).1
    have hy2 : y.2 = 1 := ((hmemY y).mp hyY).2
    have hyq : y.1 ≠ 1 := fun h => hy1' (Prod.ext h hy2)
    refine ⟨Y₀, A₀, inf_le_left, inf_le_left, hinter, ?_, hcardY, ?_, (hmemA s).mpr ⟨hsX, hs1⟩,
      fun p hp hp2 => Prod.ext ((hmemA p).mp hp).2 hp2, ?_⟩
    · apply le_antisymm (sup_le inf_le_left inf_le_left)
      intro p hp
      by_cases hq : p.1 = 1
      · exact Subgroup.mem_sup_right ((hmemA p).mpr ⟨hp, hq⟩)
      · have hpy : p.1 = y.1 :=
          CFSG.Semidihedral.SemilinearOuterQuotient.eq_of_nonone_of_card_two hQ hq hyq
        have h5 : y⁻¹ * p ∈ A₀ := by
          rw [hmemA]
          refine ⟨X.mul_mem (X.inv_mem hyX) hp, ?_⟩
          simp [hpy]
        have h6 := Subgroup.mul_mem_sup hyY h5
        simpa using h6
    · have hinj : Function.Injective ((MonoidHom.snd Q C).comp A₀.subtype) := by
        rw [injective_iff_map_eq_one]
        intro p hp
        have h1 := ((hmemA _).mp p.2).2
        apply Subtype.ext
        exact Prod.ext h1 hp
      exact isCyclic_of_injective _ hinj
    · intro _
      refine ⟨⟨y, hyX, ?_, hy2, hyq⟩, fun p hp => ((hmemA p).mp hp).2⟩
      have hfin : Finite ↥Y₀ := Finite.of_injective (fun p : Y₀ => (p : Q × C).1) (by
        intro p p' h
        apply Subtype.ext
        exact Prod.ext h (by rw [((hmemY p).mp p.2).2, ((hmemY p').mp p'.2).2]))
      symm
      apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hyY)
      have hz : Nat.card (zpowers y) ≠ 1 := by
        intro h
        rw [Subgroup.card_eq_one] at h
        apply hy1'
        have : y ∈ zpowers y := Subgroup.mem_zpowers y
        rw [h] at this
        exact this
      have hpos : 0 < Nat.card (zpowers y) := by
        have : Finite ↥(zpowers y) := Finite.of_injective (Subgroup.inclusion (Subgroup.zpowers_le.mpr hyY))
          (Subgroup.inclusion_injective _)
        exact Nat.card_pos
      omega

end Dec
end CFSG.GH74.GLS.IVK.Prod3
