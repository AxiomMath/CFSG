module

public import CFSG.LieType.SteinbergBRMulEquivCores
public import CFSG.LieType.SteinbergBRSemidirectRadical
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple

public section

namespace CFSG.LieType.SteinbergBR

open Matrix SemidirectProduct

variable {F : Type*} [Field F]

theorem center_SL_eq_bot_of_charTwo [CharP F 2] {m : ℕ} (hm : 1 ≤ m)
    (h : m = 2 ∨ Nat.card F = 2) :
    Subgroup.center (SpecialLinearGroup (Fin m) F) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  rw [Fintype.card_fin] at hr
  have hr1 : r = 1 := by
    rcases h with rfl | hF
    · have h2 := sub_pow_char (p := 2) r 1
      rw [hr, one_pow, sub_self] at h2
      exact sub_eq_zero.1 ((pow_eq_zero_iff (by norm_num)).1 h2)
    · have hr0 : r ≠ 0 := by
        rintro rfl
        rw [zero_pow (by omega)] at hr
        exact zero_ne_one hr
      have hsub : Subsingleton Fˣ := by
        have hcard : Nat.card Fˣ = 1 := by rw [Nat.card_units, hF]
        exact (Nat.card_eq_one_iff_unique.1 hcard).1
      have := Subsingleton.elim (Units.mk0 r hr0) 1
      exact congrArg Units.val this
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hrA, hr1, map_one]
  rfl

variable {N : Type*} [CommGroup N] {m : ℕ} {φ : SpecialLinearGroup (Fin m) F →* MulAut N}

theorem radPre_eq_range_inl (hZ : Subgroup.center (SpecialLinearGroup (Fin m) F) = ⊥) :
    radPre φ = (inl : N →* N ⋊[φ] SpecialLinearGroup (Fin m) F).range := by
  rw [radPre, hZ, MonoidHom.comap_bot, range_inl_eq_ker_rightHom]

theorem semidirect_SL_even_structure [Finite F] (hm : 2 ≤ m)
    (h : 3 ≤ m ∨ ∃ s : Finset F, s.card = 4)
    (hZ : Subgroup.center (SpecialLinearGroup (Fin m) F) = ⊥) [Finite N] (hN : IsPGroup 2 N)
    {H : Type*} [Group H] (Φ : N ⋊[φ] SpecialLinearGroup (Fin m) F ≃* H) :
    CFSG.solvableRadical H =
      (inl : N →* N ⋊[φ] SpecialLinearGroup (Fin m) F).range.map Φ.toMonoidHom ∧
    CFSG.pCore 2 H = CFSG.solvableRadical H ∧
    Nat.card H = Nat.card N * Nat.card (SpecialLinearGroup (Fin m) F) ∧
    Nonempty (H ⧸ CFSG.solvableRadical H ≃* ProjectiveSpecialLinearGroup (Fin m) F) := by
  obtain ⟨hnt, hsimple, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := F) hm h
  have hperf := CFSG.LinearGroups.linear_projective_perfect (K := F) hm h
  have hns : ¬ Group.IsSolvable (ProjectiveSpecialLinearGroup (Fin m) F) :=
    not_isSolvable_of_isPerfect
  have hRadG := solvableRadical_eq_radPre (φ := φ) hsimple hns
  have hRad : CFSG.solvableRadical H = (radPre φ).map Φ.toMonoidHom := by
    rw [← solvableRadical_map_equiv Φ, hRadG]
  rw [radPre_eq_range_inl hZ] at hRad hRadG
  have : Finite (N ⋊[φ] SpecialLinearGroup (Fin m) F) :=
    Finite.of_equiv _ SemidirectProduct.equivProd.symm
  have hO2G : CFSG.pCore 2 (N ⋊[φ] SpecialLinearGroup (Fin m) F) =
      (inl : N →* N ⋊[φ] SpecialLinearGroup (Fin m) F).range := by
    refine le_antisymm (sSup_le fun K hK => ?_) (le_sSup ⟨?_, ?_⟩)
    · obtain ⟨hKn, hK2⟩ := hK
      have : Group.IsNilpotent K := hK2.isNilpotent
      rw [← hRadG]
      exact le_sSup ⟨hKn, inferInstance⟩
    · rw [range_inl_eq_ker_rightHom]
      infer_instance
    · exact hN.of_surjective _
        (inl : N →* N ⋊[φ] SpecialLinearGroup (Fin m) F).rangeRestrict_surjective
  refine ⟨hRad, ?_, ?_, ⟨?_⟩⟩
  · rw [← pCore_map_equiv 2 Φ, hO2G, hRad]
  · rw [← Nat.card_congr Φ.toEquiv, SemidirectProduct.card]
  · refine (QuotientGroup.congr (radPre φ) (CFSG.solvableRadical H) Φ ?_).symm.trans
      quotientRadPreEquiv
    rw [hRad, radPre_eq_range_inl hZ]
    rfl

end CFSG.LieType.SteinbergBR
