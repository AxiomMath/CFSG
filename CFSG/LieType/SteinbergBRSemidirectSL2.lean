module

public import CFSG.LieType.SteinbergBRSemidirectRadical
public import CFSG.LieType.SteinbergBRMulEquivCores
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple

public section

namespace CFSG.LieType.SteinbergBR

open Matrix SemidirectProduct

variable {F : Type*} [Field F]

theorem mem_center_SL2_iff {A : SpecialLinearGroup (Fin 2) F} :
    A ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) ↔ A.val = 1 ∨ A.val = -1 := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff, Fintype.card_fin]
  constructor
  · rintro ⟨r, hr, hA⟩
    rcases sq_eq_one_iff.1 hr with rfl | rfl
    · left
      rw [← hA, map_one]
    · right
      rw [← hA, map_neg, map_one]
  · rintro (h | h)
    · exact ⟨1, one_pow 2, by rw [map_one]; exact h.symm⟩
    · exact ⟨-1, by norm_num, by rw [map_neg, map_one]; exact h.symm⟩

theorem card_center_SL2_eq_two (hF : ringChar F ≠ 2) :
    Nat.card (Subgroup.center (SpecialLinearGroup (Fin 2) F)) = 2 := by
  have hne : (1 : SpecialLinearGroup (Fin 2) F) ≠ -1 := by
    intro h
    have h00 := congrArg (fun A : SpecialLinearGroup (Fin 2) F => A.val 0 0) h
    change (1 : Matrix (Fin 2) (Fin 2) F) 0 0 = -((1 : Matrix (Fin 2) (Fin 2) F) 0 0) at h00
    rw [Matrix.one_apply_eq] at h00
    exact Ring.neg_one_ne_one_of_char_ne_two hF h00.symm
  have hset : ((Subgroup.center (SpecialLinearGroup (Fin 2) F) :
      Set (SpecialLinearGroup (Fin 2) F))) = {1, -1} := by
    ext A
    rw [SetLike.mem_coe, mem_center_SL2_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact or_congr (Subtype.ext_iff (a1 := A) (a2 := (1 : SpecialLinearGroup (Fin 2) F))).symm
      (Subtype.ext_iff (a1 := A) (a2 := (-1 : SpecialLinearGroup (Fin 2) F))).symm
  rw [← SetLike.coe_sort_coe, hset, Nat.card_coe_set_eq, Set.ncard_pair hne]

variable {N : Type*} [CommGroup N] {φ : SpecialLinearGroup (Fin 2) F →* MulAut N}

theorem semidirect_SL2_structure [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p] (hp2 : p ≠ 2)
    (h4 : ∃ s : Finset F, s.card = 4) [Finite N] (hNp : IsPGroup p N)
    (hφ : Function.Injective φ) {H : Type*} [Group H]
    (Φ : N ⋊[φ] SpecialLinearGroup (Fin 2) F ≃* H) :
    CFSG.solvableRadical H = (radPre φ).map Φ.toMonoidHom ∧
    Nat.card H = Nat.card N * Nat.card (SpecialLinearGroup (Fin 2) F) ∧
    Nat.card (CFSG.solvableRadical H) = Nat.card N * 2 ∧
    Nonempty (H ⧸ CFSG.solvableRadical H ≃* ProjectiveSpecialLinearGroup (Fin 2) F) ∧
    CFSG.pCore 2 H = ⊥ := by
  have hF : ringChar F ≠ 2 := by rwa [ringChar.eq F p]
  obtain ⟨hnt, hsimple, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := F) le_rfl
    (Or.inr h4)
  have hperf := CFSG.LinearGroups.linear_projective_perfect (K := F) le_rfl (Or.inr h4)
  have hns : ¬ Group.IsSolvable (ProjectiveSpecialLinearGroup (Fin 2) F) :=
    not_isSolvable_of_isPerfect
  have hRad : CFSG.solvableRadical H = (radPre φ).map Φ.toMonoidHom := by
    rw [← solvableRadical_map_equiv Φ, solvableRadical_eq_radPre hsimple hns]
  refine ⟨hRad, ?_, ?_, ⟨?_⟩, ?_⟩
  · rw [← Nat.card_congr Φ.toEquiv, SemidirectProduct.card]
  · rw [hRad, Subgroup.card_map_of_injective Φ.injective, card_radPre,
      card_center_SL2_eq_two hF]
  · refine (QuotientGroup.congr (radPre φ) (CFSG.solvableRadical H) Φ ?_).symm.trans
      quotientRadPreEquiv
    rw [hRad]
    rfl
  · rw [← pCore_map_equiv 2 Φ, pCore_two_eq_bot hNp hp2 hφ, Subgroup.map_bot]

end CFSG.LieType.SteinbergBR
