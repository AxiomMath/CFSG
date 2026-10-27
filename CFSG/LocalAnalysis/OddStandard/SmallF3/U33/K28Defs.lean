module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.WreathOf
public import CFSG.GH74.KGroups.U33

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.K28

open CFSG.GH74.KGroups CFSG.GH74.KGroups.U33 CFSG.Sporadic.Schreier CFSG.Certificates

abbrev Pm := Equiv.Perm (Fin 28)

@[expose] def fx₁ : Pm :=
  List.formPerm [0, 10, 18, 14] * List.formPerm [1, 13, 11, 6]
   * List.formPerm [2, 23, 7, 27] * List.formPerm [3, 20] * List.formPerm [4, 24]
   * List.formPerm [5, 26, 9, 21] * List.formPerm [8, 16, 25, 17]
   * List.formPerm [12, 22, 19, 15]

@[expose] def fx₂ : Pm :=
  List.formPerm [0, 23, 25, 21] * List.formPerm [1, 11] * List.formPerm [2, 16, 9, 14]
   * List.formPerm [3, 4, 20, 24] * List.formPerm [5, 10, 7, 17] * List.formPerm [6, 13]
   * List.formPerm [8, 26, 18, 27] * List.formPerm [12, 15, 19, 22]

@[expose] def flam : Pm :=
  List.formPerm [1, 4] * List.formPerm [2, 5] * List.formPerm [3, 6]
   * List.formPerm [10, 23] * List.formPerm [11, 24] * List.formPerm [12, 22]
   * List.formPerm [13, 20] * List.formPerm [14, 21] * List.formPerm [15, 19]
   * List.formPerm [16, 26] * List.formPerm [17, 27] * List.formPerm [18, 25]

@[expose] def frho : Pm :=
  List.formPerm [0, 18, 25] * List.formPerm [1, 20, 19] * List.formPerm [2, 26, 17]
   * List.formPerm [3, 12, 11] * List.formPerm [4, 15, 13] * List.formPerm [5, 27, 16]
   * List.formPerm [6, 24, 22] * List.formPerm [7, 23, 10] * List.formPerm [9, 21, 14]

@[expose] def ftau : Pm :=
  List.formPerm [1, 6] * List.formPerm [2, 5] * List.formPerm [3, 4]
   * List.formPerm [7, 9] * List.formPerm [10, 14] * List.formPerm [11, 13]
   * List.formPerm [12, 15] * List.formPerm [16, 17] * List.formPerm [19, 22]
   * List.formPerm [20, 24] * List.formPerm [21, 23] * List.formPerm [26, 27]

@[expose] def fk0 : Pm :=
  List.formPerm [0, 1, 6, 26, 19, 9, 27, 18, 21, 25, 14, 12]
   * List.formPerm [2, 11, 3, 13, 16, 5, 24, 23, 15, 8, 4, 10] * List.formPerm [7, 17, 22]

@[expose] def fg3 : Pm :=
  List.formPerm [0, 10, 11] * List.formPerm [1, 8, 16] * List.formPerm [2, 14, 4]
   * List.formPerm [3, 25, 23] * List.formPerm [5, 17, 24] * List.formPerm [6, 9, 21]
   * List.formPerm [7, 27, 13] * List.formPerm [15, 19, 22] * List.formPerm [18, 26, 20]

@[expose] def fy : Pm := fx₁ ^ 2

@[expose] def fz : Pm := (fx₁ * fx₂) ^ 2

@[expose] def letterP : Fin 4 → Pm
  | 0 => pa
  | 1 => pb
  | 2 => pa⁻¹
  | 3 => pb⁻¹

@[expose] def wordP (w : List (Fin 4)) : Pm := (w.map letterP).prod

theorem QA_closure : QA.originalSubgroup = Subgroup.closure {pa, pb, sg0} := by
  rw [QA, certificate_originalSubgroup]
  congr 1
  ext g
  simp

theorem wordP_mem (w : List (Fin 4)) : wordP w ∈ QP.originalSubgroup := by
  rw [QP_closure]
  apply Subgroup.list_prod_mem
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨i, -, rfl⟩ := hx
  fin_cases i <;> simp only [letterP]
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))
  · exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))

theorem P_le_A : QP.originalSubgroup ≤ QA.originalSubgroup := by
  rw [QP_closure, QA_closure]
  exact Subgroup.closure_mono (by rintro g (rfl | rfl) <;> simp)

theorem fx₁_pow : fx₁ ^ 4 = 1 ∧ fx₁ ^ 2 ≠ 1 := by decide +kernel

theorem fx₂_pow : fx₂ ^ 4 = 1 ∧ fx₂ ^ 2 ≠ 1 := by decide +kernel

theorem fx₁_fx₂_comm : fx₁ * fx₂ = fx₂ * fx₁ := by decide +kernel

theorem fx₁_sq_ne : fx₁ ^ 2 ≠ fx₂ ^ 2 := by decide +kernel

theorem flam_pow : flam ^ 2 = 1 ∧ flam ≠ 1 := by decide +kernel

theorem flam_conj : flam * fx₁ * flam⁻¹ = fx₂ := by decide +kernel

theorem wreathRel_frame : WreathRel fx₁ fx₂ flam :=
  WreathRel.of_pow fx₁_pow.1 fx₁_pow.2 fx₂_pow.1 fx₂_pow.2 fx₁_fx₂_comm fx₁_sq_ne flam_pow.1
    flam_pow.2 flam_conj

theorem ftau_pow : ftau ^ 2 = 1 ∧ ftau ≠ 1 := by decide +kernel

theorem ftau_flam : flam * ftau = ftau * flam := by decide +kernel

theorem ftau_x₁ : ftau * fx₁ * ftau⁻¹ = fx₁⁻¹ := by decide +kernel

theorem ftau_x₂ : ftau * fx₂ * ftau⁻¹ = fx₂⁻¹ := by decide +kernel

theorem m12Rel_frame : M12Rel fx₁ fx₂ flam ftau :=
  M12Rel.of_pow wreathRel_frame ftau_pow.1 ftau_pow.2 ftau_flam ftau_x₁ ftau_x₂

theorem frho_pow : frho ^ 3 = 1 ∧ frho ≠ 1 := by decide +kernel

theorem frho_ord : orderOf frho = 3 := orderOf_eq_prime frho_pow.1 frho_pow.2

theorem frho_x₁ : frho * fx₁ * frho⁻¹ = fx₁⁻¹ * fx₂ := by decide +kernel

theorem frho_x₂ : frho * fx₂ * frho⁻¹ = fx₁⁻¹ := by decide +kernel

theorem flam_frho : flam * frho * flam⁻¹ = frho⁻¹ := by decide +kernel

theorem ftau_frho : ftau * frho = frho * ftau := by decide +kernel

theorem frho_cent_base : ∀ a b : Fin 4,
    frho * (fx₁ ^ a.val * fx₂ ^ b.val) = (fx₁ ^ a.val * fx₂ ^ b.val) * frho → a = 0 ∧ b = 0 := by
  decide +kernel

theorem fy_def : fy = fx₁ ^ 2 := rfl

theorem fz_eq : fz = fx₁ ^ 2 * fx₂ ^ 2 ∧ fx₂ ^ 2 = fy * fz := by decide +kernel

theorem fg3_pow : fg3 ^ 3 = 1 ∧ fg3 ≠ 1 ∧ fg3 * fz = fz * fg3 := by decide +kernel

section Membership

theorem fx₁_mem : fx₁ ∈ QP.originalSubgroup :=
  (mem_iff_sift QP QP_ok _).2 (by decide +kernel)

theorem fx₂_mem : fx₂ ∈ QP.originalSubgroup :=
  (mem_iff_sift QP QP_ok _).2 (by decide +kernel)

theorem flam_mem : flam ∈ QP.originalSubgroup :=
  (mem_iff_sift QP QP_ok _).2 (by decide +kernel)

theorem frho_mem : frho ∈ QP.originalSubgroup :=
  (mem_iff_sift QP QP_ok _).2 (by decide +kernel)

theorem fk0_mem : fk0 ∈ QP.originalSubgroup :=
  (mem_iff_sift QP QP_ok _).2 (by decide +kernel)

theorem fg3_mem : fg3 ∈ QP.originalSubgroup :=
  (mem_iff_sift QP QP_ok _).2 (by decide +kernel)

theorem ftau_mem_A : ftau ∈ QA.originalSubgroup :=
  (mem_iff_sift QA QA_ok _).2 (by decide +kernel)

theorem ftau_not_mem_P : ftau ∉ QP.originalSubgroup := fun h =>
  absurd ((mem_iff_sift QP QP_ok _).1 h) (by decide +kernel)

end Membership

end CFSG.OddStandard.SmallF3.HarrisU33.K28
