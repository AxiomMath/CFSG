module

public import CFSG.CharacterTheory.Semidihedral.MatrixTorus

public section

namespace CFSG.GH74.GLS.IVK.L2Torus

open Matrix CFSG.Semidihedral.MatrixTorus CFSG.Semidihedral.MatrixCoverData
  CFSG.Semidihedral.OddFieldSL2

variable {F : Type*} [Field F]

theorem sq_entries (x : SL F) (hx : x * x = minusIdentity F) :
    x.1 0 0 * x.1 0 0 + x.1 0 1 * x.1 1 0 = -1 ∧ x.1 0 0 * x.1 0 1 + x.1 0 1 * x.1 1 1 = 0 ∧
    x.1 1 0 * x.1 0 0 + x.1 1 1 * x.1 1 0 = 0 ∧ x.1 1 0 * x.1 0 1 + x.1 1 1 * x.1 1 1 = -1 := by
  have h := fun i j => congrArg (fun y : SL F => (y : Matrix (Fin 2) (Fin 2) F) i j) hx
  have h00 := h 0 0
  have h01 := h 0 1
  have h10 := h 1 0
  have h11 := h 1 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, minusIdentity_matrix] at h00 h01 h10 h11
  exact ⟨h00, h01, h10, h11⟩

theorem trace_eq_zero (h2 : (2 : F) ≠ 0) (x : SL F) (hx : x * x = minusIdentity F) :
    x.1 1 1 = -x.1 0 0 := by
  obtain ⟨e00, e01, e10, e11⟩ := sq_entries x hx
  have hdet := x.2
  rw [Matrix.det_fin_two] at hdet
  by_contra hne
  have hs : x.1 0 0 + x.1 1 1 ≠ 0 := fun h => hne (by linear_combination h)
  have hb : x.1 0 1 = 0 := by
    have : x.1 0 1 * (x.1 0 0 + x.1 1 1) = 0 := by linear_combination e01
    exact (mul_eq_zero.1 this).resolve_right hs
  have hc : x.1 1 0 = 0 := by
    have : x.1 1 0 * (x.1 0 0 + x.1 1 1) = 0 := by linear_combination e10
    exact (mul_eq_zero.1 this).resolve_right hs
  rw [hb, hc] at e00 e11 hdet
  have had : x.1 0 0 = x.1 1 1 := by
    have : (x.1 0 0 - x.1 1 1) * (x.1 0 0 + x.1 1 1) = 0 := by linear_combination e00 - e11
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hs)
  apply h2
  rw [← had] at hdet
  linear_combination e00 - hdet

theorem exists_vec_det_ne_zero (h2 : (2 : F) ≠ 0) (x : SL F) (hx : x * x = minusIdentity F) :
    ∃ v : Fin 2 → F, v 0 * (x.1 *ᵥ v) 1 - (x.1 *ᵥ v) 0 * v 1 ≠ 0 := by
  obtain ⟨e00, e01, e10, e11⟩ := sq_entries x hx
  have htr := trace_eq_zero h2 x hx
  by_cases hc : x.1 1 0 = 0
  · by_cases hb : x.1 0 1 = 0
    · refine ⟨![1, 1], ?_⟩
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hb, hc, htr]
      intro h
      have ha : x.1 0 0 = 0 := by
        have : (2 : F) * x.1 0 0 = 0 := by linear_combination -h
        exact (mul_eq_zero.1 this).resolve_left h2
      rw [ha, hb, hc] at e00
      simp at e00
    · refine ⟨![0, 1], ?_⟩
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hb]
  · refine ⟨![1, 0], ?_⟩
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hc]

theorem exists_conj_J (h2 : (2 : F) ≠ 0) (x : SL F) (hx : x * x = minusIdentity F) :
    ∃ P : GL2 F, SpecialLinearGroup.toGL x = P * J F 1 * P⁻¹ := by
  obtain ⟨v, hv⟩ := exists_vec_det_ne_zero h2 x hx
  obtain ⟨e00, e01, e10, e11⟩ := sq_entries x hx
  let M : Matrix (Fin 2) (Fin 2) F := !![v 0, (x.1 *ᵥ v) 0; v 1, (x.1 *ᵥ v) 1]
  have hM : M.det ≠ 0 := by simpa [M, Matrix.det_fin_two_of] using hv
  refine ⟨GeneralLinearGroup.mkOfDetNeZero M hM, ?_⟩
  rw [eq_mul_inv_iff_mul_eq]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [M, J_matrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mulVec, dotProduct]
  · linear_combination v 0 * e00 + v 1 * e01
  · linear_combination v 0 * e10 + v 1 * e11

theorem centralizer_eq_map_torus (x : SL F) (P : GL2 F)
    (hP : SpecialLinearGroup.toGL x = P * J F 1 * P⁻¹) :
    Subgroup.centralizer ({x} : Set (SL F)) =
      (Torus F 1).map (slConjugation F P).toMonoidHom := by
  ext y
  rw [Subgroup.mem_map_equiv]
  obtain ⟨y', rfl⟩ := (slConjugation F P).surjective y
  rw [MulEquiv.symm_apply_apply, Subgroup.mem_centralizer_singleton_iff]
  have hTorus : y' ∈ Torus F 1 ↔
      SpecialLinearGroup.toGL y' * J F 1 = J F 1 * SpecialLinearGroup.toGL y' := by
    change SpecialLinearGroup.toGL y' ∈ Subgroup.centralizer {J F 1} ↔ _
    rw [Subgroup.mem_centralizer_singleton_iff]
  rw [hTorus, ← SpecialLinearGroup.toGL_injective.eq_iff, map_mul, map_mul, hP]
  have hc : SpecialLinearGroup.toGL ((slConjugation F P : MulAut (SL F)) y') =
      P * SpecialLinearGroup.toGL y' * P⁻¹ := slConjugation_toGL F P y'
  rw [hc]
  have e1 : P * SpecialLinearGroup.toGL y' * P⁻¹ * (P * J F 1 * P⁻¹) =
      P * (SpecialLinearGroup.toGL y' * J F 1) * P⁻¹ := by group
  have e2 : P * J F 1 * P⁻¹ * (P * SpecialLinearGroup.toGL y' * P⁻¹) =
      P * (J F 1 * SpecialLinearGroup.toGL y') * P⁻¹ := by group
  rw [e1, e2, mul_left_inj, mul_right_inj]

theorem centralizer_cyclic_card [Finite F] (hodd : Odd (Nat.card F)) (x : SL F)
    (hx : x * x = minusIdentity F) :
    IsCyclic ↥(Subgroup.centralizer ({x} : Set (SL F))) ∧
      (IsSquare (-1 : F) → Nat.card ↥(Subgroup.centralizer ({x} : Set (SL F))) = Nat.card F - 1) ∧
      (¬ IsSquare (-1 : F) →
        Nat.card ↥(Subgroup.centralizer ({x} : Set (SL F))) = Nat.card F + 1) := by
  have h2 := two_ne_zero_of_odd_card F hodd
  obtain ⟨P, hP⟩ := exists_conj_J h2 x hx
  rw [centralizer_eq_map_torus x P hP]
  set c : SL F →* SL F := (slConjugation F P).toMonoidHom
  have hinj : Function.Injective c := (slConjugation F P).injective
  have e := Subgroup.equivMapOfInjective (Torus F 1) c hinj
  have hcard : Nat.card ((Torus F 1).map c) = Nat.card (Torus F 1) :=
    Subgroup.card_map_of_injective hinj
  refine ⟨?_, fun hs => ?_, fun hs => ?_⟩
  · by_cases hs : IsSquare (-1 : F)
    · have := split_torus_cyclic F 1 h2 (by simpa using hs)
      exact e.isCyclic.1 this
    · have := nonsplit_torus_cyclic F 1 (by simpa using hs)
      exact e.isCyclic.1 this
  · rw [hcard]
    exact split_torus_card F 1 h2 (by simpa using hs)
  · rw [hcard]
    exact nonsplit_torus_card F 1 (by simpa using hs)

end CFSG.GH74.GLS.IVK.L2Torus
