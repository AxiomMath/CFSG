module

public import CFSG.Adapters.TauCetiExceptional.ReePoly
public import CFSG.Adapters.TauCetiExceptional.ReeVanish
public import CFSG.Adapters.TauCetiExceptional.BigCellPoints
public import Certificates.Certificate113
public import Certificates.Certificate114
public import CFSG.Adapters.TauCetiExceptional.ReeAdHom

public noncomputable section

namespace CFSG.TauCetiBridge.Ree

open CFSG.Blueprint.Chevalley CFSG.Quasithin.G2U CFSG.TauCetiBridge.BigCell TauCeti

variable {A : Type*} [CommRing A]

theorem tcE_inl_upper_aux (i : Fin 2) : ∀ p : Fin 7 × Fin 7, p.2 ≤ p.1 →
    tcE (.inl i) p.1 p.2 = 0 ∧ tcE2 (.inl i) p.1 p.2 = 0 := by
  fin_cases i <;> decide

theorem tcE_inr_lower_aux (i : Fin 2) : ∀ p : Fin 7 × Fin 7, p.1 ≤ p.2 →
    tcE (.inr i) p.1 p.2 = 0 ∧ tcE2 (.inr i) p.1 p.2 = 0 := by
  fin_cases i <;> decide

theorem tcE_inl_upper (i : Fin 2) (a b : Fin 7) (h : b ≤ a) :
    tcE (.inl i) a b = 0 ∧ tcE2 (.inl i) a b = 0 :=
  tcE_inl_upper_aux i (a, b) h

theorem tcE_inr_lower (i : Fin 2) (a b : Fin 7) (h : a ≤ b) :
    tcE (.inr i) a b = 0 ∧ tcE2 (.inr i) a b = 0 :=
  tcE_inr_lower_aux i (a, b) h

theorem det_rootPointMat (k : Fin 2 ⊕ Fin 2) (t : A) : (rootPointMat k t).det = 1 := by
  rw [rootPointMat_eq]
  rcases k with i | i
  · rw [Matrix.det_of_isUpperTriangular]
    · refine Finset.prod_eq_one fun a _ => ?_
      simp [(tcE_inl_upper i a a le_rfl).1, (tcE_inl_upper i a a le_rfl).2]
    · intro a b hba
      have hba' : b < a := hba
      simp [Matrix.one_apply_ne (ne_of_lt hba').symm, (tcE_inl_upper i a b hba'.le).1,
        (tcE_inl_upper i a b hba'.le).2]
  · rw [Matrix.det_of_isLowerTriangular]
    · refine Finset.prod_eq_one fun a _ => ?_
      simp [(tcE_inr_lower i a a le_rfl).1, (tcE_inr_lower i a a le_rfl).2]
    · intro a b hba
      have hab : a < b := hba
      simp [Matrix.one_apply_ne (ne_of_lt hab), (tcE_inr_lower i a b hab.le).1,
        (tcE_inr_lower i a b hab.le).2]

theorem det_eq_one_of_mem_ratRootGroup {s : Matrix.GeneralLinearGroup (Fin 7) ℚ}
    (hs : s ∈ ratRootGroup) : (s : Matrix (Fin 7) (Fin 7) ℚ).det = 1 := by
  have hle : ratRootGroup ≤ (Matrix.GeneralLinearGroup.det :
      Matrix.GeneralLinearGroup (Fin 7) ℚ →* ℚˣ).ker := by
    rw [ratRootGroup, Subgroup.closure_le]
    rintro _ ⟨k, t, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
    exact det_rootPointMat k t
  have h := MonoidHom.mem_ker.1 (hle hs)
  rw [Units.ext_iff, Matrix.GeneralLinearGroup.val_det_apply] at h
  exact h

theorem ratRootGroup_le_normGroup : ratRootGroup ≤ normGroup ℚ := by
  rw [ratRootGroup, Subgroup.closure_le]
  rintro _ ⟨k, t, rfl⟩
  exact rootPoint_mem_normGroup k t

theorem adUnits_mem_adjointGroup
    {s : Matrix.GeneralLinearGroup (Fin 7) ℚ}
    (hs : s ∈ ratRootGroup) :
    adUnits ℚ ⟨s, ratRootGroup_le_normGroup hs⟩ ∈ adjointGroup .G2 ℚ := by
  have hle : ratRootGroup ≤ ((adjointGroup .G2 ℚ).comap (adUnits ℚ)).map
      (normGroup ℚ).subtype := by
    rw [ratRootGroup, Subgroup.closure_le]
    rintro _ ⟨k, t, rfl⟩
    refine ⟨⟨rootPoint k t, rootPoint_mem_normGroup k t⟩, ?_, rfl⟩
    change adUnits ℚ ⟨rootPoint k t, rootPoint_mem_normGroup k t⟩ ∈ adjointGroup .G2 ℚ
    rcases k with i | i
    · have e : adUnits ℚ ⟨rootPoint (.inl i) t, rootPoint_mem_normGroup _ t⟩ =
          xUnit .G2 ℚ (nodeMap i) t := Units.ext (by rw [coe_adUnits, adConj_rootPoint_inl]; rfl)
      rw [e]
      exact xUnit_mem_adjointGroup _ _
    · have e : adUnits ℚ ⟨rootPoint (.inr i) t, rootPoint_mem_normGroup _ t⟩ =
          yUnit .G2 ℚ (nodeMap i) t := Units.ext (by rw [coe_adUnits, adConj_rootPoint_inr]; rfl)
      rw [e]
      exact yUnit_mem_adjointGroup _ _
  obtain ⟨n, hn, hns⟩ := hle hs
  have e : n = ⟨s, ratRootGroup_le_normGroup hs⟩ := Subtype.ext hns
  rw [← e]
  exact hn

theorem evalMat_detPoly_ratRootGroup (s : Matrix.GeneralLinearGroup (Fin 7) ℚ)
    (hs : s ∈ ratRootGroup) : evalMat (s : Matrix (Fin 7) (Fin 7) ℚ) detPoly = 0 := by
  rw [evalMat_detPoly, det_eq_one_of_mem_ratRootGroup hs, sub_self]

theorem evalMat_normPoly_ratRootGroup (t : Fin 14) (r c : Fin 7)
    (s : Matrix.GeneralLinearGroup (Fin 7) ℚ) (hs : s ∈ ratRootGroup) :
    evalMat (s : Matrix (Fin 7) (Fin 7) ℚ) (normPoly t r c) = 0 := by
  rw [evalMat_normPoly, adjugate_eq_inv_of_det_eq_one s (det_eq_one_of_mem_ratRootGroup hs),
    ← ((ratRootGroup_le_normGroup hs t).1).eq_sum, sub_self, Matrix.zero_apply]

theorem evalMat_adPoly_ratRootGroup
    (P : MvPolynomial (Fin (nLab .G2) × Fin (nLab .G2)) ℤ)
    (hP : VanishesOnRat .G2 P) (s : Matrix.GeneralLinearGroup (Fin 7) ℚ)
    (hs : s ∈ ratRootGroup) : evalMat (s : Matrix (Fin 7) (Fin 7) ℚ) (adPoly P) = 0 := by
  rw [evalMat_adPoly, adjugate_eq_inv_of_det_eq_one s (det_eq_one_of_mem_ratRootGroup hs)]
  have h := hP _ (adUnits_mem_adjointGroup hs)
  rwa [coe_adUnits] at h

end CFSG.TauCetiBridge.Ree
