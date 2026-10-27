module

public import CFSG.CGT.Stroth77.Stroth35T300
public import CFSG.CGT.Stroth77.Stroth3Transfer

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsSylowIn)

namespace Type320

theorem t320_k (m : ℕ) (hm : 3 ≤ m) (i : Fin 3) : (StrothTypeIndex.t320 m hm).k i = m := by
  fin_cases i <;> rfl

@[expose] def psiM : IntMat := !![3, -8, 0; 0, -1, 2; 0, -2, 1]

@[expose] def psiAdj : IntMat := !![3, 8, -16; 0, 3, -6; 0, 6, -3]

attribute [local simp] Type320.ρM Type320.uvA Type320.tM Type320.uvM Type300.ρM Type300.uvA
  Type300.tM Type300.uvM psiM psiAdj ofCols_apply Matrix.mul_apply Fin.sum_univ_three
  Matrix.mulVec dotProduct Matrix.one_apply

theorem psi_uv {m : ℕ} {i F G N : ℤ} (h : Type32x.Data m i F G N) :
    MatEq (Type32x.k m) (psiM * Type320.uvM i F G) (Type300.uvM * psiM) := by
  obtain ⟨hm, hi, hF, hG, hN⟩ := h
  have hs := Type32x.dvd_three_mul_add_seven ⟨hm, hi, hF, hG, hN⟩
  subst hi
  subst hF
  refine MatEq.of_dvd (3 * G + 7) hs (P := !![-8, 128 * G + 400, -1536 * G ^ 2 - 4480 * G - 1880;
    0, 24, 768 * G + 1856; 0, 32, 1344 * G + 3232]) ?_
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1

theorem psi_t {m : ℕ} {i F G N : ℤ} (h : Type32x.Data m i F G N) :
    MatEq (Type32x.k m) (psiM * Type320.tM i F G) (Type300.tM * psiM) := by
  obtain ⟨hm, hi, hF, hG, hN⟩ := h
  have hs := Type32x.dvd_three_mul_add_seven ⟨hm, hi, hF, hG, hN⟩
  subst hi
  subst hF
  refine MatEq.of_dvd (3 * G + 7) hs (P := !![-8, 64 * G + 152, 128 * G + 272; 0, -24, -32;
    0, 16, -8]) ?_
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1

theorem psi_ρ (m : ℕ) : MatEq (Type32x.k m) (psiM * Type320.ρM) (Type300.ρM * psiM) := by
  refine MatEq.of_witness (W := 0) ?_
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]

theorem psiAdj_mul (m : ℕ) :
    MatEq (StrothTypeIndex.t300 m).k (psiAdj * psiM) ((9 : ℤ) • (1 : IntMat)) := by
  refine MatEq.of_witness (W := 0) ?_
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]

@[expose] noncomputable def psi (m : ℕ) (hm : 3 ≤ m) :
    Torus (StrothTypeIndex.t320 m hm).k ≃+ Torus (StrothTypeIndex.t300 m).k :=
  torusEquivOfMat psiM psiAdj (Type300.compat_const m _) (Type300.compat_const m _)
    (d := 9) ⟨4, by norm_num⟩ (psiAdj_mul m)

theorem psi_φuv {m : ℕ} (hm : 3 ≤ m) (x : Torus (StrothTypeIndex.t320 m hm).k) :
    psi m hm ((StrothTypeIndex.t320 m hm).action.φuv x) =
      (StrothTypeIndex.t300 m).action.φuv (psi m hm x) :=
  matAct_intertwine (Type300.compat_const m _) (Type300.compat_const m _)
    (StrothTypeIndex.t300 m).action.compat_uv (psi_uv (Type32x.data m (by omega))) x

theorem psi_φt {m : ℕ} (hm : 3 ≤ m) (x : Torus (StrothTypeIndex.t320 m hm).k) :
    psi m hm ((StrothTypeIndex.t320 m hm).action.φt x) =
      (StrothTypeIndex.t300 m).action.φt (psi m hm x) :=
  matAct_intertwine (Type300.compat_const m _) (Type300.compat_const m _)
    (StrothTypeIndex.t300 m).action.compat_t (psi_t (Type32x.data m (by omega))) x

theorem psi_φρ {m : ℕ} (hm : 3 ≤ m) (x : Torus (StrothTypeIndex.t320 m hm).k) :
    psi m hm ((StrothTypeIndex.t320 m hm).action.φρ x) =
      (StrothTypeIndex.t300 m).action.φρ (psi m hm x) :=
  matAct_intertwine (Type300.compat_const m _) (Type300.compat_const m _)
    (StrothTypeIndex.t300 m).action.compat_ρ (psi_ρ m) x

theorem psiM_row : Odd (psiM 0 0) ∧ Even (psiM 0 1) ∧ Even (psiM 0 2) :=
  ⟨⟨1, by simp [psiM]⟩, ⟨-4, by simp [psiM]⟩, by simp [psiM]⟩

theorem psi_val_mod_two {m : ℕ} (hm : 3 ≤ m) (x : Torus (StrothTypeIndex.t320 m hm).k) :
    ((psi m hm x) 0).val % 2 = (x 0).val % 2 :=
  matAct_val_zero_mod_two (k := (StrothTypeIndex.t300 m).k) (by show 1 ≤ m; omega)
    psiM (Type300.compat_const m _) psiM_row.1 psiM_row.2.1 psiM_row.2.2 x

theorem psi_zero {m : ℕ} (hm : 3 ≤ m) (x : Torus (StrothTypeIndex.t320 m hm).k) (hx : x + x = 0) :
    (psi m hm x) 0 = 0 ↔ x 0 = 0 :=
  matAct_apply_zero_eq_zero_iff (k := (StrothTypeIndex.t300 m).k) (fun i => by fin_cases i <;> rfl)
    psiM (Type300.compat_const m _) psiM_row.1 psiM_row.2.1 psiM_row.2.2 hx

theorem uM_row {m : ℕ} (hm : 3 ≤ m) : Odd ((StrothTypeIndex.t320 m hm).action.u 0 0) ∧
    Even ((StrothTypeIndex.t320 m hm).action.u 0 1) ∧
    Even ((StrothTypeIndex.t320 m hm).action.u 0 2) := by
  show Odd (Type320.uM (Type120.FV m) 0 0) ∧ Even (Type320.uM (Type120.FV m) 0 1) ∧
    Even (Type320.uM (Type120.FV m) 0 2)
  refine ⟨⟨-1, ?_⟩, ⟨-4 * Type120.FV m, ?_⟩, ⟨-4 * Type120.FV m, ?_⟩⟩ <;>
    simp [Type320.uM, uMat] <;> ring

theorem par_u {m : ℕ} (hm : 3 ≤ m) (x : Torus (StrothTypeIndex.t320 m hm).k) :
    (((StrothTypeIndex.t320 m hm).action.φu x) 0).val % 2 = (x 0).val % 2 :=
  matAct_val_zero_mod_two (by rw [t320_k]; omega) _ _ (uM_row hm).1 (uM_row hm).2.1
    (uM_row hm).2.2 x

theorem W_u {m : ℕ} (hm : 3 ≤ m) (w : Torus (StrothTypeIndex.t320 m hm).k) (hw : InW w) :
    ((StrothTypeIndex.t320 m hm).action.φu w) 0 = 0 :=
  (matAct_apply_zero_eq_zero_iff (fun i => by rw [t320_k, t320_k]) _ _ (uM_row hm).1
    (uM_row hm).2.1 (uM_row hm).2.2 hw.2).mpr hw.1

theorem vFacts (m : ℕ) (hm : 3 ≤ m) : VFacts (StrothTypeIndex.t320 m hm) :=
  VFacts.of_equiv (psi m hm) (Type300.vFacts (by omega)) (psi_φuv hm) (psi_φt hm) (psi_φρ hm)
    (psi_val_mod_two hm) (psi_zero hm) (by rw [t320_k]; omega) (par_u hm) (W_u hm)

theorem killFact (m : ℕ) (hm : 3 ≤ m) : KillFact (StrothTypeIndex.t320 m hm) :=
  KillFact.of_equiv (psi m hm) Type300.killFact (psi_φuv hm) (psi_φt hm) (psi_φρ hm) (psi_zero hm)

end Type320

theorem StrothFrame.IsD.stroth_3_7 {G : Type} [Group G] [Finite G] {F : StrothFrame G}
    {D : Subgroup G} {m : ℕ} {hm : 3 ≤ m} {dD : StrothWeakTypeData D (StrothTypeIndex.t320 m hm)}
    (h : F.IsD D dD)
    (hns : IsSylowIn 2 (Subgroup.normalizer (D : Set G))
      ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G))) :
    (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ∨
      ∃ X : Subgroup G, IsMulCommutative X ∧ F.A ≤ X ∧ X ≤ (F.S : Subgroup G) ∧
        F.dA.L ≤ Subgroup.normalizer
          ((X ⊔ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) ∧
        Nat.card D < Nat.card X :=
  h.stroth_form_ii (Type320.vFacts m hm) (Type320.killFact m hm) hns

end CFSG.CGT.Stroth77
