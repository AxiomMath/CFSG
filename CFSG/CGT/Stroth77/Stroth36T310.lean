module

public import CFSG.CGT.Stroth77.Stroth35T300
public import CFSG.CGT.Stroth77.Stroth3Transfer

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsSylowIn)
open Stroth42Core

namespace Type310

theorem t310_k (m : ℕ) (hm : 2 ≤ m) (i : Fin 3) : (StrothTypeIndex.t310 m hm).k i = m := by
  fin_cases i <;> rfl

@[expose] def psiM (m : ℕ) : IntMat :=
  !![1 + 2 * 2 ^ (m - 2), 0, 0; 0, 1 + 2 * 2 ^ (m - 2), 2 * 2 ^ (m - 2); 0, 2 * 2 ^ (m - 2), 1]

attribute [local simp] Type310.ρM Type310.uvA Type310.tM Type310.uvM Type300.ρM Type300.uvA
  Type300.tM Type300.uvM psiM ofCols_apply Matrix.mul_apply Fin.sum_univ_three Matrix.mulVec
  dotProduct Matrix.one_apply t300_k Nat.add_sub_cancel

theorem psi_uv {m : ℕ} (hm : 2 ≤ m) :
    MatEq (StrothTypeIndex.t300 m).k (psiM m * Type310.uvM m) (Type300.uvM * psiM m) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, by omega⟩
  refine MatEq.of_witness
    (W := !![0, -2, -16 * 2 ^ s - 8; 2 ^ s, 0, -8 * 2 ^ s - 1; 2 ^ s, -1, -4 * 2 ^ s - 2]) ?_
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1

theorem psi_t {m : ℕ} (hm : 2 ≤ m) :
    MatEq (StrothTypeIndex.t300 m).k (psiM m * Type310.tM m) (Type300.tM * psiM m) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, by omega⟩
  refine MatEq.of_witness (W := !![0, 2, -2; 2 ^ s, 1, -1; 1, 0, -1]) ?_
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1

theorem psi_ρ {m : ℕ} (hm : 2 ≤ m) :
    MatEq (StrothTypeIndex.t300 m).k (psiM m * Type310.ρM) (Type300.ρM * psiM m) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, by omega⟩
  refine MatEq.of_witness (W := !![0, 2, -2; 0, 1, -1; 0, 0, -1]) ?_
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1

theorem psi_sq {m : ℕ} (hm : 2 ≤ m) :
    MatEq (StrothTypeIndex.t300 m).k (psiM m * psiM m) ((1 : ℤ) • (1 : IntMat)) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, by omega⟩
  refine MatEq.of_witness
    (W := !![1 + 2 ^ s, 0, 0; 0, 1 + 2 * 2 ^ s, 1 + 2 ^ s; 0, 1 + 2 ^ s, 2 ^ s]) ?_
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1

@[expose] noncomputable def psi (m : ℕ) (hm : 2 ≤ m) :
    Torus (StrothTypeIndex.t310 m hm).k ≃+ Torus (StrothTypeIndex.t300 m).k :=
  torusEquivOfMat (psiM m) (psiM m) (Type300.compat_const m _) (Type300.compat_const m _) odd_one
    (psi_sq hm)

theorem psi_φuv {m : ℕ} (hm : 2 ≤ m) (x : Torus (StrothTypeIndex.t310 m hm).k) :
    psi m hm ((StrothTypeIndex.t310 m hm).action.φuv x) =
      (StrothTypeIndex.t300 m).action.φuv (psi m hm x) :=
  matAct_intertwine (Type300.compat_const m _) (Type300.compat_const m _)
    (StrothTypeIndex.t300 m).action.compat_uv (psi_uv hm) x

theorem psi_φt {m : ℕ} (hm : 2 ≤ m) (x : Torus (StrothTypeIndex.t310 m hm).k) :
    psi m hm ((StrothTypeIndex.t310 m hm).action.φt x) =
      (StrothTypeIndex.t300 m).action.φt (psi m hm x) :=
  matAct_intertwine (Type300.compat_const m _) (Type300.compat_const m _)
    (StrothTypeIndex.t300 m).action.compat_t (psi_t hm) x

theorem psi_φρ {m : ℕ} (hm : 2 ≤ m) (x : Torus (StrothTypeIndex.t310 m hm).k) :
    psi m hm ((StrothTypeIndex.t310 m hm).action.φρ x) =
      (StrothTypeIndex.t300 m).action.φρ (psi m hm x) :=
  matAct_intertwine (Type300.compat_const m _) (Type300.compat_const m _)
    (StrothTypeIndex.t300 m).action.compat_ρ (psi_ρ hm) x

theorem psiM_row {m : ℕ} : Odd (psiM m 0 0) ∧ Even (psiM m 0 1) ∧ Even (psiM m 0 2) :=
  ⟨⟨2 ^ (m - 2), by simp [psiM]; ring⟩, by simp [psiM], by simp [psiM]⟩

theorem psi_val_mod_two {m : ℕ} (hm : 2 ≤ m) (x : Torus (StrothTypeIndex.t310 m hm).k) :
    ((psi m hm x) 0).val % 2 = (x 0).val % 2 :=
  matAct_val_zero_mod_two (k := (StrothTypeIndex.t300 m).k) (by rw [t300_k]; omega) (psiM m)
    (Type300.compat_const m _) psiM_row.1 psiM_row.2.1 psiM_row.2.2 x

theorem psi_zero {m : ℕ} (hm : 2 ≤ m) (x : Torus (StrothTypeIndex.t310 m hm).k) (hx : x + x = 0) :
    (psi m hm x) 0 = 0 ↔ x 0 = 0 :=
  matAct_apply_zero_eq_zero_iff (k := (StrothTypeIndex.t300 m).k) (fun i => by rw [t300_k, t300_k])
    (psiM m) (Type300.compat_const m _) psiM_row.1 psiM_row.2.1 psiM_row.2.2 hx

theorem uM_row {m : ℕ} (hm : 2 ≤ m) : Odd ((StrothTypeIndex.t310 m hm).action.u 0 0) ∧
    Even ((StrothTypeIndex.t310 m hm).action.u 0 1) ∧
    Even ((StrothTypeIndex.t310 m hm).action.u 0 2) := by
  show Odd (Type310.uM m 0 0) ∧ Even (Type310.uM m 0 1) ∧ Even (Type310.uM m 0 2)
  refine ⟨⟨2 ^ (m - 2), ?_⟩, ?_, ?_⟩ <;> simp [Type310.uM, uMat] <;> ring

theorem par_u {m : ℕ} (hm : 2 ≤ m) (x : Torus (StrothTypeIndex.t310 m hm).k) :
    (((StrothTypeIndex.t310 m hm).action.φu x) 0).val % 2 = (x 0).val % 2 :=
  matAct_val_zero_mod_two (by rw [t310_k]; omega) _ _ (uM_row hm).1 (uM_row hm).2.1
    (uM_row hm).2.2 x

theorem W_u {m : ℕ} (hm : 2 ≤ m) (w : Torus (StrothTypeIndex.t310 m hm).k) (hw : InW w) :
    ((StrothTypeIndex.t310 m hm).action.φu w) 0 = 0 :=
  (matAct_apply_zero_eq_zero_iff (fun i => by rw [t310_k, t310_k]) _ _ (uM_row hm).1
    (uM_row hm).2.1 (uM_row hm).2.2 hw.2).mpr hw.1

theorem vFacts (m : ℕ) (hm : 2 ≤ m) : VFacts (StrothTypeIndex.t310 m hm) :=
  VFacts.of_equiv (psi m hm) (Type300.vFacts hm) (psi_φuv hm) (psi_φt hm) (psi_φρ hm)
    (psi_val_mod_two hm) (psi_zero hm) (by rw [t310_k]; exact hm) (par_u hm) (W_u hm)

theorem killFact (m : ℕ) (hm : 2 ≤ m) : KillFact (StrothTypeIndex.t310 m hm) :=
  KillFact.of_equiv (psi m hm) Type300.killFact (psi_φuv hm) (psi_φt hm) (psi_φρ hm) (psi_zero hm)

end Type310

theorem StrothFrame.IsD.stroth_3_6 {G : Type} [Group G] [Finite G] {F : StrothFrame G}
    {D : Subgroup G} {m : ℕ} {hm : 2 ≤ m} {dD : StrothWeakTypeData D (StrothTypeIndex.t310 m hm)}
    (h : F.IsD D dD)
    (hns : IsSylowIn 2 (Subgroup.normalizer (D : Set G))
      ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G))) :
    (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ∨
      ∃ X : Subgroup G, IsMulCommutative X ∧ F.A ≤ X ∧ X ≤ (F.S : Subgroup G) ∧
        F.dA.L ≤ Subgroup.normalizer
          ((X ⊔ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) ∧
        Nat.card D < Nat.card X :=
  h.stroth_form_ii (Type310.vFacts m hm) (Type310.killFact m hm) hns

end CFSG.CGT.Stroth77
