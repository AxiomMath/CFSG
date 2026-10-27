module

public import CFSG.CGT.Stroth77.Stroth35T300
public import CFSG.CGT.Stroth77.Stroth3Transfer

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsSylowIn)

namespace Type330

theorem t330_k (m : ℕ) (hm : 3 ≤ m) (i : Fin 3) : (StrothTypeIndex.t330 m hm).k i = m := by
  fin_cases i <;> rfl

@[expose] def psiM (N : ℤ) : IntMat := !![3 + N, -8, 0; 0, -1 + N, 2 + N; 0, -2 + N, 1]

@[expose] def psiAdj (N : ℤ) : IntMat :=
  !![-N ^ 2 + N + 3, 8, -8 * N - 16; 0, N + 3, -N ^ 2 - 5 * N - 6; 0, -N ^ 2 - N + 6,
    N ^ 2 + 2 * N - 3]

@[expose] def psiDet (N : ℤ) : ℤ := -(N + 3) * (N ^ 2 - N - 3)

theorem data_arith {m : ℕ} {i F G N : ℤ} (h : Type32x.Data m i F G N) :
    ∃ n : ℤ, N = 2 * n ∧ 3 * G + 7 = 4 * n * n ∧
      (∀ r : Fin 3, (2 : ℤ) ^ Type32x.k m r = 4 * n) ∧ i = 8 * G + 19 ∧ F = 4 * G + 9 := by
  obtain ⟨hm, hi, hF, hG, hN⟩ := h
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  have hsub : s + 2 - 1 = s + 1 := rfl
  refine ⟨2 ^ s, ?_, ?_, fun r => ?_, hi, hF⟩
  · rw [hN, hsub, pow_succ]
    ring
  · rw [hG, hN, hsub, pow_succ]
    ring
  · fin_cases r <;> simp [Type32x.k, pow_add] <;> ring

attribute [local simp] Type330.ρM Type330.uvA Type330.tM Type330.uvM Type300.ρM Type300.uvA
  Type300.tM Type300.uvM psiM psiAdj ofCols_apply Matrix.mul_apply Fin.sum_univ_three
  Matrix.mulVec dotProduct Matrix.one_apply

theorem psi_uv {m : ℕ} {i F G N : ℤ} (h : Type32x.Data m i F G N) :
    MatEq (Type32x.k m) (psiM N * Type330.uvM i F G N) (Type300.uvM * psiM N) := by
  obtain ⟨n, rfl, hG', h2m, rfl, rfl⟩ := data_arith h
  refine MatEq.of_three_pow_mul_witness (k := Type32x.k m) 2 (W :=
      !![-48*n^2 - 72*n - 24,
      1024*n^4 + 1536*n^3 - 32*n^2 + 912*n - 38,
      -16384*n^6 - 32768*n^5 - 23552*n^4 + 32512*n^3 - 656*n^2 + 1912*n - 16;
      9*n, -144*n^2 + 216*n - 18, -4096*n^5 - 14848*n^4 + 9344*n^3 - 544*n^2 + 584*n - 7;
      9*n, -240*n^2 + 288*n - 21, -2048*n^5 - 14336*n^4 + 16192*n^3 - 800*n^2 + 868*n - 20]) ?_
  intro r c
  rw [h2m r]
  fin_cases r <;> fin_cases c
  · simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    linear_combination (-48*n - 72) * hG'
  · simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    linear_combination (1024*n^3 + 1536*n^2 + 768*n*G + 1760*n + 1152*G + 3600) * hG'
  · simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    linear_combination (
      -16384*n^5 - 32768*n^4 - 12288*n^3*G - 52224*n^3 - 24576*n^2*G - 9216*n*G^2 - 24832*n^2 -
        60672*n*G - 13824*G^2 - 92048*n - 40320*G - 16920) * hG'
  · simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    ring1
  · simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    linear_combination (-144*n + 216) * hG'
  · simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    linear_combination (
      -4096*n^4 - 14848*n^3 - 3072*n^2*G + 2176*n^2 - 11136*n*G - 26528*n + 6912*G + 16704) * hG'
  · simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    ring1
  · simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    linear_combination (-240*n + 288) * hG'
  · simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    linear_combination (
      -2048*n^4 - 14336*n^3 - 1536*n^2*G + 12608*n^2 - 10752*n*G - 25888*n + 12096*G + 29088) * hG'

theorem psi_t {m : ℕ} {i F G N : ℤ} (h : Type32x.Data m i F G N) :
    MatEq (Type32x.k m) (psiM N * Type330.tM i F G N) (Type300.tM * psiM N) := by
  obtain ⟨n, rfl, hG', h2m, rfl, rfl⟩ := data_arith h
  refine MatEq.of_three_pow_mul_witness (k := Type32x.k m) 2 (W :=
      !![-48*n^2 - 72*n + 12,
      512*n^4 + 768*n^3 - 880*n^2 + 24*n - 10,
      1024*n^4 + 1536*n^3 - 416*n^2 - 240*n - 14;
      9*n + 18, -720*n^2 - 216*n - 9, -432*n^2 - 288*n - 9;
      9, -336*n^2 + 144*n - 6, -96*n^2 - 72*n - 3]) ?_
  intro r c
  rw [h2m r]
  fin_cases r <;> fin_cases c
  · simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    linear_combination (-48*n - 72) * hG'
  · simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    linear_combination (512*n^3 + 768*n^2 + 384*n*G + 16*n + 576*G + 1368) * hG'
  · simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    linear_combination (1024*n^3 + 1536*n^2 + 768*n*G + 1376*n + 1152*G + 2448) * hG'
  · simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    ring1
  · simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    linear_combination (-720*n - 216) * hG'
  · simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    linear_combination (-432*n - 288) * hG'
  · simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    ring1
  · simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    linear_combination (-336*n + 144) * hG'
  · simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    linear_combination (-96*n - 72) * hG'

theorem psi_ρ {m : ℕ} {i F G N : ℤ} (h : Type32x.Data m i F G N) :
    MatEq (Type32x.k m) (psiM N * Type330.ρM) (Type300.ρM * psiM N) := by
  obtain ⟨n, rfl, hG', h2m, rfl, rfl⟩ := data_arith h
  refine MatEq.of_three_pow_mul_witness (k := Type32x.k m) 0 (W :=
      !![0, 2, -2;
      0, 1, -1;
      0, 0, -1]) ?_
  intro r c
  rw [h2m r]
  fin_cases r <;> fin_cases c
  · simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    ring1
  · simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    ring1
  · simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    ring1
  · simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    ring1
  · simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    ring1
  · simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    ring1
  · simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    ring1
  · simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    ring1
  · simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    ring1

theorem psiAdj_mul (m : ℕ) (N : ℤ) :
    MatEq (StrothTypeIndex.t300 m).k (psiAdj N * psiM N) (psiDet N • (1 : IntMat)) := by
  refine MatEq.of_witness (W := 0) ?_
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp [psiDet, -mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1

theorem psiDet_odd {m : ℕ} (hm : 2 ≤ m) : Odd (psiDet (2 ^ (m - 1))) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, by omega⟩
  refine ⟨-4 * (2 ^ s) ^ 3 - 4 * (2 ^ s) ^ 2 + 6 * 2 ^ s + 4, ?_⟩
  rw [show s + 2 - 1 = s + 1 from rfl, pow_succ, psiDet]
  ring

@[expose] noncomputable def psi (m : ℕ) (hm : 3 ≤ m) :
    Torus (StrothTypeIndex.t330 m hm).k ≃+ Torus (StrothTypeIndex.t300 m).k :=
  torusEquivOfMat (psiM (2 ^ (m - 1))) (psiAdj (2 ^ (m - 1))) (Type300.compat_const m _)
    (Type300.compat_const m _) (psiDet_odd (by omega)) (psiAdj_mul m _)

theorem psi_φuv {m : ℕ} (hm : 3 ≤ m) (x : Torus (StrothTypeIndex.t330 m hm).k) :
    psi m hm ((StrothTypeIndex.t330 m hm).action.φuv x) =
      (StrothTypeIndex.t300 m).action.φuv (psi m hm x) :=
  matAct_intertwine (Type300.compat_const m _) (Type300.compat_const m _)
    (StrothTypeIndex.t300 m).action.compat_uv (psi_uv (Type32x.data m (by omega))) x

theorem psi_φt {m : ℕ} (hm : 3 ≤ m) (x : Torus (StrothTypeIndex.t330 m hm).k) :
    psi m hm ((StrothTypeIndex.t330 m hm).action.φt x) =
      (StrothTypeIndex.t300 m).action.φt (psi m hm x) :=
  matAct_intertwine (Type300.compat_const m _) (Type300.compat_const m _)
    (StrothTypeIndex.t300 m).action.compat_t (psi_t (Type32x.data m (by omega))) x

theorem psi_φρ {m : ℕ} (hm : 3 ≤ m) (x : Torus (StrothTypeIndex.t330 m hm).k) :
    psi m hm ((StrothTypeIndex.t330 m hm).action.φρ x) =
      (StrothTypeIndex.t300 m).action.φρ (psi m hm x) :=
  matAct_intertwine (Type300.compat_const m _) (Type300.compat_const m _)
    (StrothTypeIndex.t300 m).action.compat_ρ (psi_ρ (Type32x.data m (by omega))) x

theorem psiM_row {m : ℕ} (hm : 2 ≤ m) : Odd (psiM (2 ^ (m - 1)) 0 0) ∧
    Even (psiM (2 ^ (m - 1)) 0 1) ∧ Even (psiM (2 ^ (m - 1)) 0 2) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, by omega⟩
  refine ⟨⟨1 + 2 ^ s, ?_⟩, ⟨-4, ?_⟩, ?_⟩ <;> simp [psiM, pow_succ] <;> ring

theorem psi_val_mod_two {m : ℕ} (hm : 3 ≤ m) (x : Torus (StrothTypeIndex.t330 m hm).k) :
    ((psi m hm x) 0).val % 2 = (x 0).val % 2 :=
  matAct_val_zero_mod_two (k := (StrothTypeIndex.t300 m).k) (by show 1 ≤ m; omega)
    (psiM (2 ^ (m - 1))) (Type300.compat_const m _) (psiM_row (by omega)).1
    (psiM_row (by omega)).2.1 (psiM_row (by omega)).2.2 x

theorem psi_zero {m : ℕ} (hm : 3 ≤ m) (x : Torus (StrothTypeIndex.t330 m hm).k) (hx : x + x = 0) :
    (psi m hm x) 0 = 0 ↔ x 0 = 0 :=
  matAct_apply_zero_eq_zero_iff (k := (StrothTypeIndex.t300 m).k) (fun i => by fin_cases i <;> rfl)
    (psiM (2 ^ (m - 1))) (Type300.compat_const m _) (psiM_row (by omega)).1
    (psiM_row (by omega)).2.1 (psiM_row (by omega)).2.2 hx

theorem uM_row {m : ℕ} (hm : 3 ≤ m) : Odd ((StrothTypeIndex.t330 m hm).action.u 0 0) ∧
    Even ((StrothTypeIndex.t330 m hm).action.u 0 1) ∧
    Even ((StrothTypeIndex.t330 m hm).action.u 0 2) := by
  show Odd (Type330.uM (Type120.FV m) (2 ^ (m - 1)) 0 0) ∧
    Even (Type330.uM (Type120.FV m) (2 ^ (m - 1)) 0 1) ∧
    Even (Type330.uM (Type120.FV m) (2 ^ (m - 1)) 0 2)
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, by omega⟩
  refine ⟨⟨2 ^ s - 1, ?_⟩, ⟨-4 * Type120.FV (s + 2), ?_⟩,
    ⟨4 * Type120.FV (s + 2) * (2 * 2 ^ s - 1), ?_⟩⟩ <;>
    simp [Type330.uM, uMat, pow_succ] <;> ring

theorem par_u {m : ℕ} (hm : 3 ≤ m) (x : Torus (StrothTypeIndex.t330 m hm).k) :
    (((StrothTypeIndex.t330 m hm).action.φu x) 0).val % 2 = (x 0).val % 2 :=
  matAct_val_zero_mod_two (by rw [t330_k]; omega) _ _ (uM_row hm).1 (uM_row hm).2.1
    (uM_row hm).2.2 x

theorem W_u {m : ℕ} (hm : 3 ≤ m) (w : Torus (StrothTypeIndex.t330 m hm).k) (hw : InW w) :
    ((StrothTypeIndex.t330 m hm).action.φu w) 0 = 0 :=
  (matAct_apply_zero_eq_zero_iff (fun i => by rw [t330_k, t330_k]) _ _ (uM_row hm).1
    (uM_row hm).2.1 (uM_row hm).2.2 hw.2).mpr hw.1

theorem vFacts (m : ℕ) (hm : 3 ≤ m) : VFacts (StrothTypeIndex.t330 m hm) :=
  VFacts.of_equiv (psi m hm) (Type300.vFacts (by omega)) (psi_φuv hm) (psi_φt hm) (psi_φρ hm)
    (psi_val_mod_two hm) (psi_zero hm) (by rw [t330_k]; omega) (par_u hm) (W_u hm)

theorem killFact (m : ℕ) (hm : 3 ≤ m) : KillFact (StrothTypeIndex.t330 m hm) :=
  KillFact.of_equiv (psi m hm) Type300.killFact (psi_φuv hm) (psi_φt hm) (psi_φρ hm) (psi_zero hm)

end Type330

theorem StrothFrame.IsD.stroth_3_8 {G : Type} [Group G] [Finite G] {F : StrothFrame G}
    {D : Subgroup G} {m : ℕ} {hm : 3 ≤ m} {dD : StrothWeakTypeData D (StrothTypeIndex.t330 m hm)}
    (h : F.IsD D dD)
    (hns : IsSylowIn 2 (Subgroup.normalizer (D : Set G))
      ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G))) :
    (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ∨
      ∃ X : Subgroup G, IsMulCommutative X ∧ F.A ≤ X ∧ X ≤ (F.S : Subgroup G) ∧
        F.dA.L ≤ Subgroup.normalizer
          ((X ⊔ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) ∧
        Nat.card D < Nat.card X :=
  h.stroth_form_ii (Type330.vFacts m hm) (Type330.killFact m hm) hns

end CFSG.CGT.Stroth77
