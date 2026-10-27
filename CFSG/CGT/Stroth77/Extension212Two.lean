module

public import CFSG.CGT.Stroth77.Extension212Profile
public import CFSG.CGT.Stroth77.Extension212Group

public section

namespace CFSG.CGT.Stroth77

variable {S : Type*} [Group S] [Finite S] {B C S' : Subgroup S}

theorem sec_t120 {m : ℕ} (hm : 3 ≤ m) (v : Torus (StrothTypeIndex.t120 m hm).k)
    (hρ : ∃ z, 2 • z = (StrothTypeIndex.t120 m hm).action.φρ v - v) :
    (∃ z, 2 • z = v) ∨ (∃ z, 2 • z = v - gen (StrothTypeIndex.t120 m hm).k 0) := by
  have hk : ∀ i, 1 ≤ (StrothTypeIndex.t120 m hm).k i := by
    intro i; fin_cases i <;> simp [StrothTypeIndex.k, Type120.k] <;> omega
  obtain ⟨x, y, z, rfl⟩ := torus_eq_zsmul_gens _ v
  have hR : (StrothTypeIndex.t120 m hm).action.φρ (x • gen _ 0 + y • gen _ 1 + z • gen _ 2) =
      (x - 2 * z) • gen _ 0 + (-z) • gen _ 1 + (y - z) • gen _ 2 := by
    have h0 : (StrothTypeIndex.t120 m hm).action.φρ (gen _ 0) = (1 : ℤ) • gen _ 0 :=
      Type120.rho_c (Type120.data m (by omega))
    have h1 : (StrothTypeIndex.t120 m hm).action.φρ (gen _ 1) = (1 : ℤ) • gen _ 2 :=
      Type120.rho_a (Type120.data m (by omega))
    have h2 : (StrothTypeIndex.t120 m hm).action.φρ (gen _ 2) =
        (-2 : ℤ) • gen _ 0 + (-1 : ℤ) • gen _ 1 + (-1 : ℤ) • gen _ 2 :=
      Type120.rho_b (Type120.data m (by omega))
    rw [map_add, map_add, map_zsmul, map_zsmul, map_zsmul, h0, h1, h2]
    module
  rw [hR] at hρ
  have e : (x - 2 * z) • gen (StrothTypeIndex.t120 m hm).k 0 + (-z) • gen _ 1 +
      (y - z) • gen _ 2 - (x • gen _ 0 + y • gen _ 1 + z • gen _ 2) =
      (-2 * z) • gen _ 0 + (-z - y) • gen _ 1 + (y - 2 * z) • gen _ 2 := by
    module
  rw [e, exists_two_nsmul_eq_iff hk] at hρ
  obtain ⟨-, h1, h2⟩ := hρ
  have hy : Even y := by
    obtain ⟨b, hb⟩ := h2
    exact ⟨b + z, by omega⟩
  have hz : Even z := by
    obtain ⟨a, ha⟩ := h1
    obtain ⟨c, hc⟩ := hy
    exact ⟨-a - c, by omega⟩
  rcases Int.even_or_odd x with hx | hx
  · left
    exact (exists_two_nsmul_eq_iff hk x y z).2 ⟨hx, hy, hz⟩
  · right
    have e2 : x • gen (StrothTypeIndex.t120 m hm).k 0 + y • gen _ 1 + z • gen _ 2 -
        gen _ 0 = (x - 1) • gen _ 0 + y • gen _ 1 + z • gen _ 2 := by
      module
    rw [e2]
    exact (exists_two_nsmul_eq_iff hk _ y z).2 ⟨by
      obtain ⟨w, hw⟩ := hx
      exact ⟨w, by omega⟩, hy, hz⟩

section Target

variable (m : ℕ)

local notation "ι" => Type120.iV (m + 1)
local notation "φ" => Type120.FV (m + 1)
local notation "γ" => Type120.GV (m + 1)

theorem k_t320_succ (h : 3 ≤ m + 1) : ∀ j, (StrothTypeIndex.t320 (m + 1) h).k j = m + 1 := by
  intro j
  fin_cases j <;> rfl

theorem par_uv_t320 (hm : 1 ≤ m) :
    (Type320.uvM ι φ γ).map (Int.cast : ℤ → ZMod 2) = parUV := by
  have hi := iV_cast_two (m + 1)
  have hF := FV_cast_two (n := m + 1) (by omega)
  have hG := GV_cast_two (n := m + 1) (by omega)
  ext a b
  fin_cases a <;> fin_cases b <;>
  simp [parUV, Type320.uvM, Type320.uvA, Type320.tM, Type320.ρM, ofCols_apply, Matrix.mulVec,
    dotProduct, Fin.sum_univ_three, hi, hF, hG] <;> decide

theorem par_t_t320 (hm : 1 ≤ m) :
    (Type320.tM ι φ γ).map (Int.cast : ℤ → ZMod 2) = parT := by
  have hi := iV_cast_two (m + 1)
  have hF := FV_cast_two (n := m + 1) (by omega)
  have hG := GV_cast_two (n := m + 1) (by omega)
  ext a b
  fin_cases a <;> fin_cases b <;>
  simp [parT, Type320.tM, Type320.uvA, Type320.ρM, ofCols_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three, hi, hF, hG] <;> decide

theorem par_u_t320 (hm : 1 ≤ m) : (Type320.uM φ).map (Int.cast : ℤ → ZMod 2) = parU := by
  have hF := FV_cast_two (n := m + 1) (by omega)
  ext a b
  fin_cases a <;> fin_cases b <;>
  simp [parU, Type320.uM, uMat, ofCols_apply, hF] <;> decide

theorem par_ρ_t320 : Type320.ρM.map (Int.cast : ℤ → ZMod 2) = parR := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [parR, Type320.ρM, ofCols_apply] <;> decide

theorem profile2_t320 (h : 3 ≤ m + 1) :
    Profile2 (StrothTypeIndex.t320 (m + 1) h).k (StrothTypeIndex.t320 (m + 1) h).action.φuv
      (StrothTypeIndex.t320 (m + 1) h).action.φt (StrothTypeIndex.t320 (m + 1) h).action.φu
      (StrothTypeIndex.t320 (m + 1) h).action.φρ :=
  profile2_of_par_const (k_t320_succ m h) _ (par_uv_t320 m (by omega)) (par_t_t320 m (by omega))
    (par_u_t320 m (by omega)) (par_ρ_t320)

theorem k_t330_succ (h : 3 ≤ m + 1) : ∀ j, (StrothTypeIndex.t330 (m + 1) h).k j = m + 1 := by
  intro j
  fin_cases j <;> rfl

section Matrices

variable (h : 3 ≤ m + 1)

theorem t320_uv_eq : (StrothTypeIndex.t320 (m + 1) h).action.uv = Type320.uvM ι φ γ := rfl
theorem t320_t_eq : (StrothTypeIndex.t320 (m + 1) h).action.t = Type320.tM ι φ γ := rfl
theorem t320_u_eq : (StrothTypeIndex.t320 (m + 1) h).action.u = Type320.uM φ := rfl
theorem t320_ρ_eq : (StrothTypeIndex.t320 (m + 1) h).action.ρ = Type320.ρM := rfl
theorem t330_uv_eq :
    (StrothTypeIndex.t330 (m + 1) h).action.uv = Type330.uvM ι φ γ (2 ^ (m + 1 - 1)) := rfl
theorem t330_t_eq :
    (StrothTypeIndex.t330 (m + 1) h).action.t = Type330.tM ι φ γ (2 ^ (m + 1 - 1)) := rfl
theorem t330_u_eq : (StrothTypeIndex.t330 (m + 1) h).action.u = Type330.uM φ (2 ^ (m + 1 - 1)) :=
  rfl
theorem t330_ρ_eq : (StrothTypeIndex.t330 (m + 1) h).action.ρ = Type330.ρM := rfl

end Matrices

theorem twist2_t320 (h : 3 ≤ m + 1) :
    Twist2 (StrothTypeIndex.t320 (m + 1) h).k (StrothTypeIndex.t320 (m + 1) h).action.φuv
      (StrothTypeIndex.t320 (m + 1) h).action.φt (StrothTypeIndex.t320 (m + 1) h).action.φu
      (StrothTypeIndex.t320 (m + 1) h).action.φρ (StrothTypeIndex.t330 (m + 1) h).action.φuv
      (StrothTypeIndex.t330 (m + 1) h).action.φt (StrothTypeIndex.t330 (m + 1) h).action.φu
      (StrothTypeIndex.t330 (m + 1) h).action.φρ := by
  have hK := k_t320_succ m h
  have hK' := k_t330_succ m h
  have e0 {M M' : IntMat} (hM : Compat (StrothTypeIndex.t320 (m + 1) h).k M)
      (hM' : Compat (StrothTypeIndex.t320 (m + 1) h).k M') (j : Fin 3)
      (h0 : M 0 j = M' 0 j) (h1 : M 1 j = M' 1 j) (h2 : M 2 j = M' 2 j) :
      matAct _ M' hM' (gen _ j) = matAct _ M hM (gen _ j) := by
    rw [matAct_gen_eq, matAct_gen_eq, h0, h1, h2]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine matAct_gen_eq_add_tw _ _ 0 0 1 0 ?_ ?_ ?_ <;>
      simp [hK, hK', t320_uv_eq, t330_uv_eq, Type320.uvM, Type330.uvM, ofCols_apply]
  · exact e0 _ _ 1 (by simp [t320_uv_eq, t330_uv_eq, Type320.uvM, Type330.uvM, Type320.uvA,
      Type330.uvA, ofCols_apply]) (by simp [t320_uv_eq, t330_uv_eq, Type320.uvM, Type330.uvM,
      Type320.uvA, Type330.uvA, ofCols_apply]) (by simp [t320_uv_eq, t330_uv_eq, Type320.uvM,
      Type330.uvM, Type320.uvA, Type330.uvA, ofCols_apply])
  · refine matAct_gen_eq_of_dvd _ _ 2 ?_ ?_ ?_ <;>
      simp only [hK, hK', t320_uv_eq, t330_uv_eq]
    · exact ⟨8 * ι * φ, by
        simp [Type320.uvM, Type330.uvM, Type320.uvA, Type330.uvA, Type320.tM, Type330.tM,
          Type320.ρM, Type330.ρM, ofCols_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        ring⟩
    · exact ⟨2 * ι * φ, by
        simp [Type320.uvM, Type330.uvM, Type320.uvA, Type330.uvA, Type320.tM, Type330.tM,
          Type320.ρM, Type330.ρM, ofCols_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        ring⟩
    · exact ⟨2 * ι * φ, by
        simp [Type320.uvM, Type330.uvM, Type320.uvA, Type330.uvA, Type320.tM, Type330.tM,
          Type320.ρM, Type330.ρM, ofCols_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        ring⟩
  · refine matAct_gen_eq_add_tw _ _ 0 0 0 1 ?_ ?_ ?_ <;>
      simp [hK, hK', t320_t_eq, t330_t_eq, Type320.tM, Type330.tM, ofCols_apply]
  · exact e0 _ _ 1 (by simp [t320_t_eq, t330_t_eq, Type320.tM, Type330.tM, ofCols_apply])
      (by simp [t320_t_eq, t330_t_eq, Type320.tM, Type330.tM, ofCols_apply])
      (by simp [t320_t_eq, t330_t_eq, Type320.tM, Type330.tM, ofCols_apply])
  · exact e0 _ _ 2 (by simp [t320_t_eq, t330_t_eq, Type320.tM, Type330.tM, Type320.uvA,
      Type330.uvA, Type320.ρM, Type330.ρM, ofCols_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three])
      (by simp [t320_t_eq, t330_t_eq, Type320.tM, Type330.tM, Type320.uvA, Type330.uvA,
        Type320.ρM, Type330.ρM, ofCols_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three])
      (by simp [t320_t_eq, t330_t_eq, Type320.tM, Type330.tM, Type320.uvA, Type330.uvA,
        Type320.ρM, Type330.ρM, ofCols_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three])
  · refine matAct_gen_eq_add_tw _ _ 0 1 0 0 ?_ ?_ ?_ <;>
      simp [hK, hK', t320_u_eq, t330_u_eq, Type320.uM, Type330.uM, uMat, ofCols_apply] <;>
      ring_nf <;> simp
  · exact e0 _ _ 1 (by simp [t320_u_eq, t330_u_eq, Type320.uM, Type330.uM, uMat, ofCols_apply])
      (by simp [t320_u_eq, t330_u_eq, Type320.uM, Type330.uM, uMat, ofCols_apply])
      (by simp [t320_u_eq, t330_u_eq, Type320.uM, Type330.uM, uMat, ofCols_apply])
  · refine matAct_gen_eq_of_dvd _ _ 2 ?_ ?_ ?_ <;>
      simp only [hK, hK', t320_u_eq, t330_u_eq]
    · exact ⟨-4 * φ, by simp [Type320.uM, Type330.uM, uMat, ofCols_apply]; ring⟩
    · simp [Type320.uM, Type330.uM, uMat, ofCols_apply]
    · simp [Type320.uM, Type330.uM, uMat, ofCols_apply]
  · exact e0 _ _ 0 (by simp [t320_ρ_eq, t330_ρ_eq, Type320.ρM, Type330.ρM, ofCols_apply])
      (by simp [t320_ρ_eq, t330_ρ_eq, Type320.ρM, Type330.ρM, ofCols_apply])
      (by simp [t320_ρ_eq, t330_ρ_eq, Type320.ρM, Type330.ρM, ofCols_apply])
  · exact e0 _ _ 1 (by simp [t320_ρ_eq, t330_ρ_eq, Type320.ρM, Type330.ρM, ofCols_apply])
      (by simp [t320_ρ_eq, t330_ρ_eq, Type320.ρM, Type330.ρM, ofCols_apply])
      (by simp [t320_ρ_eq, t330_ρ_eq, Type320.ρM, Type330.ρM, ofCols_apply])
  · exact e0 _ _ 2 (by simp [t320_ρ_eq, t330_ρ_eq, Type320.ρM, Type330.ρM, ofCols_apply])
      (by simp [t320_ρ_eq, t330_ρ_eq, Type320.ρM, Type330.ρM, ofCols_apply])
      (by simp [t320_ρ_eq, t330_ρ_eq, Type320.ρM, Type330.ρM, ofCols_apply])

theorem restrict_t120_t320 (h : 3 ≤ m + 1) (hm : 3 ≤ m) :
    MatEq (StrothTypeIndex.t320 (m + 1) h).k
        ((StrothTypeIndex.t320 (m + 1) h).action.uv * diag2)
        (diag2 * (StrothTypeIndex.t120 m hm).action.uv) ∧
      MatEq (StrothTypeIndex.t320 (m + 1) h).k
        ((StrothTypeIndex.t320 (m + 1) h).action.t * diag2)
        (diag2 * (StrothTypeIndex.t120 m hm).action.t) ∧
      MatEq (StrothTypeIndex.t320 (m + 1) h).k
        ((StrothTypeIndex.t320 (m + 1) h).action.u * diag2)
        (diag2 * (StrothTypeIndex.t120 m hm).action.u) ∧
      MatEq (StrothTypeIndex.t320 (m + 1) h).k
        ((StrothTypeIndex.t320 (m + 1) h).action.ρ * diag2)
        (diag2 * (StrothTypeIndex.t120 m hm).action.ρ) := by
  have e120uv : (StrothTypeIndex.t120 m hm).action.uv = Type120.uvM ι φ γ := rfl
  have e120t : (StrothTypeIndex.t120 m hm).action.t = Type120.tM ι φ γ := rfl
  have e120u : (StrothTypeIndex.t120 m hm).action.u = Type120.uM φ := rfl
  have e120ρ : (StrothTypeIndex.t120 m hm).action.ρ = Type120.ρM := rfl
  refine ⟨MatEq.of_eq ?_, MatEq.of_eq ?_, MatEq.of_eq ?_, MatEq.of_eq ?_⟩ <;>
  · simp only [t320_uv_eq, t320_t_eq, t320_u_eq, t320_ρ_eq, e120uv, e120t, e120u, e120ρ]
    ext a b
    fin_cases a <;> fin_cases b <;>
    simp [diag2, Matrix.mul_diagonal, Matrix.diagonal_mul, Type320.uvM, Type320.uvA, Type320.tM,
      Type320.ρM, Type320.uM, Type120.uvM, Type120.uvA, Type120.tM, Type120.ρM, Type120.uM, uMat,
      ofCols_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

end Target

theorem hasStrothType_t320_or_t330_of_data {m : ℕ} {hm : 3 ≤ m}
    (D : StrothTypeData B (StrothTypeIndex.t120 m hm)) (hBC : B ≤ C)
    (hC : C ≤ Subgroup.centralizer (B : Set S)) (hrel : Nat.card C = 2 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C) (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') :
    HasStrothType C (StrothTypeIndex.t320 (m + 1) (by omega)) ∨
      HasStrothType C (StrothTypeIndex.t330 (m + 1) (by omega)) := by
  have h : 3 ≤ m + 1 := by omega
  obtain ⟨cV, cW, cU, cR⟩ := restrict_t120_t320 m h hm
  rcases hasStrothType_or_of_index_two_of_data D hBC hC hrel hL hH hcS
      (fun v _ _ _ hρ => sec_t120 hm v hρ) (StrothTypeIndex.t320 (m + 1) h) rfl rfl rfl
      (fun j => by rw [k_t320_succ]; omega) (by rw [k_t320_succ]; omega)
      (StrothTypeIndex.t330 (m + 1) h).action (profile2_t320 m h) (twist2_t320 m h)
      cV cW cU cR with h1 | ⟨E, φ, h2⟩
  · exact Or.inl h1
  · exact Or.inr (hasStrothType_of_basisChange D hL (StrothTypeIndex.t330 (m + 1) h) E φ h2)

theorem hasStrothTypeOver_t320_or_t330_of_data {m : ℕ} {hm : 3 ≤ m}
    (D : StrothTypeData B (StrothTypeIndex.t120 m hm)) (hBC : B ≤ C)
    (hC : C ≤ Subgroup.centralizer (B : Set S)) (hrel : Nat.card C = 2 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C) (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') :
    HasStrothTypeOver D C (StrothTypeIndex.t320 (m + 1) (by omega)) ∨
      HasStrothTypeOver D C (StrothTypeIndex.t330 (m + 1) (by omega)) := by
  have h : 3 ≤ m + 1 := by omega
  obtain ⟨cV, cW, cU, cR⟩ := restrict_t120_t320 m h hm
  rcases hasStrothTypeOver_or_of_index_two_of_data D hBC hC hrel hL hH hcS
      (fun v _ _ _ hρ => sec_t120 hm v hρ) (StrothTypeIndex.t320 (m + 1) h) rfl rfl rfl
      (fun j => by rw [k_t320_succ]; omega) (by rw [k_t320_succ]; omega)
      (StrothTypeIndex.t330 (m + 1) h).action (profile2_t320 m h) (twist2_t320 m h)
      cV cW cU cR with h1 | ⟨E, φ, h2⟩
  · exact Or.inl h1
  · exact Or.inr (hasStrothTypeOver_of_basisChange D hL (StrothTypeIndex.t330 (m + 1) h) E φ h2)

end CFSG.CGT.Stroth77
