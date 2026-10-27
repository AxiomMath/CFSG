module

public import CFSG.CGT.Stroth77.Extension212Profile
public import CFSG.CGT.Stroth77.Extension212Group

public section

namespace CFSG.CGT.Stroth77

variable {S : Type*} [Group S] [Finite S] {B C S' : Subgroup S}

theorem sec_t220 {s : ℕ} (hs : 1 ≤ s) (v : Torus (StrothTypeIndex.t220 s hs).k)
    (hρ : ∃ z, 2 • z = (StrothTypeIndex.t220 s hs).action.φρ v - v) :
    (∃ z, 2 • z = v) ∨ (∃ z, 2 • z = v - gen (StrothTypeIndex.t220 s hs).k 0) := by
  have hk : ∀ i, 1 ≤ (StrothTypeIndex.t220 s hs).k i := by
    intro i; fin_cases i <;> simp [StrothTypeIndex.k, Type220.k]
  obtain ⟨x, y, z, rfl⟩ := torus_eq_zsmul_gens _ v
  have hR : (StrothTypeIndex.t220 s hs).action.φρ (x • gen _ 0 + y • gen _ 1 + z • gen _ 2) =
      (x - z) • gen _ 0 + (-z) • gen _ 1 + (y - z) • gen _ 2 := by
    change matAct _ (StrothTypeIndex.t220 s hs).action.ρ _ _ = _
    rw [matAct_zsmul_gens]
    have hρM : (StrothTypeIndex.t220 s hs).action.ρ = Type220.ρM := rfl
    simp only [hρM, Type220.ρM, ofCols_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    module
  rw [hR] at hρ
  have e : (x - z) • gen (StrothTypeIndex.t220 s hs).k 0 + (-z) • gen _ 1 +
      (y - z) • gen _ 2 - (x • gen _ 0 + y • gen _ 1 + z • gen _ 2) =
      (-z) • gen _ 0 + (-z - y) • gen _ 1 + (y - 2 * z) • gen _ 2 := by
    module
  rw [e, exists_two_nsmul_eq_iff hk] at hρ
  obtain ⟨h0, -, h2⟩ := hρ
  have hz : Even z := by
    obtain ⟨a, ha⟩ := h0
    exact ⟨-a, by omega⟩
  have hy : Even y := by
    obtain ⟨b, hb⟩ := h2
    obtain ⟨c, hc⟩ := hz
    exact ⟨b + c + c, by omega⟩
  rcases Int.even_or_odd x with hx | hx
  · left
    exact (exists_two_nsmul_eq_iff hk x y z).2 ⟨hx, hy, hz⟩
  · right
    have e2 : x • gen (StrothTypeIndex.t220 s hs).k 0 + y • gen _ 1 + z • gen _ 2 -
        gen _ 0 = (x - 1) • gen _ 0 + y • gen _ 1 + z • gen _ 2 := by
      module
    rw [e2]
    exact (exists_two_nsmul_eq_iff hk _ y z).2 ⟨by
      obtain ⟨w, hw⟩ := hx
      exact ⟨w, by omega⟩, hy, hz⟩

section Target

variable (s : ℕ)

local notation "ι" => Type120.iV (s + 3 + 1)
local notation "φ" => Type120.FV (s + 3 + 1)
local notation "γ" => Type120.GV (s + 3 + 1)

section Matrices

variable (h : 3 ≤ s + 3)

theorem t120_uv_eq3 : (StrothTypeIndex.t120 (s + 3) h).action.uv = Type120.uvM ι φ γ := rfl
theorem t120_t_eq3 : (StrothTypeIndex.t120 (s + 3) h).action.t = Type120.tM ι φ γ := rfl
theorem t120_u_eq3 : (StrothTypeIndex.t120 (s + 3) h).action.u = Type120.uM φ := rfl
theorem t120_ρ_eq3 : (StrothTypeIndex.t120 (s + 3) h).action.ρ = Type120.ρM := rfl
theorem t130_uv_eq3 :
    (StrothTypeIndex.t130 (s + 3) h).action.uv = Type130.uvM ι φ γ (2 ^ (s + 3)) := rfl
theorem t130_t_eq3 :
    (StrothTypeIndex.t130 (s + 3) h).action.t = Type130.tM ι φ γ (2 ^ (s + 3)) := rfl
theorem t130_u_eq3 :
    (StrothTypeIndex.t130 (s + 3) h).action.u = Type130.uM φ (2 ^ (s + 3 - 1)) := rfl
theorem t130_ρ_eq3 : (StrothTypeIndex.t130 (s + 3) h).action.ρ = Type130.ρM := rfl

end Matrices

theorem profile2_t120 (h : 3 ≤ s + 3) :
    Profile2 (StrothTypeIndex.t120 (s + 3) h).k (StrothTypeIndex.t120 (s + 3) h).action.φuv
      (StrothTypeIndex.t120 (s + 3) h).action.φt (StrothTypeIndex.t120 (s + 3) h).action.φu
      (StrothTypeIndex.t120 (s + 3) h).action.φρ := by
  have hi := iV_cast_two (s + 3 + 1)
  have hF := FV_cast_two_succ (s + 3)
  have hG := GV_cast_two_add_two (s + 2)
  refine profile2_of_par (k := s + 3) (n := s + 4) rfl (by omega) (by omega) _ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_
  all_goals simp only [t120_uv_eq3, t120_t_eq3, t120_u_eq3, t120_ρ_eq3]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    first
    | (apply odd_of_cast_two; simp [Type120.uvM, Type120.uvA, Type120.tM, Type120.ρM, ofCols_apply,
        Matrix.mulVec, dotProduct, Fin.sum_univ_three, hi, hF, hG] <;> decide)
    | (apply even_of_cast_two; simp [Type120.uvM, Type120.uvA, Type120.tM, Type120.ρM,
        ofCols_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three, hi, hF, hG] <;> decide)
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    first
    | (apply odd_of_cast_two; simp [Type120.tM, Type120.uvA, Type120.ρM, ofCols_apply,
        Matrix.mulVec, dotProduct, Fin.sum_univ_three, hi, hF, hG] <;> decide)
    | (apply even_of_cast_two; simp [Type120.tM, Type120.uvA, Type120.ρM, ofCols_apply,
        Matrix.mulVec, dotProduct, Fin.sum_univ_three, hi, hF, hG] <;> decide)
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    first
    | (apply odd_of_cast_two; simp [Type120.uM, uMat, ofCols_apply, hF] <;> decide)
    | (apply even_of_cast_two; simp [Type120.uM, uMat, ofCols_apply, hF] <;> decide)
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    first
    | (apply odd_of_cast_two; simp [Type120.ρM, ofCols_apply] <;> decide)
    | (apply even_of_cast_two; simp [Type120.ρM, ofCols_apply] <;> decide)
  · refine ⟨?_, ?_⟩ <;> apply even_of_cast_two <;>
      simp [Type120.uvM, Type120.uvA, Type120.tM, Type120.ρM, ofCols_apply, Matrix.mulVec,
        dotProduct, Fin.sum_univ_three, hi, hF, hG] <;> decide
  · refine ⟨?_, ?_⟩ <;> apply even_of_cast_two <;>
      simp [Type120.tM, Type120.uvA, Type120.ρM, ofCols_apply, Matrix.mulVec, dotProduct,
        Fin.sum_univ_three, hi, hF, hG] <;> decide
  · refine ⟨?_, ?_⟩ <;> apply even_of_cast_two <;>
      simp [Type120.uM, uMat, ofCols_apply, hF] <;> decide
  · refine ⟨?_, ?_⟩ <;> apply even_of_cast_two <;> simp [Type120.ρM, ofCols_apply] <;> decide
  · exact ⟨1, -1, by simp [Type120.uvM, ofCols_apply], by simp [Type120.uvM, ofCols_apply],
      by decide, by decide⟩
  · exact ⟨1, 2, by simp [Type120.tM, ofCols_apply], by simp [Type120.tM, ofCols_apply],
      by decide, by decide⟩
  · exact ⟨0, 0, by simp [Type120.uM, uMat, ofCols_apply], by simp [Type120.uM, uMat,
      ofCols_apply], by decide, by decide⟩
  · exact ⟨0, 0, by simp [Type120.ρM, ofCols_apply], by simp [Type120.ρM, ofCols_apply],
      by decide, by decide⟩

theorem twist2_t120 (h : 3 ≤ s + 3) :
    Twist2 (StrothTypeIndex.t120 (s + 3) h).k (StrothTypeIndex.t120 (s + 3) h).action.φuv
      (StrothTypeIndex.t120 (s + 3) h).action.φt (StrothTypeIndex.t120 (s + 3) h).action.φu
      (StrothTypeIndex.t120 (s + 3) h).action.φρ (StrothTypeIndex.t130 (s + 3) h).action.φuv
      (StrothTypeIndex.t130 (s + 3) h).action.φt (StrothTypeIndex.t130 (s + 3) h).action.φu
      (StrothTypeIndex.t130 (s + 3) h).action.φρ := by
  have hK0 : (StrothTypeIndex.t120 (s + 3) h).k 0 = s + 3 := rfl
  have hK1 : (StrothTypeIndex.t120 (s + 3) h).k 1 = s + 4 := rfl
  have hK2 : (StrothTypeIndex.t120 (s + 3) h).k 2 = s + 4 := rfl
  have hK0' : (StrothTypeIndex.t130 (s + 3) h).k 0 = s + 3 := rfl
  have hK1' : (StrothTypeIndex.t130 (s + 3) h).k 1 = s + 4 := rfl
  have hK2' : (StrothTypeIndex.t130 (s + 3) h).k 2 = s + 4 := rfl
  have e0 {M M' : IntMat} (hM : Compat (StrothTypeIndex.t120 (s + 3) h).k M)
      (hM' : Compat (StrothTypeIndex.t120 (s + 3) h).k M') (j : Fin 3)
      (h0 : M 0 j = M' 0 j) (h1 : M 1 j = M' 1 j) (h2 : M 2 j = M' 2 j) :
      matAct _ M' hM' (gen _ j) = matAct _ M hM (gen _ j) := by
    rw [matAct_gen_eq, matAct_gen_eq, h0, h1, h2]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine matAct_gen_eq_add_tw _ _ 0 0 1 0 ?_ ?_ ?_ <;>
      simp [hK0, hK1, hK2, hK0', hK1', hK2', t120_uv_eq3, t130_uv_eq3, Type120.uvM, Type130.uvM,
        ofCols_apply]
  · exact e0 _ _ 1 (by simp [t120_uv_eq3, t130_uv_eq3, Type120.uvM, Type130.uvM, Type120.uvA,
      Type130.uvA, ofCols_apply]) (by simp [t120_uv_eq3, t130_uv_eq3, Type120.uvM, Type130.uvM,
      Type120.uvA, Type130.uvA, ofCols_apply]) (by simp [t120_uv_eq3, t130_uv_eq3, Type120.uvM,
      Type130.uvM, Type120.uvA, Type130.uvA, ofCols_apply])
  · refine matAct_gen_eq_of_dvd _ _ 2 ?_ ?_ ?_ <;>
      simp only [hK0, hK1, hK2, hK0', hK1', hK2', t120_uv_eq3, t130_uv_eq3]
    · exact ⟨4 * ι * φ, by
        simp [Type120.uvM, Type130.uvM, Type120.uvA, Type130.uvA, Type120.tM, Type130.tM,
          Type120.ρM, Type130.ρM, ofCols_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        ring⟩
    · exact ⟨ι * φ, by
        simp [Type120.uvM, Type130.uvM, Type120.uvA, Type130.uvA, Type120.tM, Type130.tM,
          Type120.ρM, Type130.ρM, ofCols_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        ring⟩
    · exact ⟨ι * φ, by
        simp [Type120.uvM, Type130.uvM, Type120.uvA, Type130.uvA, Type120.tM, Type130.tM,
          Type120.ρM, Type130.ρM, ofCols_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        ring⟩
  · refine matAct_gen_eq_add_tw _ _ 0 0 0 1 ?_ ?_ ?_ <;>
      simp [hK0, hK1, hK2, hK0', hK1', hK2', t120_t_eq3, t130_t_eq3, Type120.tM, Type130.tM,
        ofCols_apply]
  · exact e0 _ _ 1 (by simp [t120_t_eq3, t130_t_eq3, Type120.tM, Type130.tM, ofCols_apply])
      (by simp [t120_t_eq3, t130_t_eq3, Type120.tM, Type130.tM, ofCols_apply])
      (by simp [t120_t_eq3, t130_t_eq3, Type120.tM, Type130.tM, ofCols_apply])
  · exact e0 _ _ 2 (by simp [t120_t_eq3, t130_t_eq3, Type120.tM, Type130.tM, Type120.uvA,
      Type130.uvA, Type120.ρM, Type130.ρM, ofCols_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three])
      (by simp [t120_t_eq3, t130_t_eq3, Type120.tM, Type130.tM, Type120.uvA, Type130.uvA,
        Type120.ρM, Type130.ρM, ofCols_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three])
      (by simp [t120_t_eq3, t130_t_eq3, Type120.tM, Type130.tM, Type120.uvA, Type130.uvA,
        Type120.ρM, Type130.ρM, ofCols_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three])
  · refine matAct_gen_eq_add_tw _ _ 0 1 0 0 ?_ ?_ ?_ <;>
      simp [hK0, hK1, hK2, hK0', hK1', hK2', t120_u_eq3, t130_u_eq3, Type120.uM, Type130.uM,
        uMat, ofCols_apply] <;>
      ring_nf <;> simp
  · exact e0 _ _ 1 (by simp [t120_u_eq3, t130_u_eq3, Type120.uM, Type130.uM, uMat, ofCols_apply])
      (by simp [t120_u_eq3, t130_u_eq3, Type120.uM, Type130.uM, uMat, ofCols_apply])
      (by simp [t120_u_eq3, t130_u_eq3, Type120.uM, Type130.uM, uMat, ofCols_apply])
  · refine matAct_gen_eq_of_dvd _ _ 2 ?_ ?_ ?_ <;>
      simp only [hK0, hK1, hK2, hK0', hK1', hK2', t120_u_eq3, t130_u_eq3]
    · exact ⟨-2 * φ, by simp [Type120.uM, Type130.uM, uMat, ofCols_apply]; ring⟩
    · simp [Type120.uM, Type130.uM, uMat, ofCols_apply]
    · simp [Type120.uM, Type130.uM, uMat, ofCols_apply]
  · exact e0 _ _ 0 (by simp [t120_ρ_eq3, t130_ρ_eq3, Type120.ρM, Type130.ρM, ofCols_apply])
      (by simp [t120_ρ_eq3, t130_ρ_eq3, Type120.ρM, Type130.ρM, ofCols_apply])
      (by simp [t120_ρ_eq3, t130_ρ_eq3, Type120.ρM, Type130.ρM, ofCols_apply])
  · exact e0 _ _ 1 (by simp [t120_ρ_eq3, t130_ρ_eq3, Type120.ρM, Type130.ρM, ofCols_apply])
      (by simp [t120_ρ_eq3, t130_ρ_eq3, Type120.ρM, Type130.ρM, ofCols_apply])
      (by simp [t120_ρ_eq3, t130_ρ_eq3, Type120.ρM, Type130.ρM, ofCols_apply])
  · exact e0 _ _ 2 (by simp [t120_ρ_eq3, t130_ρ_eq3, Type120.ρM, Type130.ρM, ofCols_apply])
      (by simp [t120_ρ_eq3, t130_ρ_eq3, Type120.ρM, Type130.ρM, ofCols_apply])
      (by simp [t120_ρ_eq3, t130_ρ_eq3, Type120.ρM, Type130.ρM, ofCols_apply])

theorem restrict_t220_t120 (h : 3 ≤ s + 3) (hs : 1 ≤ s) :
    MatEq (StrothTypeIndex.t120 (s + 3) h).k
        ((StrothTypeIndex.t120 (s + 3) h).action.uv * diag2)
        (diag2 * (StrothTypeIndex.t220 s hs).action.uv) ∧
      MatEq (StrothTypeIndex.t120 (s + 3) h).k
        ((StrothTypeIndex.t120 (s + 3) h).action.t * diag2)
        (diag2 * (StrothTypeIndex.t220 s hs).action.t) ∧
      MatEq (StrothTypeIndex.t120 (s + 3) h).k
        ((StrothTypeIndex.t120 (s + 3) h).action.u * diag2)
        (diag2 * (StrothTypeIndex.t220 s hs).action.u) ∧
      MatEq (StrothTypeIndex.t120 (s + 3) h).k
        ((StrothTypeIndex.t120 (s + 3) h).action.ρ * diag2)
        (diag2 * (StrothTypeIndex.t220 s hs).action.ρ) := by
  have e220uv : (StrothTypeIndex.t220 s hs).action.uv = Type220.uvM ι φ γ := rfl
  have e220t : (StrothTypeIndex.t220 s hs).action.t = Type220.tM ι φ γ := rfl
  have e220u : (StrothTypeIndex.t220 s hs).action.u = Type220.uM ι φ γ := rfl
  have e220ρ : (StrothTypeIndex.t220 s hs).action.ρ = Type220.ρM := rfl
  refine ⟨MatEq.of_eq ?_, MatEq.of_eq ?_, MatEq.of_eq ?_, MatEq.of_eq ?_⟩ <;>
  · simp only [t120_uv_eq3, t120_t_eq3, t120_u_eq3, t120_ρ_eq3, e220uv, e220t, e220u, e220ρ]
    ext a b
    fin_cases a <;> fin_cases b <;>
    simp [diag2, Matrix.mul_diagonal, Matrix.diagonal_mul, Type120.uvM, Type120.uvA, Type120.tM,
      Type120.ρM, Type120.uM, Type220.uvM, Type220.uvA, Type220.tM, Type220.ρM, Type220.uM, uMat,
      ofCols_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

end Target

theorem hasStrothType_t120_or_t130_of_data {s : ℕ} {hs : 1 ≤ s}
    (D : StrothTypeData B (StrothTypeIndex.t220 s hs)) (hBC : B ≤ C)
    (hC : C ≤ Subgroup.centralizer (B : Set S)) (hrel : Nat.card C = 2 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C) (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') :
    HasStrothType C (StrothTypeIndex.t120 (s + 3) (by omega)) ∨
      HasStrothType C (StrothTypeIndex.t130 (s + 3) (by omega)) := by
  have h : 3 ≤ s + 3 := by omega
  obtain ⟨cV, cW, cU, cR⟩ := restrict_t220_t120 s h hs
  rcases hasStrothType_or_of_index_two_of_data D hBC hC hrel hL hH hcS
      (fun v _ _ _ hρ => sec_t220 hs v hρ) (StrothTypeIndex.t120 (s + 3) h) rfl rfl rfl
      (forall_fin_three (P := fun j => 1 ≤ (StrothTypeIndex.t120 (s + 3) h).k j)
        (by change 1 ≤ s + 3; omega) (by change 1 ≤ s + 3 + 1; omega)
        (by change 1 ≤ s + 3 + 1; omega))
      (by change 2 ≤ s + 3; omega)
      (StrothTypeIndex.t130 (s + 3) h).action (profile2_t120 s h) (twist2_t120 s h)
      cV cW cU cR with h1 | ⟨E, φ, h2⟩
  · exact Or.inl h1
  · exact Or.inr (hasStrothType_of_basisChange D hL (StrothTypeIndex.t130 (s + 3) h) E φ h2)

theorem hasStrothTypeOver_t120_or_t130_of_data {s : ℕ} {hs : 1 ≤ s}
    (D : StrothTypeData B (StrothTypeIndex.t220 s hs)) (hBC : B ≤ C)
    (hC : C ≤ Subgroup.centralizer (B : Set S)) (hrel : Nat.card C = 2 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C) (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') :
    HasStrothTypeOver D C (StrothTypeIndex.t120 (s + 3) (by omega)) ∨
      HasStrothTypeOver D C (StrothTypeIndex.t130 (s + 3) (by omega)) := by
  have h : 3 ≤ s + 3 := by omega
  obtain ⟨cV, cW, cU, cR⟩ := restrict_t220_t120 s h hs
  rcases hasStrothTypeOver_or_of_index_two_of_data D hBC hC hrel hL hH hcS
      (fun v _ _ _ hρ => sec_t220 hs v hρ) (StrothTypeIndex.t120 (s + 3) h) rfl rfl rfl
      (forall_fin_three (P := fun j => 1 ≤ (StrothTypeIndex.t120 (s + 3) h).k j)
        (by change 1 ≤ s + 3; omega) (by change 1 ≤ s + 3 + 1; omega)
        (by change 1 ≤ s + 3 + 1; omega))
      (by change 2 ≤ s + 3; omega)
      (StrothTypeIndex.t130 (s + 3) h).action (profile2_t120 s h) (twist2_t120 s h)
      cV cW cU cR with h1 | ⟨E, φ, h2⟩
  · exact Or.inl h1
  · exact Or.inr (hasStrothTypeOver_of_basisChange D hL (StrothTypeIndex.t130 (s + 3) h) E φ h2)

end CFSG.CGT.Stroth77
