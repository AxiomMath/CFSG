module

public import CFSG.CGT.Stroth77.Extension25Common
public import CFSG.CGT.Stroth77.TorusNormalForm

public section

namespace CFSG.CGT.Stroth77

open Matrix

theorem t321_k_pos (i : Fin 3) : 1 ≤ Type321.k i := by
  fin_cases i <;> simp [Type321.k]

theorem parityTorus_rho_t321 (y : Torus StrothTypeIndex.t321.k) :
    parityTorus _ t321_k_pos (StrothTypeIndex.t321.action.φρ y) =
      rhoBar300 (parityTorus _ t321_k_pos y) := by
  change parityTorus Type321.k t321_k_pos (matAct Type321.k Type321.ρM Type321.compat_rho y) =
    rhoBar300 (parityTorus Type321.k t321_k_pos y)
  obtain ⟨v, hv⟩ := Torus.exists_ofInt (k := Type321.k) y
  rw [← hv, matAct_ofInt, Torus.ofInt_eq_zsmul_gens, Torus.ofInt_eq_zsmul_gens,
    parityTorus_zsmul_gens, parityTorus_zsmul_gens]
  have h4 : (4 : ZMod 2) = 0 := by decide
  funext r
  fin_cases r <;> simp [rhoBar300, Type321.ρM, ofCols_mulVec, h4, sub_eq_add_neg,
    ZMod.neg_eq_self_mod_two]

theorem parityTorus_uv_c_sub_t321 :
    parityTorus _ t321_k_pos (StrothTypeIndex.t321.action.φuv Torus.c - Torus.c) = ![0, 1, 1] := by
  change parityTorus Type321.k t321_k_pos
    (matAct Type321.k Type321.uvM Type321.compat_uv (Torus.c : Torus Type321.k) -
      (Torus.c : Torus Type321.k)) = ![0, 1, 1]
  have hc : (Torus.c : Torus Type321.k) = Torus.ofInt Type321.k ![1, 0, 0] := by
    rw [Torus.ofInt_eq_zsmul_gens]
    simp
  rw [hc, matAct_ofInt, ← Torus.ofInt_sub, Torus.ofInt_eq_zsmul_gens, parityTorus_zsmul_gens]
  have h4 : (4 : ZMod 2) = 0 := by decide
  funext r
  fin_cases r <;> simp [Type321.uvM, Type321.uvA, Type321.tM, Type321.ρM, ofCols_mulVec, h4]

theorem false_of_index_two_t321_of_data {S : Type*} [Group S] [Finite S] {B C S' : Subgroup S}
    (D : StrothTypeData B StrothTypeIndex.t321)
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') : False := by
  obtain ⟨zuv, -, h1, -, -, -⟩ := exists_cocycle_index_two_of_data_Idx4 D t321_k_pos
    parityTorus_rho_t321 (fun v h1 h2 => rhoBar300_fixed_check v ⟨h1, h2⟩) hBC hC hrel hL hH hcS
  have h0 : parityTorus _ t321_k_pos (StrothTypeIndex.t321.action.φuv Torus.c - Torus.c) = 0 :=
    (parityTorus_eq_zero_iff t321_k_pos _).mpr ⟨zuv, h1⟩
  rw [parityTorus_uv_c_sub_t321] at h0
  exact absurd (congrFun h0 1) (by decide)

theorem iV_FV_GV_three : Type120.iV 3 = 43 ∧ Type120.FV 3 = 21 ∧ Type120.GV 3 = 3 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem t321_uvM_matEq :
    MatEq Type321.k (Type320.uvM (Type120.iV 3) (Type120.FV 3) (Type120.GV 3)) Type321.uvM := by
  obtain ⟨hi, hF, hG⟩ := iV_FV_GV_three
  rw [hi, hF, hG]
  refine MatEq.of_witness (W := !![-5, 451, -37872; 0, -27, -6915; 0, 10, 705]) ?_
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp [Type320.uvM, Type320.uvA, Type320.tM, Type320.ρM, Type321.uvM, Type321.uvA,
      Type321.tM, Type321.ρM, Type321.k, ofCols_mulVec, ofCols_apply]

theorem t321_tM_matEq :
    MatEq Type321.k (Type320.tM (Type120.iV 3) (Type120.FV 3) (Type120.GV 3)) Type321.tM := by
  obtain ⟨hi, hF, hG⟩ := iV_FV_GV_three
  rw [hi, hF, hG]
  refine MatEq.of_witness (W := !![-5, 129, 405; 0, -38, -10; 0, -43, -37]) ?_
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp [Type320.uvA, Type320.tM, Type320.ρM, Type321.uvA, Type321.tM, Type321.ρM,
      Type321.k, ofCols_mulVec, ofCols_apply]

theorem t321_uM_matEq : MatEq Type321.k (Type320.uM (Type120.FV 3)) Type321.uM := by
  obtain ⟨-, hF, -⟩ := iV_FV_GV_three
  rw [hF]
  refine MatEq.of_witness (W := !![0, -21, -21; 0, 0, 0; 0, 0, 0]) ?_
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp [Type320.uM, Type321.uM, uMat, Type321.k, ofCols_apply]

theorem t321_ρM_matEq : MatEq Type321.k Type320.ρM Type321.ρM := by
  refine MatEq.of_witness (W := !![0, 0, -1; 0, 0, 0; 0, 0, 0]) ?_
  intro r c
  fin_cases r <;> fin_cases c <;> simp [Type320.ρM, Type321.ρM, Type321.k, ofCols_apply]

theorem t320_three_φuv :
    (StrothTypeIndex.t320 3 le_rfl).action.φuv = StrothTypeIndex.t321.action.φuv :=
  matAct_congr (k := Type321.k) _ _ t321_uvM_matEq

theorem t320_three_φt :
    (StrothTypeIndex.t320 3 le_rfl).action.φt = StrothTypeIndex.t321.action.φt :=
  matAct_congr (k := Type321.k) _ _ t321_tM_matEq

theorem t320_three_φu :
    (StrothTypeIndex.t320 3 le_rfl).action.φu = StrothTypeIndex.t321.action.φu :=
  matAct_congr (k := Type321.k) _ _ t321_uM_matEq

theorem t320_three_φρ :
    (StrothTypeIndex.t320 3 le_rfl).action.φρ = StrothTypeIndex.t321.action.φρ :=
  matAct_congr (k := Type321.k) _ _ t321_ρM_matEq

@[expose] def StrothTypeData.t320OfT321 {S : Type*} [Group S] {B : Subgroup S}
    (D : StrothTypeData B StrothTypeIndex.t321) :
    StrothTypeData B (StrothTypeIndex.t320 3 le_rfl) where
  e := D.e
  uv := D.uv
  t := D.t
  u := D.u
  ρ := D.ρ
  uv_sq := D.uv_sq
  t_sq := D.t_sq
  uv_comm_t := D.uv_comm_t
  rho_cube := D.rho_cube
  u_sq := D.u_sq
  u_rho := D.u_rho
  uv_rho := D.uv_rho
  t_rho := D.t_rho
  uv_comm_u := D.uv_comm_u
  t_u := D.t_u
  uv_mem := D.uv_mem
  t_mem := D.t_mem
  u_mem := D.u_mem
  ρ_mem := D.ρ_mem
  uv_conj x := by rw [t320_three_φuv]; exact D.uv_conj x
  t_conj x := by rw [t320_three_φt]; exact D.t_conj x
  u_conj x := by rw [t320_three_φu]; exact D.u_conj x
  ρ_conj x := by rw [t320_three_φρ]; exact D.ρ_conj x

end CFSG.CGT.Stroth77
