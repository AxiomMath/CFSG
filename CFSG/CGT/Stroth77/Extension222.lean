module

public import CFSG.CGT.Stroth77.Extension25Common
public import CFSG.CGT.Stroth77.TorusNormalForm

public section

namespace CFSG.CGT.Stroth77

open Matrix

theorem t331_k_pos (i : Fin 3) : 1 ≤ Type331.k i := by
  fin_cases i <;> simp [Type331.k]

theorem parityTorus_rho_t331 (y : Torus StrothTypeIndex.t331.k) :
    parityTorus _ t331_k_pos (StrothTypeIndex.t331.action.φρ y) =
      rhoBar300 (parityTorus _ t331_k_pos y) := by
  change parityTorus Type331.k t331_k_pos (matAct Type331.k Type331.ρM Type331.compat_rho y) =
    rhoBar300 (parityTorus Type331.k t331_k_pos y)
  obtain ⟨v, hv⟩ := Torus.exists_ofInt (k := Type331.k) y
  rw [← hv, matAct_ofInt, Torus.ofInt_eq_zsmul_gens, Torus.ofInt_eq_zsmul_gens,
    parityTorus_zsmul_gens, parityTorus_zsmul_gens]
  have h4 : (4 : ZMod 2) = 0 := by decide
  funext r
  fin_cases r <;> simp [rhoBar300, Type331.ρM, ofCols_mulVec, h4, sub_eq_add_neg,
    ZMod.neg_eq_self_mod_two]

theorem parityTorus_uv_c_sub_t331 :
    parityTorus _ t331_k_pos (StrothTypeIndex.t331.action.φuv Torus.c - Torus.c) =
      ![0, 1, 1] := by
  change parityTorus Type331.k t331_k_pos
    (matAct Type331.k Type331.uvM Type331.compat_uv (Torus.c : Torus Type331.k) -
      (Torus.c : Torus Type331.k)) = ![0, 1, 1]
  have hc : (Torus.c : Torus Type331.k) = Torus.ofInt Type331.k ![1, 0, 0] := by
    rw [Torus.ofInt_eq_zsmul_gens]
    simp
  rw [hc, matAct_ofInt, ← Torus.ofInt_sub, Torus.ofInt_eq_zsmul_gens, parityTorus_zsmul_gens]
  have h4 : (4 : ZMod 2) = 0 := by decide
  have h5 : (5 : ZMod 2) = 1 := by decide
  funext r
  fin_cases r <;> simp [Type331.uvM, Type331.uvA, Type331.tM, Type331.ρM, ofCols_mulVec, h4, h5,
    ZMod.neg_eq_self_mod_two]

theorem false_of_index_two_t331_of_data {S : Type*} [Group S] [Finite S] {B C S' : Subgroup S}
    (D : StrothTypeData B StrothTypeIndex.t331)
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') : False := by
  obtain ⟨zuv, -, h1, -, -, -⟩ := exists_cocycle_index_two_of_data_Idx4 D t331_k_pos
    parityTorus_rho_t331 (fun v h1 h2 => rhoBar300_fixed_check v ⟨h1, h2⟩) hBC hC hrel hL hH hcS
  have h0 : parityTorus _ t331_k_pos (StrothTypeIndex.t331.action.φuv Torus.c - Torus.c) = 0 :=
    (parityTorus_eq_zero_iff t331_k_pos _).mpr ⟨zuv, h1⟩
  rw [parityTorus_uv_c_sub_t331] at h0
  exact absurd (congrFun h0 1) (by decide)

theorem t331_uvM_matEq :
    MatEq Type331.k
      (Type330.uvM (Type120.iV 3) (Type120.FV 3) (Type120.GV 3) (2 ^ (3 - 1))) Type331.uvM := by
  refine MatEq.of_witness (W := !![-5, 451, -45088; 0, -27, -8723; 0, 10, -1103]) ?_
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp [Type120.iV, Type120.FV, Type120.GV, Type330.uvM, Type330.uvA, Type330.tM, Type330.ρM,
      Type331.uvM, Type331.uvA, Type331.tM, Type331.ρM, Type331.k, ofCols_mulVec, ofCols_apply]

theorem t331_tM_matEq :
    MatEq Type331.k
      (Type330.tM (Type120.iV 3) (Type120.FV 3) (Type120.GV 3) (2 ^ (3 - 1))) Type331.tM := by
  refine MatEq.of_witness (W := !![-5, 129, 405; 0, -38, -10; 1, -43, -37]) ?_
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp [Type120.iV, Type120.FV, Type120.GV, Type330.uvA, Type330.tM, Type330.ρM,
      Type331.uvA, Type331.tM, Type331.ρM, Type331.k, ofCols_mulVec, ofCols_apply]

theorem t331_uM_matEq :
    MatEq Type331.k (Type330.uM (Type120.FV 3) (2 ^ (3 - 1))) Type331.uM := by
  refine MatEq.of_witness (W := !![0, -21, 63; 0, 0, 0; 0, 0, 0]) ?_
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp [Type120.FV, Type330.uM, Type331.uM, uMat, Type331.k, ofCols_apply]

theorem t331_ρM_matEq : MatEq Type331.k Type330.ρM Type331.ρM := by
  refine MatEq.of_witness (W := !![0, 0, -1; 0, 0, 0; 0, 0, 0]) ?_
  intro r c
  fin_cases r <;> fin_cases c <;> simp [Type330.ρM, Type331.ρM, Type331.k, ofCols_apply]

theorem t330_three_φuv :
    (StrothTypeIndex.t330 3 le_rfl).action.φuv = StrothTypeIndex.t331.action.φuv :=
  matAct_congr (k := Type331.k) _ _ t331_uvM_matEq

theorem t330_three_φt :
    (StrothTypeIndex.t330 3 le_rfl).action.φt = StrothTypeIndex.t331.action.φt :=
  matAct_congr (k := Type331.k) _ _ t331_tM_matEq

theorem t330_three_φu :
    (StrothTypeIndex.t330 3 le_rfl).action.φu = StrothTypeIndex.t331.action.φu :=
  matAct_congr (k := Type331.k) _ _ t331_uM_matEq

theorem t330_three_φρ :
    (StrothTypeIndex.t330 3 le_rfl).action.φρ = StrothTypeIndex.t331.action.φρ :=
  matAct_congr (k := Type331.k) _ _ t331_ρM_matEq

@[expose] def StrothTypeData.t330OfT331 {S : Type*} [Group S] {B : Subgroup S}
    (D : StrothTypeData B StrothTypeIndex.t331) :
    StrothTypeData B (StrothTypeIndex.t330 3 le_rfl) where
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
  uv_conj x := by rw [t330_three_φuv]; exact D.uv_conj x
  t_conj x := by rw [t330_three_φt]; exact D.t_conj x
  u_conj x := by rw [t330_three_φu]; exact D.u_conj x
  ρ_conj x := by rw [t330_three_φρ]; exact D.ρ_conj x

theorem StrothTypeData.t330OfT331_L {S : Type*} [Group S] {B : Subgroup S}
    (D : StrothTypeData B StrothTypeIndex.t331) : D.t330OfT331.L = D.L := rfl

end CFSG.CGT.Stroth77
