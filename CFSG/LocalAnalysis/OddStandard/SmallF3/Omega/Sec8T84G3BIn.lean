module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G3BSd
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G3AB
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G3AC
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G3AF
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G3AQ
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F3Yb
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84E4Syl
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G}
  {E Y1 Y2 T T1 T2 V1 V2 F1 F2 : Subgroup G}

theorem sec8t84g3b_F2_e16 (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) : IsElemAb2 F2 4 := by
  rw [D.F2_eq]
  exact ⟨CFSG.Open.IsElemAbelian.map D.mod1.F_e16.1 _, by
    rw [Subgroup.card_map_of_injective (MulAut.conj t).injective, D.mod1.F_e16.2]⟩

theorem sec8t84g3b_sylow (h : Sec8T84GSet G t E Y1 Y2 T T1 T2 V1 V2 F1 F2) :
    IsSylow2Of T1 Y1 ∧ IsSylow2Of T2 Y2 := by
  have htT : t ∈ T := by
    rw [h.D.T_eq]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  obtain ⟨-, -, -, hS1, hS2, -⟩ := sec8t84_tstruct h.D.t_sq h.E8 h.XO.core h.T_syl htT
  exact ⟨by rw [h.T1_eq]; exact hS1, by rw [h.T2_eq]; exact hS2⟩

theorem sec8t84g3b_side1 (h : Sec8T84GSet G t E Y1 Y2 T T1 T2 V1 V2 F1 F2) :
    ∃ H : Subgroup G, Sec8T84G3BSide G E (F1 ⊔ F2) Y1 Y2 V1 V2 F1 F2 T1 H := by
  obtain ⟨hS1, -⟩ := sec8t84g3b_sylow h
  obtain ⟨H, hH⟩ := sec8t84_ydata1 h.E8 h.XO
  rw [← h.V1_eq] at hH
  have hmod := h.D.mod1
  have hF2T : F2 ≤ T2 := sec8t84g3a_F2_le_T2 h.D
  have hV2T : V2 ≤ T2 := sec8t84g3a_V2_le_T2 h.D
  have hT2Y : T2 ≤ Y2 := by rw [h.T2_eq]; exact inf_le_right
  have hT1T : T1 ≤ T := by rw [h.T1_eq]; exact inf_le_left
  have hV2E : V2 ≤ E := by rw [h.V2_eq]; exact inf_le_left
  refine ⟨H, ?_⟩
  exact
  { Y_le := h.XO.le1
    Y'_le := h.XO.le2
    ydata := hH
    P_syl := hS1
    F_le_P := hmod.F_le
    F_e16 := hmod.F_e16
    F_ne := hmod.F_ne
    F'_le := hF2T.trans hT2Y
    V_eq := h.V1_eq
    V'_eq := h.V2_eq
    E0_eq := rfl
    FF'_comm := fun f hf f' hf' => h.D.comm f (hmod.F_le hf) f' (hF2T hf')
    N_le' := h.XO.o_le2
    comm := h.XO.comm
    inf := h.XO.inf
    odd_mem := fun x hx hodd => sec8t84g3a_odd_mem_Y h.XO h.D.t_sq hx hodd
    cent' := by rw [h.V2_eq]; exact h.XO.cent2
    Y_cent' := fun y hy v hv => (sec8t84g3a_Y_cent_V h.E8 h.XO).2 y hy v
      (by rw [← h.V2_eq]; exact hv)
    N_cent' := fun v hv o ho => sec8t84_oddCore_cent h.E8 ho (hV2E hv)
    V'_sq := fun v hv => h.E8.1.mul_self_eq_one (hV2E hv)
    W_inf := sec8t84g3a_W_inf h
    O_eq := sec8t84g3a_O_eq h
    frattini := fun x hx hx0 => sec8t84g3a_frattini h hx hx0
    U_le_Q := (sup_le hmod.V_le hmod.F_le).trans (hT1T.trans (sec8t84g3a_T_le_Q h))
    UU'_comm := fun u hu u' hu' => h.D.comm u ((sup_le hmod.V_le hmod.F_le) hu) u'
      ((sup_le hV2T hF2T) hu') }

theorem sec8t84g3b_side2 (h : Sec8T84GSet G t E Y1 Y2 T T1 T2 V1 V2 F1 F2) :
    ∃ H : Subgroup G, Sec8T84G3BSide G E (F1 ⊔ F2) Y2 Y1 V2 V1 F2 F1 T2 H := by
  obtain ⟨-, hS2⟩ := sec8t84g3b_sylow h
  obtain ⟨H, hH⟩ := sec8t84_ydata2 h.E8 h.XO
  rw [← h.V2_eq] at hH
  have hmod := h.D.mod1
  have hF2T : F2 ≤ T2 := sec8t84g3a_F2_le_T2 h.D
  have hV2T : V2 ≤ T2 := sec8t84g3a_V2_le_T2 h.D
  have hT1Y : T1 ≤ Y1 := by rw [h.T1_eq]; exact inf_le_right
  have hT2T : T2 ≤ T := by rw [h.T2_eq]; exact inf_le_left
  have hV1E : V1 ≤ E := by rw [h.V1_eq]; exact inf_le_left
  refine ⟨H, ?_⟩
  exact
  { Y_le := h.XO.le2
    Y'_le := h.XO.le1
    ydata := hH
    P_syl := hS2
    F_le_P := hF2T
    F_e16 := sec8t84g3b_F2_e16 h.D
    F_ne := sec8t84g3a_F2_ne_V2 h.D
    F'_le := hmod.F_le.trans hT1Y
    V_eq := h.V2_eq
    V'_eq := h.V1_eq
    E0_eq := sup_comm F1 F2
    FF'_comm := fun f hf f' hf' => (h.D.comm f' (hmod.F_le hf') f (hF2T hf)).symm
    N_le' := h.XO.o_le1
    comm := fun a ha b hb => by
      have h1 := (oddCoreIn (normalizer (E : Set G))).inv_mem (h.XO.comm b hb a ha)
      have h2 : a * b * a⁻¹ * b⁻¹ = (b * a * b⁻¹ * a⁻¹)⁻¹ := by group
      rw [h2]
      exact h1
    inf := (inf_comm Y2 Y1).le.trans h.XO.inf
    odd_mem := fun x hx hodd => by
      obtain ⟨y1, hy1, y2, hy2, rfl⟩ := sec8t84g3a_odd_mem_Y h.XO h.D.t_sq hx hodd
      refine ⟨y1 * y2 * y1⁻¹, ?_, y1, hy1, by group⟩
      have h1 : y1 * y2 * y1⁻¹ = (y1 * y2 * y1⁻¹ * y2⁻¹) * y2 := by group
      rw [h1]
      exact Y2.mul_mem (h.XO.o_le2 (h.XO.comm y1 hy1 y2 hy2)) hy2
    cent' := by rw [h.V1_eq]; exact h.XO.cent1
    Y_cent' := fun y hy v hv => (sec8t84g3a_Y_cent_V h.E8 h.XO).1 y hy v
      (by rw [← h.V1_eq]; exact hv)
    N_cent' := fun v hv o ho => sec8t84_oddCore_cent h.E8 ho (hV1E hv)
    V'_sq := fun v hv => h.E8.1.mul_self_eq_one (hV1E hv)
    W_inf := sec8t84g3a_W_inf h
    O_eq := sec8t84g3a_O_eq h
    frattini := fun x hx hx0 => sec8t84g3a_frattini h hx hx0
    U_le_Q := (sup_le hV2T hF2T).trans (hT2T.trans (sec8t84g3a_T_le_Q h))
    UU'_comm := fun u hu u' hu' => (h.D.comm u' ((sup_le hmod.V_le hmod.F_le) hu') u
      ((sup_le hV2T hF2T) hu)).symm }

end CFSG.OddStandard.SmallF3.Omega
