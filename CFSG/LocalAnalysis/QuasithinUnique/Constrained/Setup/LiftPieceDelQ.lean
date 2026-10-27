module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceDelTools
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelDecomp

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Lift.PieceDel
open scoped commutatorElement

theorem delQProp : DelQProp := by
  intro G _ _ R M V n F _ r Lc ctx i Fs P hcore hbase hseed hH0 hmin hbasic himage hW hres had
  classical
  have hX := ctx.hX
  have hS := ctx.setting
  have hQn : (pCoreOf 2 (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R)).Normal :=
    normal_Q hcore.normal
  have hSP : baum R ≤ P := hbasic.lt.le
  have hQP : pCoreOf 2 (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R) ≤ P :=
    hbase.base.Q_le_S.trans hSP
  have hQO : pCoreOf 2 (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R) ≤ pCoreOf 2 P :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQP
      (by rw [Subgroup.normalizer_eq_top_iff.mpr hQn]; exact le_top)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  have hBV : oddOrderSubgroup P ≤ Subgroup.normalizer (V : Set G) := le_top.trans hX
  have hVQ : V ≤ pCoreOf 2 (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R) := hbase.base.V_le_Q
  have hWV : modComm V Fs ≤ V := modComm_le_V V Fs
  have hle : ⁅pCoreOf 2 (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R), oddOrderSubgroup P⁆ ≤
      modComm V Fs := by
    rw [← had.core.2]
    exact Subgroup.commutator_mono hQO le_rfl
  have hWB : modComm V Fs = ⁅oddOrderSubgroup P, V⁆ := by
    rw [← hres.image]
    exact Piece.modComm_autOn hBV
  have hge : modComm V Fs ≤
      ⁅pCoreOf 2 (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R), oddOrderSubgroup P⁆ := by
    rw [hWB, Subgroup.commutator_comm (oddOrderSubgroup P) V]
    exact Subgroup.commutator_mono hVQ le_rfl
  have hcomm : ⁅pCoreOf 2 (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R), oddOrderSubgroup P⁆ =
      modComm V Fs := le_antisymm hle hge
  refine ⟨hcomm, ?_, ?_⟩
  ·
    refine le_omegaOneCenterOf_of_le (hWV.trans hVQ) ?_ fun v hv => hS.reduced.2.2.1.2 v (hWV hv)
    intro q hq
    have hq' : q ∈ baum R ⊓ Subgroup.centralizer (V : Set G) := by
      rw [← hbase.Q_eq]
      exact hq
    refine Subgroup.mem_centralizer_iff.2 fun w hw => ?_
    exact Subgroup.mem_centralizer_iff.1 hq'.2 w (hWV hw)
  ·
    have hWB' : modComm V Fs ≤ oddOrderSubgroup P := by
      rw [← had.core.1]
      exact CFSG.LieType.BorelTits.pCoreOf_le 2 _
    have key : ∀ q ∈ pCoreOf 2 (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R),
        ∀ b ∈ oddOrderSubgroup P, q * b * q⁻¹ ∈ oddOrderSubgroup P := by
      intro q hq b hb
      have h1 : ⁅q, b⁆ ∈
          ⁅pCoreOf 2 (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R), oddOrderSubgroup P⁆ :=
        Subgroup.commutator_mem_commutator hq hb
      rw [hcomm] at h1
      have : q * b * q⁻¹ = ⁅q, b⁆ * b := by simp [commutatorElement_def, mul_assoc]
      rw [this]
      exact (oddOrderSubgroup P).mul_mem (hWB' h1) hb
    intro q hq
    rw [Subgroup.mem_normalizer_iff]
    intro b
    exact ⟨key q hq b, fun hb => by
      simpa [mul_assoc] using key q⁻¹ (Subgroup.inv_mem _ hq) _ hb⟩

end CFSG.QuasithinUnique.Setup.Lift
