
module

public import CFSG.Certificates.Kernel.L34Cov.AlphaGenSound
public import Certificates.Data.Kernel.L34Cov.Lift

public section

namespace CFSG.Certificates.L34Cov

open CFSG.KC CFSG.KC.L34Cov CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34
open CFSG.Certificates.CosetEnumeration CFSG.CosetTable CFSG.ComponentClassification.GrSLit.L34Facts
open Subgroup

theorem liftsOK_sound {V : ℕ} {TA TB : ℕ → ℕ}
    (hV : vtOK V = true) (hA : MonoModel TA 3 2) (hB : MonoModel TB 0 1)
    {uA uB : List (Fin 2 × Bool)} {L : List (List (Fin 2 × Bool) × List (Fin 2 × Bool) × ℕ)}
    (h : liftsOK V TA TB FW (uA.map letterCode) (uB.map letterCode) (liftCodes L) = true)
    {p w : List (Fin 2 × Bool)} {e : ℕ} (hx : (p, w, e) ∈ L) :
    cv (p ++ substWord (autWs uA uB) w) = z₁ ^ (e % 48 / 12) * z₂ ^ (e % 12 / 3) * z₃ ^ (e % 3) := by
  unfold liftsOK at h
  rw [bindB_eq, bindB_eq] at h
  generalize zvC V TA TB (invW (uA.map letterCode) ++
    substC [uA.map letterCode, uB.map letterCode] (FW.getD 0 [])) = vA at h
  generalize zvC V TA TB (invW (uB.map letterCode) ++
    substC [uA.map letterCode, uB.map letterCode] (FW.getD 1 [])) = vB at h
  simp only [andB_eq, Bool.and_eq_true] at h
  obtain ⟨hzA, hzB, hL⟩ := h
  have hU : [uA.map letterCode, uB.map letterCode] = [uA, uB].map (List.map letterCode) := rfl
  have eA : invW (uA.map letterCode) ++ substC [uA.map letterCode, uB.map letterCode]
      (FW.getD 0 []) = (FreeGroup.invRev uA ++ (autWs uA uB).getD 0 []).map letterCode := by
    rw [List.map_append, map_letterCode_invRev, FW_getD, hU, ← map_letterCode_substWord]
    rfl
  have eB : invW (uB.map letterCode) ++ substC [uA.map letterCode, uB.map letterCode]
      (FW.getD 1 []) = (FreeGroup.invRev uB ++ (autWs uA uB).getD 1 []).map letterCode := by
    rw [List.map_append, map_letterCode_invRev, FW_getD, hU, ← map_letterCode_substWord]
    rfl
  rw [eA] at hzA
  rw [eB] at hzB
  have zA := cv_of_zvOK hV hA hB hzA
  have zB := cv_of_zvOK hV hA hB hzB
  rw [cv_append, cv_invRev] at zA zB
  have hc0 : (cv ([uA, uB].getD 0 []))⁻¹ * cv ((autWs uA uB).getD 0 []) = zc vA := zA
  have hc1 : (cv ([uA, uB].getD 1 []))⁻¹ * cv ((autWs uA uB).getD 1 []) = zc vB := zB
  have hl : cv (substWord (autWs uA uB) w) =
      cv (substWord [uA, uB] w) * zc vA ^ expOf 0 w * zc vB ^ expOf 1 w := by
    rw [← lift_cv_getD (autWs uA uB) w, ← lift_cv_getD [uA, uB] w, ← hc0, ← hc1]
    exact lift_eq_corr _ _ (hc0 ▸ zc_mem_center vA) (hc1 ▸ zc_mem_center vB) w
  have hx' := List.all_eq_true.1 hL (p.map letterCode, w.map letterCode, e)
    (List.mem_map.2 ⟨_, hx, rfl⟩)
  unfold liftIdOK at hx'
  rw [hU, ← map_letterCode_substWord, ← List.map_append] at hx'
  have hid := cv_of_zvOK hV hA hB hx'
  rw [cv_append] at hid
  have e0 := eN_modEq 0 w
  have e1 := eN_modEq 1 w
  rw [Fin.val_zero] at e0
  rw [Fin.val_one] at e1
  have hcorr := corr_spec (e := e) (vA := vA) (vB := vB) e0 e1 (eN_le _ _) (eN_le _ _)
  rw [cv_append, hl]
  calc cv p * (cv (substWord [uA, uB] w) * zc vA ^ expOf 0 w * zc vB ^ expOf 1 w) =
      cv p * cv (substWord [uA, uB] w) * zc vA ^ expOf 0 w * zc vB ^ expOf 1 w := by
        simp only [mul_assoc]
    _ = _ := by rw [hid]; exact hcorr

end CFSG.Certificates.L34Cov

end
