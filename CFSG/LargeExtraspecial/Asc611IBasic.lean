module

public import CFSG.LargeExtraspecial.AS35LInvA
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LargeExtraspecial.Asc611I

open Subgroup Matrix CFSG.Fischer.Classification.Unitary CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Unitary CFSG.LargeExtraspecial.AS35L
open CFSG.Blueprint.Fischer (K)

variable {m : ℕ}

theorem invN_smul_of_comm {e g : SUid frob m} (hg : g * e = e * g) (x : Fin m → K) :
    invN e (g • x) = g • invN e x := by
  rw [invN_apply, invN_apply, smul_add, smul_smul, smul_smul, hg]

theorem herm_invN_smul_smul {e g : SUid frob m} (hg : g * e = e * g) (a b : Fin m → K) :
    herm frob (g • a) (invN e (g • b)) = herm frob a (invN e b) := by
  rw [invN_smul_of_comm hg, herm_smul_smul]

@[expose] noncomputable def cv (e : SUid frob m) (y : Fin m → K) : SUid frob m :=
  tvU y * tvU (e • y)

section Invol

variable {e : SUid frob m} (he : e * e = 1)
include he

omit he in
theorem herm_e_iso {y : Fin m → K} (hy : herm frob y y = 0) :
    herm frob (e • y) (e • y) = 0 := by
  rw [herm_smul_smul, hy]

omit he in
theorem herm_y_ey {y : Fin m → K} (hy : herm frob y y = 0)
    (hyN : herm frob y (invN e y) = 0) : herm frob y (e • y) = 0 := by
  rw [smul_eq_invN_add, herm_add_right, hyN, hy, add_zero]

omit he in
theorem tvU_comm_of_ker {v : Fin m → K} (hv : herm frob v v = 0) (hNv : invN e v = 0) :
    tvU v * e = e * tvU v := by
  have h1 := conj_tvU e hv
  rw [(invN_eq_zero_iff e v).mp hNv] at h1
  calc tvU v * e = e * tvU v * e⁻¹ * e := by rw [h1]
    _ = e * tvU v := by group

omit he in
theorem cv_smul {y : Fin m → K} (hy : herm frob y y = 0) (hyN : herm frob y (invN e y) = 0)
    (x : Fin m → K) :
    cv e y • x = x + herm frob y x • invN e y + herm frob (invN e y) x • y +
      herm frob (invN e y) x • invN e y := by
  have hey := herm_e_iso (e := e) hy
  have hyey := herm_y_ey hy hyN
  rw [cv, mul_smul, tvU_smul hey, tvU_smul hy, herm_add_right, herm_smul_right, hyey,
    mul_zero, add_zero, smul_eq_invN_add, herm_add_left]
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring_nf
  simp [two_eq_zero]

theorem cv_smul_ker {y : Fin m → K} (hy : herm frob y y = 0)
    (hyN : herm frob y (invN e y) = 0) {v : Fin m → K} (hv : invN e v = 0) :
    cv e y • v = v + herm frob y v • invN e y := by
  rw [cv_smul hy hyN, herm_invN_left he, hv, herm_zero_right, zero_smul, zero_smul,
    add_zero, add_zero]

omit he in
theorem cv_mul_self {y : Fin m → K} (hy : herm frob y y = 0)
    (hyN : herm frob y (invN e y) = 0) : cv e y * cv e y = 1 := by
  have hey := herm_e_iso (e := e) hy
  have hc := tvU_commute hy hey (herm_y_ey hy hyN)
  rw [cv, show tvU y * tvU (e • y) * (tvU y * tvU (e • y)) =
      tvU y * (tvU (e • y) * tvU y) * tvU (e • y) by group, ← hc,
    show tvU y * (tvU y * tvU (e • y)) * tvU (e • y) =
      (tvU y * tvU y) * (tvU (e • y) * tvU (e • y)) by group,
    tvU_mul_self hy, tvU_mul_self hey, one_mul]

omit he in
theorem cv_inv {y : Fin m → K} (hy : herm frob y y = 0)
    (hyN : herm frob y (invN e y) = 0) : (cv e y)⁻¹ = cv e y :=
  inv_eq_of_mul_eq_one_right (cv_mul_self hy hyN)

theorem cv_comm {y : Fin m → K} (hy : herm frob y y = 0)
    (hyN : herm frob y (invN e y) = 0) : cv e y * e = e * cv e y := by
  have hey := herm_e_iso (e := e) hy
  have h1 : e * tvU y = tvU (e • y) * e := by
    rw [← conj_tvU e hy, inv_mul_cancel_right]
  have h2 : e * tvU (e • y) = tvU y * e := by
    have := conj_tvU e hey
    rw [smul_smul_self he] at this
    rw [← this, inv_mul_cancel_right]
  have hc := tvU_commute hy hey (herm_y_ey hy hyN)
  rw [cv]
  calc tvU y * tvU (e • y) * e = tvU (e • y) * tvU y * e := by rw [hc]
    _ = tvU (e • y) * (tvU y * e) := by group
    _ = tvU (e • y) * (e * tvU (e • y)) := by rw [← h2]
    _ = (tvU (e • y) * e) * tvU (e • y) := by group
    _ = (e * tvU y) * tvU (e • y) := by rw [h1]
    _ = e * (tvU y * tvU (e • y)) := by group

end Invol

theorem conj_cv {e g : SUid frob m} (hg : g * e = e * g) {y : Fin m → K}
    (hy : herm frob y y = 0) (hey : herm frob (e • y) (e • y) = 0) :
    g * cv e y * g⁻¹ = cv e (g • y) := by
  rw [cv, cv, show g * (tvU y * tvU (e • y)) * g⁻¹ =
      (g * tvU y * g⁻¹) * (g * tvU (e • y) * g⁻¹) by group, conj_tvU g hy, conj_tvU g hey,
    smul_smul, smul_smul, hg]

end CFSG.LargeExtraspecial.Asc611I
