module

public import CFSG.CGT.Stroth77.Section47CoreX

public section

namespace CFSG.CGT.Stroth77

open Matrix Stroth42Core Stroth34T200 Stroth47Core

namespace StrothWeakTypeData

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ}
  (dD : StrothWeakTypeData D (.t200 m)) {e f : G} {p : ℕ}

theorem t200k_f_conj_ofTorus (hrel : Rel34inv dD f 0 1 p) (v : Torus (StrothTypeIndex.t200 m).k) :
    f⁻¹ * dD.ofTorus v * f = dD.ofTorus (torusDiag _ ![-1, -1, -1] v) :=
  dD.conj_ofTorus_of_gens
    (by rw [hrel.c_conj, torusDiag_gen, ofTorus_zsmul, ← c_eq]; simp)
    (by rw [hrel.a_conj, torusDiag_gen, ofTorus_zsmul, ← a_eq]; simp)
    (by rw [hrel.b_conj, torusDiag_gen, ofTorus_zsmul, ← b_eq]; simp) v

@[expose] def t200fEAction (hrel : Rel34inv dD f 0 1 p) : dD.EAction f where
  φe := torusDiag _ ![-1, -1, -1]
  wuv := Torus.ofInt _ ![(p : ℤ), p, p]
  wt := Torus.ofInt _ ![0, -(p : ℤ), 0]
  ve := 0
  conj_ofTorus := dD.t200k_f_conj_ofTorus hrel
  conj_uv := by rw [hrel.uv_conj, dD.t200x_cab_pow]
  conj_t := by rw [hrel.t_conj, dD.t200x_a_pow_inv]
  conj_u := hrel.u_conj
  mul_self := by rw [hrel.e_sq, dD.ofTorus_zero]

theorem t200fEAction_φe (hrel : Rel34inv dD f 0 1 p) :
    (dD.t200fEAction hrel).φe = torusDiag _ ![-1, -1, -1] := rfl

theorem t200fEAction_ve (hrel : Rel34inv dD f 0 1 p) : (dD.t200fEAction hrel).ve = 0 := rfl

theorem t200fEAction_wuv (hrel : Rel34inv dD f 0 1 p) :
    (dD.t200fEAction hrel).wuv = Torus.ofInt _ ![(p : ℤ), p, p] := rfl

theorem t200fEAction_wt (hrel : Rel34inv dD f 0 1 p) :
    (dD.t200fEAction hrel).wt = Torus.ofInt _ ![0, -(p : ℤ), 0] := rfl

theorem t200k_g_conj_ofTorus (hrel_e : Rel34i dD e (2 ^ (m + 1))) (hrel_f : Rel34inv dD f 0 1 p)
    (v : Torus (StrothTypeIndex.t200 m).k) :
    (f * e)⁻¹ * dD.ofTorus v * (f * e) =
      dD.ofTorus ((torusDiag _ ![1, 1 + 2 ^ (m + 1), 1 + 2 ^ (m + 1)]).comp
        (torusDiag _ ![-1, -1, -1]) v) := by
  rw [show (f * e)⁻¹ * dD.ofTorus v * (f * e) = e⁻¹ * (f⁻¹ * dD.ofTorus v * f) * e by group,
    dD.t200k_f_conj_ofTorus hrel_f, (dD.t200iAction hrel_e).conj_ofTorus, t200iAction_φe]
  rfl

theorem t200k_g_conj_uv (hrel_e : Rel34i dD e (2 ^ (m + 1))) (hrel_f : Rel34inv dD f 0 1 p) :
    (f * e)⁻¹ * dD.uv * (f * e) = dD.ofTorus (Torus.ofInt _
      ![(p : ℤ) + 2, p + 2 + p * 2 ^ (m + 1), p + 2 + p * 2 ^ (m + 1)]) * dD.uv := by
  rw [show (f * e)⁻¹ * dD.uv * (f * e) = e⁻¹ * (f⁻¹ * dD.uv * f) * e by group, hrel_f.uv_conj,
    show e⁻¹ * (((dD.c : G) * dD.a * dD.b) ^ p * dD.uv) * e =
      e⁻¹ * ((dD.c : G) * dD.a * dD.b) ^ p * e * (e⁻¹ * dD.uv * e) by group,
    hrel_e.uv_conj, dD.t200x_cab_pow, dD.t200x_cab_pow, (dD.t200iAction hrel_e).conj_ofTorus,
    t200iAction_φe, ← mul_assoc, ← dD.ofTorus_add, torusDiag_ofInt, ← Torus.ofInt_add]
  congr 3
  funext i
  fin_cases i <;> simp <;> ring

theorem t200k_g_conj_t (hrel_e : Rel34i dD e (2 ^ (m + 1))) (hrel_f : Rel34inv dD f 0 1 p) :
    (f * e)⁻¹ * dD.t * (f * e) = dD.ofTorus (Torus.ofInt _
      ![0, -((p : ℤ) * (1 + 2 ^ (m + 1))) - 2, 0]) * dD.t := by
  rw [show (f * e)⁻¹ * dD.t * (f * e) = e⁻¹ * (f⁻¹ * dD.t * f) * e by group, hrel_f.t_conj,
    show e⁻¹ * (((dD.a : G) ^ p)⁻¹ * dD.t) * e =
      e⁻¹ * ((dD.a : G) ^ p)⁻¹ * e * (e⁻¹ * dD.t * e) by group,
    hrel_e.t_conj, dD.t200x_a_pow_inv, dD.t200x_a_pow_inv, (dD.t200iAction hrel_e).conj_ofTorus,
    t200iAction_φe, ← mul_assoc, ← dD.ofTorus_add, torusDiag_ofInt, ← Torus.ofInt_add]
  congr 3
  funext i
  fin_cases i <;> simp <;> ring

theorem t200k_e_comm_c₁ (hrel_e : Rel34i dD e (2 ^ (m + 1))) :
    e * (dD.c : G) ^ 2 ^ (m - 1) = (dD.c : G) ^ 2 ^ (m - 1) * e := by
  have hec : Commute e (dD.c : G) := by
    show e * (dD.c : G) = (dD.c : G) * e
    calc e * (dD.c : G) = e * (e⁻¹ * (dD.c : G) * e) := by rw [hrel_e.c_conj]
      _ = (dD.c : G) * e := by group
  exact (hec.pow_right _).eq

theorem t200k_g_mul_self (hrel_e : Rel34i dD e (2 ^ (m + 1))) (hrel_f : Rel34inv dD f 0 1 p)
    (hconj : f⁻¹ * e * f = e⁻¹ * (dD.c : G) ^ 2 ^ (m - 1)) :
    f * e * (f * e) = dD.ofTorus (Torus.ofInt _ ![2 ^ (m - 1), 0, 0]) := by
  have hfinv : f⁻¹ = f := inv_eq_of_mul_eq_one_right hrel_f.e_sq
  have h1 : f * e * (f * e) = f⁻¹ * e * f * e := by rw [hfinv]; group
  rw [h1, hconj, mul_assoc, ← dD.t200k_e_comm_c₁ hrel_e, ← mul_assoc, inv_mul_cancel, one_mul,
    dD.t200_c_pow, om200_apply]
  congr 2
  funext i
  fin_cases i <;> simp

@[expose] def t200gEAction (hrel_e : Rel34i dD e (2 ^ (m + 1))) (hrel_f : Rel34inv dD f 0 1 p)
    (hconj : f⁻¹ * e * f = e⁻¹ * (dD.c : G) ^ 2 ^ (m - 1)) : dD.EAction (f * e) where
  φe := (torusDiag _ ![1, 1 + 2 ^ (m + 1), 1 + 2 ^ (m + 1)]).comp (torusDiag _ ![-1, -1, -1])
  wuv := Torus.ofInt _ ![(p : ℤ) + 2, p + 2 + p * 2 ^ (m + 1), p + 2 + p * 2 ^ (m + 1)]
  wt := Torus.ofInt _ ![0, -((p : ℤ) * (1 + 2 ^ (m + 1))) - 2, 0]
  ve := Torus.ofInt _ ![2 ^ (m - 1), 0, 0]
  conj_ofTorus := dD.t200k_g_conj_ofTorus hrel_e hrel_f
  conj_uv := dD.t200k_g_conj_uv hrel_e hrel_f
  conj_t := dD.t200k_g_conj_t hrel_e hrel_f
  conj_u := by
    rw [show (f * e)⁻¹ * dD.u * (f * e) = e⁻¹ * (f⁻¹ * dD.u * f) * e by group, hrel_f.u_conj,
      hrel_e.u_conj]
  mul_self := dD.t200k_g_mul_self hrel_e hrel_f hconj

theorem t200gEAction_φe_apply (hrel_e : Rel34i dD e (2 ^ (m + 1))) (hrel_f : Rel34inv dD f 0 1 p)
    (hconj : f⁻¹ * e * f = e⁻¹ * (dD.c : G) ^ 2 ^ (m - 1)) (x : Fin 3 → ℤ) :
    (dD.t200gEAction hrel_e hrel_f hconj).φe (Torus.ofInt _ x) =
      Torus.ofInt _ ![-x 0, -((1 + 2 ^ (m + 1)) * x 1), -((1 + 2 ^ (m + 1)) * x 2)] := by
  show torusDiag _ _ (torusDiag _ _ _) = _
  rw [torusDiag_ofInt, torusDiag_ofInt]
  congr 1
  funext i
  fin_cases i <;> simp

theorem t200gEAction_ve (hrel_e : Rel34i dD e (2 ^ (m + 1))) (hrel_f : Rel34inv dD f 0 1 p)
    (hconj : f⁻¹ * e * f = e⁻¹ * (dD.c : G) ^ 2 ^ (m - 1)) :
    (dD.t200gEAction hrel_e hrel_f hconj).ve = Torus.ofInt _ ![2 ^ (m - 1), 0, 0] := rfl

theorem t200gEAction_wuv (hrel_e : Rel34i dD e (2 ^ (m + 1))) (hrel_f : Rel34inv dD f 0 1 p)
    (hconj : f⁻¹ * e * f = e⁻¹ * (dD.c : G) ^ 2 ^ (m - 1)) :
    (dD.t200gEAction hrel_e hrel_f hconj).wuv =
      Torus.ofInt _ ![(p : ℤ) + 2, p + 2 + p * 2 ^ (m + 1), p + 2 + p * 2 ^ (m + 1)] := rfl

theorem t200gEAction_wt (hrel_e : Rel34i dD e (2 ^ (m + 1))) (hrel_f : Rel34inv dD f 0 1 p)
    (hconj : f⁻¹ * e * f = e⁻¹ * (dD.c : G) ^ 2 ^ (m - 1)) :
    (dD.t200gEAction hrel_e hrel_f hconj).wt =
      Torus.ofInt _ ![0, -((p : ℤ) * (1 + 2 ^ (m + 1))) - 2, 0] := rfl

end StrothWeakTypeData

end CFSG.CGT.Stroth77
