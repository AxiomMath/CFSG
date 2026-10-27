module

public import CFSG.CGT.Stroth77.Section47Core
public import CFSG.CGT.Stroth77.Section43CoreE
public import CFSG.CGT.Stroth77.Stroth34T200Normal
public import CFSG.CGT.Stroth77.Stroth34Defs

public section

namespace CFSG.CGT.Stroth77

open Matrix Stroth42Core Stroth34T200 Stroth47Core

namespace StrothWeakTypeData

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ}
  (dD : StrothWeakTypeData D (.t200 m)) {e : G}

theorem t200_ofTorus_ofInt3 (x0 x1 x2 : ℤ) :
    dD.ofTorus (Torus.ofInt _ ![x0, x1, x2]) =
      (dD.c : G) ^ x0 * (dD.a : G) ^ x1 * (dD.b : G) ^ x2 :=
  dD.ofTorus_ofInt _

@[expose] def t200EAction
    (φe : Torus (StrothTypeIndex.t200 m).k →+ Torus (StrothTypeIndex.t200 m).k)
    (ve : Torus (StrothTypeIndex.t200 m).k)
    (hφe : ∀ v, e⁻¹ * dD.ofTorus v * e = dD.ofTorus (φe v))
    (heuv : e⁻¹ * dD.uv * e = ((dD.c : G) * dD.a * dD.b) ^ 2 * dD.uv)
    (het : e⁻¹ * dD.t * e = ((dD.a : G) ^ 2)⁻¹ * dD.t) (heu : e⁻¹ * dD.u * e = dD.u)
    (he : e * e = dD.ofTorus ve) : dD.EAction e where
  φe := φe
  wuv := Torus.ofInt _ ![2, 2, 2]
  wt := Torus.ofInt _ ![0, -2, 0]
  ve := ve
  conj_ofTorus := hφe
  conj_uv := by
    rw [heuv, dD.c_eq, dD.a_eq, dD.b_eq, ← dD.ofTorus_add, ← dD.ofTorus_add, ← dD.ofTorus_nsmul,
      c_eq_ofInt, a_eq_ofInt, b_eq_ofInt, t200_add_vec, t200_add_vec, ← natCast_zsmul,
      t200_zsmul_vec]
    norm_num
  conj_t := by
    rw [het, dD.a_eq, ← dD.ofTorus_nsmul, ← dD.ofTorus_neg, a_eq_ofInt, ← natCast_zsmul,
      t200_zsmul_vec, t200_neg_vec]
    norm_num
  conj_u := heu
  mul_self := he

@[expose] def t200iAction (hrel : Rel34i dD e (2 ^ (m + 1))) : dD.EAction e :=
  dD.t200EAction (torusDiag _ ![1, 1 + 2 ^ (m + 1), 1 + 2 ^ (m + 1)])
    (Torus.ofInt _ ![-1, 0, 0])
    (dD.conj_ofTorus_of_gens
      (by rw [hrel.c_conj, torusDiag_gen, ofTorus_zsmul, ← c_eq]; simp)
      (by
        rw [hrel.a_conj, torusDiag_gen, ofTorus_zsmul, ← a_eq,
          show (![1, 1 + 2 ^ (m + 1), 1 + 2 ^ (m + 1)] : Fin 3 → ℤ) 1 = 1 + 2 ^ (m + 1) from rfl,
          _root_.zpow_add, zpow_one,
          show ((2 : ℤ) ^ (m + 1)) = ((2 ^ (m + 1) : ℕ) : ℤ) by push_cast; rfl, zpow_natCast])
      (by
        rw [hrel.b_conj, torusDiag_gen, ofTorus_zsmul, ← b_eq,
          show (![1, 1 + 2 ^ (m + 1), 1 + 2 ^ (m + 1)] : Fin 3 → ℤ) 2 = 1 + 2 ^ (m + 1) from rfl,
          _root_.zpow_add, zpow_one,
          show ((2 : ℤ) ^ (m + 1)) = ((2 ^ (m + 1) : ℕ) : ℤ) by push_cast; rfl, zpow_natCast]))
    hrel.uv_conj hrel.t_conj hrel.u_conj
    (by
      rw [hrel.e_sq, dD.ofTorus_ofInt]
      simp)

theorem t200iAction_φe (hrel : Rel34i dD e (2 ^ (m + 1))) :
    (dD.t200iAction hrel).φe = torusDiag _ ![1, 1 + 2 ^ (m + 1), 1 + 2 ^ (m + 1)] := rfl

theorem t200iAction_ve (hrel : Rel34i dD e (2 ^ (m + 1))) :
    (dD.t200iAction hrel).ve = Torus.ofInt _ ![-1, 0, 0] := rfl

theorem t200iAction_wuv (hrel : Rel34i dD e (2 ^ (m + 1))) :
    (dD.t200iAction hrel).wuv = Torus.ofInt _ ![2, 2, 2] := rfl

theorem t200iAction_wt (hrel : Rel34i dD e (2 ^ (m + 1))) :
    (dD.t200iAction hrel).wt = Torus.ofInt _ ![0, -2, 0] := rfl

end StrothWeakTypeData

namespace Stroth47Core

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ}
  (dD : StrothWeakTypeData D (.t200 m)) {e : G}

open StrothWeakTypeData in
theorem t200_i_sqE_ne_zero (hm : 1 ≤ m) (hrel : Rel34i dD e (2 ^ (m + 1))) (x0 x1 x2 : ℤ)
    {i j l : Bool} (hlj : (l && j) = false) :
    (dD.t200iAction hrel).sqE (Torus.ofInt _ ![x0, x1, x2]) i j l ≠ 0 := by
  intro h
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hP : (2 : ℤ) ^ (m' + 2) ≠ 0 := pow_ne_zero _ two_ne_zero
  simp only [EAction.sqE, EAction.twist, t200iAction_φe, t200iAction_ve, t200iAction_wuv,
    t200iAction_wt] at h
  cases i <;> cases j <;> cases l <;> simp only [Bool.and_true, Bool.and_false] at hlj <;>
  (try exact absurd hlj (by decide)) <;>
  simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
    AddMonoidHom.id_apply, Bool.and_false, Bool.and_true, map_add, map_sub, map_zero,
    torusDiag_ofInt, t200_φuv, t200_φt, t200_φu, ← Torus.ofInt_add, ← Torus.ofInt_sub,
    add_zero, zero_add, t200_ofInt_eq_zero_iff, Pi.add_apply, Pi.sub_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h <;>
  obtain ⟨⟨k0, hk0⟩, ⟨k1, hk1⟩, ⟨k2, hk2⟩⟩ := h
  ·
    have : (2 : ℤ) * (x0 - 2 ^ m' * k0) = 1 := by linear_combination hk0
    omega
  ·
    have : (2 : ℤ) * (x0 - 2 ^ m' * k0) = 1 := by linear_combination hk0
    omega
  ·
    have hx2 : x2 = -2 * k2 := mul_left_cancel₀ hP (by linear_combination -hk2)
    subst hx2
    have : (2 : ℤ) * (x0 + k2 + 2 ^ (m' + 2) * k2 - 2 ^ m' * k0) = 1 := by linear_combination hk0
    omega
  ·
    have hd : x2 = x1 + 2 * (k1 - k2) := mul_left_cancel₀ hP (by linear_combination hk1 - hk2)
    have : (2 : ℤ) * (2 ^ (m' + 1) * (x1 + x2) - 8 * 2 ^ (m' + 1) - x0 + x1 + (k1 - k2) -
        2 ^ m' * k0) + 1 = 0 := by linear_combination hk0 - hd
    omega
  ·
    have h' : (2 : ℤ) * ((2 ^ (m' + 1) + 1) * (x1 - x2)) = 2 * (2 ^ (m' + 2) * (k1 - k2)) := by
      linear_combination hk1 - hk2
    have h'' := mul_left_cancel₀ two_ne_zero h'
    have hd : x1 - x2 = 2 * (2 ^ (m' + 1) * (k1 - k2) - 2 ^ m' * (x1 - x2)) := by
      linear_combination h''
    have : (2 : ℤ) * (2 ^ (m' + 1) * (x1 + x2) - 8 * 2 ^ (m' + 1) - x0 + x2 +
        (2 ^ (m' + 1) * (k1 - k2) - 2 ^ m' * (x1 - x2)) - 2 ^ m' * k0) + 1 = 0 := by
      linear_combination hk0 - hd
    omega
  ·
    have hx1 : x1 = -2 * k1 := mul_left_cancel₀ hP (by linear_combination -hk1)
    subst hx1
    have : (2 : ℤ) * (x0 + k1 + 2 ^ (m' + 2) * k1 - 2 ^ m' * k0) = 1 := by linear_combination hk0
    omega

open StrothWeakTypeData in
theorem t200_i_h6' (hm : 1 ≤ m) (hrel : Rel34i dD e (2 ^ (m + 1))) :
    ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
      y ∉ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} → y * y ≠ 1 := by
  intro y hy hyU hyy
  obtain ⟨v, i, j, l, k, rfl⟩ := (dD.t200iAction hrel).mem_sup_zpowers_iff.mp hy
  cases k
  · exact hyU (by simpa [bpow] using dD.nf_mem v i j l)
  · simp only [bpow, ↓reduceIte] at hyy
    rw [(dD.t200iAction hrel).nfe_e_mul_self] at hyy
    obtain ⟨x0, x1, x2, rfl⟩ := t200_exists_vec v
    cases hlj : l && j
    · rw [hlj, d8_fff, mul_one, ofTorus_eq_one_iff] at hyy
      exact t200_i_sqE_ne_zero dD hm hrel x0 x1 x2 hlj hyy
    · rw [hlj] at hyy
      exact dD.d8_not_mem (t200_faithful hm) (i := true) (j := false) (l := false) (by decide) _
        (by rw [hyy]; exact one_mem _)

theorem t200_i_φe_om (hm : 1 ≤ m) (ε : Fin 3 → ℤ) :
    torusDiag (StrothTypeIndex.t200 m).k ![1, 1 + 2 ^ (m + 1), 1 + 2 ^ (m + 1)] (om200 m ε) =
      om200 m ε := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [om200_succ, torusDiag_ofInt, t200_ofInt_eq_iff]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  refine ⟨⟨0, by ring⟩, ⟨-(2 ^ (m' + 1) * ε 1), by ring⟩, ⟨-(2 ^ (m' + 1) * ε 2), by ring⟩⟩

open StrothWeakTypeData in
theorem t200_i_not_word (hm : 1 ≤ m) (hrel : Rel34i dD e (2 ^ (m + 1))) (i j l : Bool)
    (h : ∀ v, (dD.t200iAction hrel).φe v = (StrothTypeIndex.t200 m).action.d8Act i j l v) :
    False := by
  have hc := h (om200 m ![1, 0, 0])
  have ha := h (om200 m ![0, 1, 0])
  rw [t200iAction_φe, t200_i_φe_om hm] at hc ha
  obtain ⟨rfl, rfl, rfl⟩ := t200_faithful_om hm i j l hc.symm ha.symm
  have h1 := h (Torus.ofInt _ ![0, 1, 0])
  rw [t200iAction_φe, torusDiag_ofInt] at h1
  simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
    AddMonoidHom.id_apply, t200_ofInt_eq_iff] at h1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at h1
  obtain ⟨-, ⟨k, hk⟩, -⟩ := h1
  have h2 : (2 : ℤ) ^ (m + 1) * (-1) = 2 ^ (m + 1) * (2 * k) := by linear_combination hk
  have h3 := mul_left_cancel₀ (pow_ne_zero (m + 1) (two_ne_zero : (2 : ℤ) ≠ 0)) h2
  omega

open StrothWeakTypeData in
theorem t200_i_h1 (hm : 1 ≤ m) (hrel : Rel34i dD e (2 ^ (m + 1))) :
    (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}).relIndex
      (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) = 2 :=
  (dD.t200iAction hrel).relIndex_S (t200_i_not_word dD hm hrel)

open StrothWeakTypeData in
theorem t200_i_h2 (hm : 1 ≤ m) (hrel : Rel34i dD e (2 ^ (m + 1))) :
    e ∉ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} :=
  (dD.t200iAction hrel).e_not_mem (t200_i_not_word dD hm hrel)

end Stroth47Core

end CFSG.CGT.Stroth77
