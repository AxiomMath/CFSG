module

public import CFSG.CGT.Stroth77.Section47InvOneCard
public import CFSG.CGT.Stroth77.Section47InvOneOne
public import CFSG.CGT.Stroth77.Section47CoreX

public section

namespace CFSG.CGT.Stroth77

open Stroth42Core Stroth34T200

namespace Stroth47Core

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ} (dD : StrothWeakTypeData D (.t200 m))
  {e : G}

theorem t200inv1_c₂_eq (hm : 1 ≤ m) :
    (dD.c : G) ^ 2 ^ (m - 2) =
      dD.ofTorus (Torus.ofInt _ ![(2 : ℤ) ^ (m - 2), 0, 0]) := by
  have _ := hm
  rw [dD.c_eq, ← dD.ofTorus_nsmul, c_eq_ofInt, ← natCast_zsmul, t200_zsmul_vec]
  congr 1
  funext i
  fin_cases i <;> simp

theorem t200inv1_c₂_comm_u (hm : 1 ≤ m) :
    dD.u * (dD.c : G) ^ 2 ^ (m - 2) = (dD.c : G) ^ 2 ^ (m - 2) * dD.u := by
  rw [t200inv1_c₂_eq dD hm, dD.u_mul_ofTorus]
  have h : (StrothTypeIndex.t200 m).action.φu
      (Torus.ofInt _ ![(2 : ℤ) ^ (m - 2), 0, 0]) =
        Torus.ofInt _ ![(2 : ℤ) ^ (m - 2), 0, 0] := by
    rw [t200_φu]
    simp
  rw [h]

theorem t200inv1_c₂_conj_e {j p : ℕ} (hm : 2 ≤ m) (hrel : Rel34inv dD e j 1 p) :
    ((dD.c : G) ^ 2 ^ (m - 2))⁻¹ * e * (dD.c : G) ^ 2 ^ (m - 2) =
      e * (dD.c : G) ^ 2 ^ (m - 1) := by
  let hE := dD.t200inv1EAction hrel
  set w : Torus (StrothTypeIndex.t200 m).k :=
    Torus.ofInt _ ![(2 : ℤ) ^ (m - 2), 0, 0] with hw
  have hφe : hE.φe w = -w := by
    rw [hw, StrothWeakTypeData.t200inv1_φe, t200_neg_vec]
    congr 1
    funext i
    fin_cases i <;> simp
  have hew : e * dD.ofTorus w = dD.ofTorus (-w) * e := by
    rw [hE.e_mul_ofTorus, hφe]
  have hww : dD.ofTorus w * dD.ofTorus w = (dD.c : G) ^ 2 ^ (m - 1) := by
    rw [dD.ofTorus_mul_self, dD.t200_c_pow]
    congr 1
    rw [hw, om200_apply, t200_add_vec]
    congr 1
    funext i
    fin_cases i <;> simp
    have hpow : (2 : ℤ) ^ (m - 1) = 2 * 2 ^ (m - 2) := by
      rw [show m - 1 = (m - 2) + 1 by omega, pow_succ]
      ring
    rw [hpow]
    ring
  have hc₁2 : (dD.c : G) ^ 2 ^ (m - 1) * (dD.c : G) ^ 2 ^ (m - 1) = 1 := by
    rw [dD.t200_c_pow, ← dD.ofTorus_add, om200_add_self (by omega), dD.ofTorus_zero]
  have hc₁inv : ((dD.c : G) ^ 2 ^ (m - 1))⁻¹ = (dD.c : G) ^ 2 ^ (m - 1) :=
    inv_eq_of_mul_eq_one_right hc₁2
  rw [t200inv1_c₂_eq dD (by omega), ← hw]
  calc
    (dD.ofTorus w)⁻¹ * e * dD.ofTorus w
        = (dD.ofTorus w)⁻¹ * (e * dD.ofTorus w) := by group
    _ = (dD.ofTorus w)⁻¹ * (dD.ofTorus (-w) * e) := by rw [hew]
    _ = (dD.ofTorus w * dD.ofTorus w)⁻¹ * e := by
          rw [dD.ofTorus_neg]
          group
    _ = ((dD.c : G) ^ 2 ^ (m - 1))⁻¹ * e := by rw [hww]
    _ = (dD.c : G) ^ 2 ^ (m - 1) * e := by rw [hc₁inv]
    _ = e * (dD.c : G) ^ 2 ^ (m - 1) := by rw [t200inv1_e_comm_c₁ dD (by omega) hrel]

theorem t200inv1_comm_w₀ {j p : ℕ} (hm : 1 ≤ m) (hj : Even j) (hrel : Rel34inv dD e j 1 p) :
    ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
      y * ((dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1)) =
        (dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1) * y := by
  intro y hy
  let hE := dD.t200inv1EAction hrel
  rw [← t200inv1_w0_eq]
  obtain ⟨v, i, jb, l, k, rfl⟩ := hE.mem_sup_zpowers_iff.mp hy
  have hfix : ∀ i jb l, (StrothTypeIndex.t200 m).action.d8Act i jb l
      (om200 m ![0, 1, 1]) = om200 m ![0, 1, 1] := by
    intro i jb l
    cases i <;> cases jb <;> cases l <;>
      simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte,
        AddMonoidHom.comp_apply, AddMonoidHom.id_apply, t200_φuv_om hm, t200_φt_om hm,
        t200_φu_om] <;>
      exact (om200_eq_iff hm _ _).mpr (by decide)
  have hd : dD.d8 i jb l * dD.ofTorus (om200 m ![0, 1, 1]) =
      dD.ofTorus (om200 m ![0, 1, 1]) * dD.d8 i jb l := by
    have h := dD.t200_om_comm (v := 0) (i := i) (j := jb) (l := l)
      (ε := ![0, 1, 1]) (hfix i jb l)
    rw [dD.ofTorus_zero, one_mul] at h
    exact h.symm
  have hv : dD.ofTorus (om200 m ![0, 1, 1]) * dD.ofTorus v =
      dD.ofTorus v * dD.ofTorus (om200 m ![0, 1, 1]) := dD.ofTorus_comm _ _
  have he : e * dD.ofTorus (om200 m ![0, 1, 1]) =
      dD.ofTorus (om200 m ![0, 1, 1]) * e := by
    have h := hE.e_mul_ofTorus (om200 m ![0, 1, 1])
    rwa [t200inv1_φe_om dD hrel hm hj] at h
  have hk : ∀ k : Bool, Stroth42Core.bpow e k * dD.ofTorus (om200 m ![0, 1, 1]) =
      dD.ofTorus (om200 m ![0, 1, 1]) * Stroth42Core.bpow e k := by
    intro k
    cases k <;> simp [Stroth42Core.bpow, he]
  calc
    (dD.ofTorus v * dD.d8 i jb l * Stroth42Core.bpow e k) *
        dD.ofTorus (om200 m ![0, 1, 1])
        = dD.ofTorus v * dD.d8 i jb l *
            (Stroth42Core.bpow e k * dD.ofTorus (om200 m ![0, 1, 1])) := by group
    _ = dD.ofTorus v * dD.d8 i jb l *
            (dD.ofTorus (om200 m ![0, 1, 1]) * Stroth42Core.bpow e k) := by rw [hk]
    _ = dD.ofTorus v * (dD.d8 i jb l * dD.ofTorus (om200 m ![0, 1, 1])) *
            Stroth42Core.bpow e k := by group
    _ = dD.ofTorus v * (dD.ofTorus (om200 m ![0, 1, 1]) * dD.d8 i jb l) *
            Stroth42Core.bpow e k := by rw [hd]
    _ = (dD.ofTorus v * dD.ofTorus (om200 m ![0, 1, 1])) * dD.d8 i jb l *
            Stroth42Core.bpow e k := by group
    _ = (dD.ofTorus (om200 m ![0, 1, 1]) * dD.ofTorus v) * dD.d8 i jb l *
            Stroth42Core.bpow e k := by rw [hv]
    _ = dD.ofTorus (om200 m ![0, 1, 1]) *
          (dD.ofTorus v * dD.d8 i jb l * Stroth42Core.bpow e k) := by group

theorem t200inv1_conj_nfe {j p : ℕ} (hrel : Rel34inv dD e j 1 p)
    {v w : Torus (StrothTypeIndex.t200 m).k} {i jb l k : Bool} (hjl : (l && jb) = false) :
    (dD.ofTorus w)⁻¹ * (dD.ofTorus v * dD.d8 i jb l * bpow e k) * dD.ofTorus w =
      dD.ofTorus v * dD.d8 i jb l * bpow e k *
        dD.ofTorus (w - (if k then (dD.t200inv1EAction hrel).φe
          ((StrothTypeIndex.t200 m).action.d8Act i jb l w) else
            (StrothTypeIndex.t200 m).action.d8Act i jb l w)) := by
  let hE := dD.t200inv1EAction hrel
  have he2 : e * e = 1 := by
    rw [hE.mul_self, show hE.ve = 0 from rfl, dD.ofTorus_zero]
  have h8 : dD.d8 i jb l * dD.d8 i jb l = 1 := by
    rw [dD.d8_mul_self, hjl, dD.d8_fff]
  have hA : dD.d8 i jb l * dD.ofTorus w * dD.d8 i jb l =
      dD.ofTorus ((StrothTypeIndex.t200 m).action.d8Act i jb l w) := by
    rw [dD.d8_mul_ofTorus, mul_assoc, h8, mul_one]
  have hAinv : dD.d8 i jb l * (dD.ofTorus w)⁻¹ * dD.d8 i jb l =
      dD.ofTorus (-(StrothTypeIndex.t200 m).action.d8Act i jb l w) := by
    have h := congrArg Inv.inv hA
    rw [← dD.ofTorus_neg] at h
    simp only [mul_inv_rev] at h
    rw [show (dD.d8 i jb l)⁻¹ = dD.d8 i jb l from inv_eq_of_mul_eq_one_right h8] at h
    simpa [mul_assoc] using h
  have hq : (dD.ofTorus w)⁻¹ * dD.d8 i jb l * dD.ofTorus w =
      dD.d8 i jb l *
        dD.ofTorus (w - (StrothTypeIndex.t200 m).action.d8Act i jb l w) := by
    calc
      (dD.ofTorus w)⁻¹ * dD.d8 i jb l * dD.ofTorus w
          = (dD.d8 i jb l * dD.d8 i jb l) * (dD.ofTorus w)⁻¹ * dD.d8 i jb l *
              dD.ofTorus w := by rw [h8, one_mul]
      _ = dD.d8 i jb l * (dD.d8 i jb l * (dD.ofTorus w)⁻¹ * dD.d8 i jb l) *
              dD.ofTorus w := by group
      _ = dD.d8 i jb l *
            dD.ofTorus (-(StrothTypeIndex.t200 m).action.d8Act i jb l w) *
              dD.ofTorus w := by rw [hAinv]
      _ = dD.d8 i jb l *
            dD.ofTorus (w - (StrothTypeIndex.t200 m).action.d8Act i jb l w) := by
            rw [mul_assoc, ← dD.ofTorus_add,
              show -(StrothTypeIndex.t200 m).action.d8Act i jb l w + w =
                w - (StrothTypeIndex.t200 m).action.d8Act i jb l w by abel]
  have heq : (dD.ofTorus w)⁻¹ * e * dD.ofTorus w =
      e * dD.ofTorus (w - hE.φe w) := by
    have h1 : e * dD.ofTorus w * e = dD.ofTorus (hE.φe w) := by
      rw [hE.e_mul_ofTorus, mul_assoc, he2, mul_one]
    have h2 : e * (dD.ofTorus w)⁻¹ * e = dD.ofTorus (-hE.φe w) := by
      have h := congrArg Inv.inv h1
      simpa [mul_inv_rev, inv_inv, show e⁻¹ = e from inv_eq_of_mul_eq_one_right he2,
        ← dD.ofTorus_neg, mul_assoc] using h
    calc
      (dD.ofTorus w)⁻¹ * e * dD.ofTorus w
          = (e * e) * (dD.ofTorus w)⁻¹ * e * dD.ofTorus w := by rw [he2, one_mul]
      _ = e * (e * (dD.ofTorus w)⁻¹ * e) * dD.ofTorus w := by group
      _ = e * dD.ofTorus (-hE.φe w) * dD.ofTorus w := by rw [h2]
      _ = e * dD.ofTorus (w - hE.φe w) := by
            rw [mul_assoc, ← dD.ofTorus_add,
              show -hE.φe w + w = w - hE.φe w by abel]
  have hD : (dD.ofTorus w)⁻¹ * dD.ofTorus v * dD.ofTorus w = dD.ofTorus v := by
    rw [← dD.ofTorus_neg, ← dD.ofTorus_add, ← dD.ofTorus_add,
      show -w + v + w = v by abel]
  have hstep : dD.d8 i jb l *
        dD.ofTorus (w - (StrothTypeIndex.t200 m).action.d8Act i jb l w) *
          (e * dD.ofTorus (w - hE.φe w)) =
      dD.d8 i jb l * e * dD.ofTorus (w - hE.φe
        ((StrothTypeIndex.t200 m).action.d8Act i jb l w)) := by
    calc
      dD.d8 i jb l * dD.ofTorus (w - (StrothTypeIndex.t200 m).action.d8Act i jb l w) *
          (e * dD.ofTorus (w - hE.φe w))
          = dD.d8 i jb l * ((dD.ofTorus (w - (StrothTypeIndex.t200 m).action.d8Act i jb l w) *
              e) * dD.ofTorus (w - hE.φe w)) := by group
      _ = dD.d8 i jb l * ((e * dD.ofTorus (hE.φe
              (w - (StrothTypeIndex.t200 m).action.d8Act i jb l w))) *
            dD.ofTorus (w - hE.φe w)) := by rw [hE.ofTorus_mul_e]
      _ = (dD.d8 i jb l * e) * (dD.ofTorus (hE.φe
              (w - (StrothTypeIndex.t200 m).action.d8Act i jb l w)) *
            dD.ofTorus (w - hE.φe w)) := by group
      _ = (dD.d8 i jb l * e) * dD.ofTorus (w - hE.φe
              ((StrothTypeIndex.t200 m).action.d8Act i jb l w)) := by
            rw [← dD.ofTorus_add]
            congr 2
            simp only [map_sub]
            abel
  cases k
  · simp only [bpow, Bool.false_eq_true, ↓reduceIte, mul_one]
    calc
      (dD.ofTorus w)⁻¹ * (dD.ofTorus v * dD.d8 i jb l) * dD.ofTorus w
          = ((dD.ofTorus w)⁻¹ * dD.ofTorus v * dD.ofTorus w) *
              ((dD.ofTorus w)⁻¹ * dD.d8 i jb l * dD.ofTorus w) := by group
      _ = dD.ofTorus v *
            ((dD.ofTorus w)⁻¹ * dD.d8 i jb l * dD.ofTorus w) := by rw [hD]
      _ = dD.ofTorus v *
            (dD.d8 i jb l *
              dD.ofTorus (w - (StrothTypeIndex.t200 m).action.d8Act i jb l w)) := by
            rw [hq]
      _ = dD.ofTorus v * dD.d8 i jb l *
            dD.ofTorus (w - (StrothTypeIndex.t200 m).action.d8Act i jb l w) := by group
  · simp only [bpow, ↓reduceIte]
    calc
      (dD.ofTorus w)⁻¹ * (dD.ofTorus v * dD.d8 i jb l * e) * dD.ofTorus w
          = ((dD.ofTorus w)⁻¹ * dD.ofTorus v * dD.ofTorus w) *
              ((dD.ofTorus w)⁻¹ * dD.d8 i jb l * dD.ofTorus w) *
                ((dD.ofTorus w)⁻¹ * e * dD.ofTorus w) := by group
      _ = dD.ofTorus v *
            ((dD.ofTorus w)⁻¹ * dD.d8 i jb l * dD.ofTorus w) *
              ((dD.ofTorus w)⁻¹ * e * dD.ofTorus w) := by rw [hD]
      _ = dD.ofTorus v *
            (dD.d8 i jb l *
                dD.ofTorus (w - (StrothTypeIndex.t200 m).action.d8Act i jb l w)) *
              (e * dD.ofTorus (w - hE.φe w)) := by rw [hq, heq]
      _ = dD.ofTorus v * dD.d8 i jb l * e *
            dD.ofTorus (w - hE.φe
              ((StrothTypeIndex.t200 m).action.d8Act i jb l w)) := by
            rw [mul_assoc, hstep, ← mul_assoc, ← mul_assoc]

theorem t200inv1_conj_c₂ {j p : ℕ} (hm : 2 ≤ m) (hrel : Rel34inv dD e j 1 p) :
    ∀ k ∈ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) ⊓
        Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)},
      k ∉ D ⊔ Subgroup.zpowers dD.u →
        ((dD.c : G) ^ 2 ^ (m - 2))⁻¹ * k * (dD.c : G) ^ 2 ^ (m - 2) =
          (dD.c : G) ^ 2 ^ (m - 1) * k := by
  intro k hk hknot
  let hE := dD.t200inv1EAction hrel
  have hc₁ : hE.φe (om200 m ![1, 0, 0]) = om200 m ![1, 0, 0] := by
    rw [om200_apply, StrothWeakTypeData.t200inv1_φe]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, one_mul, zero_mul, mul_zero]
    rw [t200_ofInt_eq_iff]
    refine ⟨?_, by simp, by simp⟩
    simp only [Matrix.cons_val_zero]
    have h2 : (2 : ℤ) ^ (m - 1) - (-(2 : ℤ) ^ (m - 1)) = (2 : ℤ) ^ m := by
      have h := congrArg (fun k => (2 : ℤ) ^ k) (show m = (m - 1) + 1 by omega)
      rw [pow_add] at h
      rw [h]
      ring
    rw [h2]
  obtain ⟨v, l, kb, hk_eq⟩ := t200_eAction_mem_CSc₁ dD hE hc₁ (by omega) hk
  have hkb : kb = true := by
    cases kb
    · exfalso
      apply hknot
      rw [hk_eq]
      simp only [Stroth42Core.bpow, Bool.false_eq_true, ↓reduceIte, mul_one]
      have hd8 : dD.d8 false false l ∈ Subgroup.zpowers dD.u := by
        cases l
        · rw [dD.d8_fff]; exact one_mem _
        · rw [dD.d8_fft]; exact Subgroup.mem_zpowers dD.u
      exact (D ⊔ Subgroup.zpowers dD.u).mul_mem
        (Subgroup.mem_sup_left (dD.ofTorus_mem v))
        (Subgroup.mem_sup_right hd8)
    · rfl
  subst hkb
  have hkC : k * (dD.c : G) ^ 2 ^ (m - 1) =
      (dD.c : G) ^ 2 ^ (m - 1) * k := by
    obtain ⟨-, hkCmem⟩ := Subgroup.mem_inf.mp hk
    exact Subgroup.mem_centralizer_singleton_iff.1 hkCmem
  simp only [Stroth42Core.bpow, ↓reduceIte] at hk_eq
  rw [hk_eq] at hk hknot hkC ⊢
  have htw : (Torus.ofInt _ ![(2 : ℤ) ^ (m - 2), 0, 0]) -
      hE.φe ((StrothTypeIndex.t200 m).action.d8Act false false l
        (Torus.ofInt _ ![(2 : ℤ) ^ (m - 2), 0, 0])) = om200 m ![1, 0, 0] := by
    have hfix : (StrothTypeIndex.t200 m).action.d8Act false false l
        (Torus.ofInt _ ![(2 : ℤ) ^ (m - 2), 0, 0]) =
          Torus.ofInt _ ![(2 : ℤ) ^ (m - 2), 0, 0] := by
      cases l <;>
        simp [SigmaFourAction.d8Act, t200_φu, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two]
    rw [hfix, StrothWeakTypeData.t200inv1_φe]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, mul_zero]
    rw [om200_apply, t200_sub_vec, t200_ofInt_eq_iff]
    refine ⟨?_, by simp, by simp⟩
    simp only [Matrix.cons_val_zero]
    have hpow : (2 : ℤ) ^ (m - 1) = 2 * 2 ^ (m - 2) := by
      rw [show m - 1 = (m - 2) + 1 by omega, pow_succ]
      ring
    have h2 : 1 * 2 ^ (m - 1) - (2 ^ (m - 2) - -2 ^ (m - 2)) = 0 := by
      rw [hpow]
      ring
    rw [h2]
    exact dvd_zero _
  have hc₂ : ((dD.c : G) ^ 2 ^ (m - 2)) =
      dD.ofTorus (Torus.ofInt _ ![(2 : ℤ) ^ (m - 2), 0, 0]) := by
    rw [dD.c_eq, ← dD.ofTorus_nsmul, c_eq_ofInt, ← natCast_zsmul, t200_zsmul_vec]
    congr 1
    funext i
    fin_cases i <;> simp
  rw [hc₂]
  rw [show e = Stroth42Core.bpow e true from by simp [Stroth42Core.bpow]]
  rw [t200inv1_conj_nfe dD hrel (i := false) (jb := false) (l := l) (k := true)
    (by simp)]
  rw [show (if (true = true) then hE.φe
        ((StrothTypeIndex.t200 m).action.d8Act false false l
          (Torus.ofInt _ ![(2 : ℤ) ^ (m - 2), 0, 0])) else
        (StrothTypeIndex.t200 m).action.d8Act false false l
          (Torus.ofInt _ ![(2 : ℤ) ^ (m - 2), 0, 0])) =
      hE.φe ((StrothTypeIndex.t200 m).action.d8Act false false l
        (Torus.ofInt _ ![(2 : ℤ) ^ (m - 2), 0, 0])) from by simp]
  rw [show (Torus.ofInt _ ![(2 : ℤ) ^ (m - 2), 0, 0]) -
      hE.φe ((StrothTypeIndex.t200 m).action.d8Act false false l
        (Torus.ofInt _ ![(2 : ℤ) ^ (m - 2), 0, 0])) = om200 m ![1, 0, 0] from htw,
    dD.t200_c_pow]
  simpa [Stroth42Core.bpow, dD.t200_c_pow] using hkC

theorem t200inv1_conj_a₁ {j p : ℕ} (hm : 1 ≤ m) (hj : j = 0 ∨ j = 2 ^ (m + 1))
    (hrel : Rel34inv dD e j 1 p) :
    ∀ y ∈ D ⊔ Subgroup.zpowers (dD.u * e), y ∉ D ⊔ Subgroup.zpowers dD.u →
      ((dD.a : G) ^ 2 ^ (m + 1))⁻¹ * y * (dD.a : G) ^ 2 ^ (m + 1) =
        (dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1) * y := by
  intro y hy hynot
  let hE := dD.t200inv1EAction hrel
  have hEven : Even j := by
    rcases hj with rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨2 ^ m, by rw [← two_mul, pow_succ']⟩
  have heN : e ∈ Subgroup.normalizer (D : Set G) := by
    rw [Subgroup.mem_normalizer_iff'']
    intro d
    constructor
    · intro hd
      obtain ⟨v, rfl⟩ := dD.exists_ofTorus hd
      rw [hE.conj_ofTorus]
      exact dD.ofTorus_mem _
    · intro hd
      obtain ⟨v, hv⟩ := dD.exists_ofTorus hd
      have hd' : d = e * dD.ofTorus v * e⁻¹ := by rw [← hv]; group
      rw [hd', hE.conj_inv_ofTorus]
      exact dD.ofTorus_mem _
  have hueN : dD.u * e ∈ Subgroup.normalizer (D : Set G) :=
    (Subgroup.normalizer (D : Set G)).mul_mem dD.u_mem heN
  have heu : dD.u * e = e * dD.u := by
    have h := hE.conj_u
    calc dD.u * e = e * (e⁻¹ * dD.u * e) := by group
      _ = e * dD.u := by rw [h]
  have hue2 : (dD.u * e) * (dD.u * e) ∈ D := by
    have h1 : (dD.u * e) * (dD.u * e) = 1 := by
      calc
        (dD.u * e) * (dD.u * e) = dD.u * (e * dD.u) * e := by group
        _ = dD.u * (dD.u * e) * e := by rw [← heu]
        _ = (dD.u * dD.u) * (e * e) := by group
        _ = 1 := by
          rw [dD.u_sq, hE.mul_self, show hE.ve = 0 from rfl, dD.ofTorus_zero, one_mul]
    rw [h1]
    exact D.one_mem
  obtain ⟨d, hdD, kb, hynf⟩ :=
    (Stroth47.mem_sup_zpowers_iff_of_mul_self_mem hueN hue2).mp hy
  have hkb : kb = true := by
    cases kb
    · exfalso
      apply hynot
      rw [hynf]
      simp only [Stroth42Core.bpow, Bool.false_eq_true, ↓reduceIte, mul_one]
      exact Subgroup.mem_sup_left hdD
    · rfl
  subst hkb
  simp only [Stroth42Core.bpow, ↓reduceIte] at hynf
  obtain ⟨d', rfl⟩ := dD.exists_ofTorus hdD
  have hynf' : y = dD.ofTorus d' * dD.d8 false false true * e := by
    rw [hynf, ← dD.d8_fft]
    group
  rw [hynf', dD.t200_a_pow]
  rw [show e = Stroth42Core.bpow e true from by simp [Stroth42Core.bpow]]
  rw [t200inv1_conj_nfe dD hrel (i := false) (jb := false) (l := true) (k := true)
    (by simp)]
  have htw : om200 m ![0, 1, 0] -
      hE.φe ((StrothTypeIndex.t200 m).action.d8Act false false true
        (om200 m ![0, 1, 0])) = om200 m ![0, 1, 1] := by
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte,
      AddMonoidHom.comp_apply, AddMonoidHom.id_apply]
    rw [t200_φu_om, t200inv1_φe_om dD hrel hm hEven]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    rw [sub_eq_add_neg, show -om200 m ![0, 0, 1] = om200 m ![0, 0, 1] from
      neg_eq_of_add_eq_zero_right (om200_add_self hm ![0, 0, 1]), om200_add]
    congr 1
    funext i
    fin_cases i <;> simp
  rw [show (if (true = true) then hE.φe
        ((StrothTypeIndex.t200 m).action.d8Act false false true (om200 m ![0, 1, 0]))
      else (StrothTypeIndex.t200 m).action.d8Act false false true
        (om200 m ![0, 1, 0])) =
      hE.φe ((StrothTypeIndex.t200 m).action.d8Act false false true
        (om200 m ![0, 1, 0])) from by simp, htw]
  rw [← dD.t200_a_pow, t200inv1_w0_eq]
  have hycomm : y * ((dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1)) =
      (dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1) * y := by
    have hyS : y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e := by
      have hueS : dD.u * e ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔
          Subgroup.zpowers e := by
        have huS : dD.u ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} :=
          Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
        have heS : e ∈ Subgroup.zpowers e := Subgroup.mem_zpowers e
        exact Subgroup.mul_mem _
          (Subgroup.mem_sup_left huS) (Subgroup.mem_sup_right heS)
      refine (sup_le ?_ (Subgroup.zpowers_le.mpr hueS)) hy
      exact le_sup_left.trans le_sup_left
    exact t200inv1_comm_w₀ dD hm hEven hrel y hyS
  rw [show bpow e true = e from by simp [Stroth42Core.bpow], ← hynf']
  exact hycomm

theorem t200inv1_u4_uv_not_mem_D (hm : 1 ≤ m) : dD.uv ∉ D := by
  intro h
  have h8 : dD.d8 true false false ∈ D := by simpa [dD.d8_tff] using h
  have h' := dD.d8_eq_of_mem (t200_faithful (m := m) hm) h8
  exact Bool.false_ne_true h'.1.symm

theorem t200inv1_u4_dvd_alt_one (hm : 1 ≤ m) :
    (2 : ℤ) ^ (m + 2) ∣
      (2 : ℤ) ^ (m + 1) - (2 ^ m - (-1 + (2 : ℤ) ^ (m + 1)) * 2 ^ m) := by
  set a : ℤ := 2 ^ m with ha
  have ha1 : (2 : ℤ) ^ (m + 1) = 2 * a := by
    rw [pow_succ, ha]
    ring
  have ha2 : (2 : ℤ) ^ (m + 2) = 4 * a := by
    rw [show m + 2 = m + 1 + 1 by omega, pow_succ, ha1]
    ring
  have haeven : a = 2 * 2 ^ (m - 1) := by
    rw [ha]
    conv_lhs => rw [show m = (m - 1) + 1 by omega]
    rw [pow_succ']
  rw [ha1, ha2]
  rw [show 2 * a - (a - (-1 + 2 * a) * a) = 4 * a * 2 ^ (m - 1) by
    rw [haeven]
    ring]
  exact dvd_mul_of_dvd_left (dvd_refl (4 * a)) _

theorem t200inv1_u4_dvd_alt_two_a :
    (2 : ℤ) ^ (m + 2) ∣
      (2 : ℤ) ^ (m + 1) + (-1 + (2 : ℤ) ^ (m + 1)) * (2 * 2 ^ m) := by
  set a : ℤ := 2 ^ m with ha
  have ha1 : (2 : ℤ) ^ (m + 1) = 2 * a := by
    rw [pow_succ, ha]
    ring
  have ha2 : (2 : ℤ) ^ (m + 2) = 4 * a := by
    rw [show m + 2 = m + 1 + 1 by omega, pow_succ, ha1]
    ring
  rw [ha1, ha2]
  rw [show 2 * a + (-1 + 2 * a) * (2 * a) = 4 * a * a by ring]
  exact dvd_mul_of_dvd_left (dvd_refl (4 * a)) _

theorem t200inv1_u4_dvd_alt_two_b :
    (2 : ℤ) ^ (m + 2) ∣
      (2 : ℤ) ^ (m + 1) + (-1 + (2 : ℤ) ^ (m + 1)) * 2 ^ (m + 1) := by
  set a : ℤ := 2 ^ m with ha
  have ha1 : (2 : ℤ) ^ (m + 1) = 2 * a := by
    rw [pow_succ, ha]
    ring
  have ha2 : (2 : ℤ) ^ (m + 2) = 4 * a := by
    rw [show m + 2 = m + 1 + 1 by omega, pow_succ, ha1]
    ring
  rw [ha1, ha2]
  rw [show 2 * a + (-1 + 2 * a) * (2 * a) = 4 * a * a by ring]
  exact dvd_mul_of_dvd_left (dvd_refl (4 * a)) _

theorem t200inv1_u4_dvd_alt_jm1 :
    (2 : ℤ) ^ (m + 2) ∣ (-1 + (2 : ℤ) ^ (m + 1)) * (2 * 2 ^ (m + 1)) := by
  set a : ℤ := 2 ^ m with ha
  have ha1 : (2 : ℤ) ^ (m + 1) = 2 * a := by
    rw [pow_succ, ha]
    ring
  have ha2 : (2 : ℤ) ^ (m + 2) = 4 * a := by
    rw [show m + 2 = m + 1 + 1 by omega, pow_succ, ha1]
    ring
  rw [ha1, ha2]
  rw [show (-1 + 2 * a) * (2 * (2 * a)) = (-1 + 2 * a) * (4 * a) by ring]
  exact dvd_mul_of_dvd_right (dvd_refl (4 * a)) _

theorem t200inv1_u4_twist_e {j p : ℕ} (hm : 1 ≤ m) (hrel : Rel34inv dD e j 1 p)
    (hj : j = 0 ∨ j = 2 ^ (m + 1)) :
    Torus.ofInt (StrothTypeIndex.t200 m).k
        ![(2 : ℤ) ^ m, (2 : ℤ) ^ m, (2 : ℤ) ^ m] -
      (dD.t200inv1EAction hrel).φe
        (Torus.ofInt _ ![(2 : ℤ) ^ m, (2 : ℤ) ^ m, (2 : ℤ) ^ m]) =
        om200 m ![0, 1, 1] := by
  rw [StrothWeakTypeData.t200inv1_φe, t200_sub_vec, om200_apply, t200_ofInt_eq_iff]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rcases hj with rfl | rfl
  · refine ⟨?_, ?_, ?_⟩
    · convert dvd_mul_of_dvd_right (dvd_refl ((2 : ℤ) ^ m)) (-2) using 1; ring
    · convert dvd_zero ((2 : ℤ) ^ (m + 2)) using 1; ring
    · convert dvd_zero ((2 : ℤ) ^ (m + 2)) using 1; ring
  · refine ⟨?_, ?_, ?_⟩
    · convert dvd_mul_of_dvd_right (dvd_refl ((2 : ℤ) ^ m)) (-2) using 1; ring
    · simpa [Nat.cast_pow] using t200inv1_u4_dvd_alt_one (m := m) hm
    · simpa [Nat.cast_pow] using t200inv1_u4_dvd_alt_one (m := m) hm

theorem t200inv1_u4_twist_uve {j p : ℕ} (hm : 1 ≤ m) (hrel : Rel34inv dD e j 1 p)
    (hj : j = 0 ∨ j = 2 ^ (m + 1)) :
    Torus.ofInt (StrothTypeIndex.t200 m).k ![0, (2 : ℤ) ^ m, 0] -
      (dD.t200inv1EAction hrel).φe
        ((StrothTypeIndex.t200 m).action.φuv
          (Torus.ofInt _ ![0, (2 : ℤ) ^ m, 0])) = om200 m ![0, 1, 1] := by
  rw [t200_φuv_vec, StrothWeakTypeData.t200inv1_φe, t200_sub_vec, om200_apply,
    t200_ofInt_eq_iff]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rcases hj with rfl | rfl
  · refine ⟨?_, ?_, ?_⟩
    · convert dvd_neg.mpr (dvd_refl ((2 : ℤ) ^ m)) using 1; ring
    · convert dvd_zero ((2 : ℤ) ^ (m + 2)) using 1; ring
    · convert dvd_zero ((2 : ℤ) ^ (m + 2)) using 1; ring
  · refine ⟨?_, ?_, ?_⟩
    · convert dvd_neg.mpr (dvd_refl ((2 : ℤ) ^ m)) using 1; ring
    · simpa [Nat.cast_pow] using t200inv1_u4_dvd_alt_one (m := m) hm
    · simpa [Nat.cast_pow] using t200inv1_u4_dvd_alt_two_a (m := m)

theorem t200inv1_u4_twist_ue {j p : ℕ} (_hm : 1 ≤ m) (hrel : Rel34inv dD e j 1 p)
    (hj : j = 0 ∨ j = 2 ^ (m + 1)) :
    Torus.ofInt (StrothTypeIndex.t200 m).k ![0, 0, (2 : ℤ) ^ (m + 1)] -
      (dD.t200inv1EAction hrel).φe
        ((StrothTypeIndex.t200 m).action.φu
          (Torus.ofInt _ ![0, 0, (2 : ℤ) ^ (m + 1)])) = om200 m ![0, 1, 1] := by
  rw [t200_φu_vec, StrothWeakTypeData.t200inv1_φe, t200_sub_vec, om200_apply,
    t200_ofInt_eq_iff]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rcases hj with rfl | rfl
  · refine ⟨?_, ?_, ?_⟩
    · convert dvd_zero ((2 : ℤ) ^ m) using 1; ring
    · convert dvd_zero ((2 : ℤ) ^ (m + 2)) using 1; ring
    · convert dvd_zero ((2 : ℤ) ^ (m + 2)) using 1; ring
  · refine ⟨?_, ?_, ?_⟩
    · convert dvd_zero ((2 : ℤ) ^ m) using 1; ring
    · simpa [Nat.cast_pow] using t200inv1_u4_dvd_alt_two_b (m := m)
    · convert dvd_zero ((2 : ℤ) ^ (m + 2)) using 1; ring

theorem t200inv1_u4_twist_uvue {j p : ℕ} (_hm : 1 ≤ m) (hrel : Rel34inv dD e j 1 p)
    (hj : j = 0 ∨ j = 2 ^ (m + 1)) :
    Torus.ofInt (StrothTypeIndex.t200 m).k ![0, 0, (2 : ℤ) ^ (m + 1)] -
      (dD.t200inv1EAction hrel).φe
        ((StrothTypeIndex.t200 m).action.φuv
          ((StrothTypeIndex.t200 m).action.φu
            (Torus.ofInt _ ![0, 0, (2 : ℤ) ^ (m + 1)]))) = om200 m ![0, 1, 1] := by
  rw [t200_φu_vec, t200_φuv_vec, StrothWeakTypeData.t200inv1_φe, t200_sub_vec,
    om200_apply, t200_ofInt_eq_iff]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rcases hj with rfl | rfl
  · refine ⟨?_, ?_, ?_⟩
    · convert dvd_mul_of_dvd_right (dvd_refl ((2 : ℤ) ^ m)) (-2) using 1; ring
    · convert dvd_zero ((2 : ℤ) ^ (m + 2)) using 1; ring
    · convert dvd_neg.mpr (dvd_refl ((2 : ℤ) ^ (m + 2))) using 1; ring
  · refine ⟨?_, ?_, ?_⟩
    · convert dvd_mul_of_dvd_right (dvd_refl ((2 : ℤ) ^ m)) (-2) using 1; ring
    · simpa [Nat.cast_pow] using t200inv1_u4_dvd_alt_two_b (m := m)
    · simpa [Nat.cast_pow] using t200inv1_u4_dvd_alt_jm1 (m := m)

theorem t200inv1_u4_twist_t :
    Torus.ofInt (StrothTypeIndex.t200 m).k ![0, 0, (2 : ℤ) ^ m] -
        (StrothTypeIndex.t200 m).action.φt
          (Torus.ofInt _ ![0, 0, (2 : ℤ) ^ m]) = om200 m ![0, 1, 1] := by
  rw [t200_φt_vec, t200_sub_vec, om200_apply, t200_ofInt_eq_iff]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  refine ⟨?_, ?_, ?_⟩
  · convert dvd_neg.mpr (dvd_refl ((2 : ℤ) ^ m)) using 1; ring
  · convert dvd_zero ((2 : ℤ) ^ (m + 2)) using 1; ring
  · convert dvd_zero ((2 : ℤ) ^ (m + 2)) using 1; ring

theorem t200inv1_u4_twist_uv :
    Torus.ofInt (StrothTypeIndex.t200 m).k
        ![(2 : ℤ) ^ m, (2 : ℤ) ^ m, (2 : ℤ) ^ m] -
      (StrothTypeIndex.t200 m).action.φuv
        (Torus.ofInt _ ![(2 : ℤ) ^ m, (2 : ℤ) ^ m, (2 : ℤ) ^ m]) =
        om200 m ![0, 1, 1] := by
  rw [t200_φuv_vec, t200_sub_vec, om200_apply, t200_ofInt_eq_iff]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  refine ⟨?_, ?_, ?_⟩
  · convert dvd_mul_of_dvd_right (dvd_refl ((2 : ℤ) ^ m)) (-2) using 1; ring
  · convert dvd_zero ((2 : ℤ) ^ (m + 2)) using 1; ring
  · convert dvd_zero ((2 : ℤ) ^ (m + 2)) using 1; ring

theorem t200inv1_u4_twist_uvt :
    Torus.ofInt (StrothTypeIndex.t200 m).k ![0, (2 : ℤ) ^ m, 0] -
      (StrothTypeIndex.t200 m).action.φuv
        ((StrothTypeIndex.t200 m).action.φt
          (Torus.ofInt _ ![0, (2 : ℤ) ^ m, 0])) = om200 m ![0, 1, 1] := by
  rw [t200_φt_vec, t200_φuv_vec, t200_sub_vec, om200_apply, t200_ofInt_eq_iff]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  refine ⟨?_, ?_, ?_⟩
  · convert dvd_neg.mpr (dvd_refl ((2 : ℤ) ^ m)) using 1; ring
  · convert dvd_zero ((2 : ℤ) ^ (m + 2)) using 1; ring
  · convert dvd_zero ((2 : ℤ) ^ (m + 2)) using 1; ring

theorem t200inv1_u4_twist_uvu :
    Torus.ofInt (StrothTypeIndex.t200 m).k ![0, (2 : ℤ) ^ (m + 1), 0] -
      (StrothTypeIndex.t200 m).action.φuv
        ((StrothTypeIndex.t200 m).action.φu
          (Torus.ofInt _ ![0, (2 : ℤ) ^ (m + 1), 0])) = om200 m ![0, 1, 1] := by
  rw [t200_φu_vec, t200_φuv_vec, t200_sub_vec, om200_apply, t200_ofInt_eq_iff]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  refine ⟨?_, ?_, ?_⟩
  · convert dvd_mul_of_dvd_right (dvd_refl ((2 : ℤ) ^ m)) 2 using 1; ring
  · convert dvd_refl ((2 : ℤ) ^ (m + 2)) using 1; ring
  · convert dvd_refl ((2 : ℤ) ^ (m + 2)) using 1; ring

theorem t200inv1_u4_twist_u :
    Torus.ofInt (StrothTypeIndex.t200 m).k ![0, 0, (2 : ℤ) ^ (m + 1)] -
      (StrothTypeIndex.t200 m).action.φu
        (Torus.ofInt _ ![0, 0, (2 : ℤ) ^ (m + 1)]) = om200 m ![0, 1, 1] := by
  rw [t200_φu_vec, t200_sub_vec, om200_apply, t200_ofInt_eq_iff]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  refine ⟨?_, ?_, ?_⟩
  · convert dvd_zero ((2 : ℤ) ^ m) using 1; ring
  · convert dvd_refl ((2 : ℤ) ^ (m + 2)) using 1; ring
  · convert dvd_zero ((2 : ℤ) ^ (m + 2)) using 1; ring

theorem t200inv1_u4_conj_w0 {j p : ℕ} (_hm : 1 ≤ m)
    (hrel : Rel34inv dD e j 1 p) {v w : Torus (StrothTypeIndex.t200 m).k}
    {i jb l k : Bool} (hjl : (l && jb) = false)
    (htw : w - (if k then (dD.t200inv1EAction hrel).φe
      ((StrothTypeIndex.t200 m).action.d8Act i jb l w) else
        (StrothTypeIndex.t200 m).action.d8Act i jb l w) = om200 m ![0, 1, 1]) :
    (dD.ofTorus w)⁻¹ * (dD.ofTorus v * dD.d8 i jb l * bpow e k) * dD.ofTorus w =
      (dD.ofTorus v * dD.d8 i jb l * bpow e k) *
        ((dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1)) := by
  rw [t200inv1_conj_nfe dD hrel hjl, htw, t200inv1_w0_eq]

theorem t200inv1_conj_mul_w₀ {j p : ℕ} (hm : 1 ≤ m) (hj : j = 0 ∨ j = 2 ^ (m + 1))
    (hrel : Rel34inv dD e j 1 p) :
    ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e, y * y = 1 → y ≠ 1 →
      y ≠ (dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1) →
      (∀ (v : Torus (StrothTypeIndex.t200 m).k) (i : Bool),
        y ≠ dD.ofTorus v * dD.d8 i true false * e) →
      ∃ q ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
        q⁻¹ * y * q = y * ((dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1)) := by
  intro y hyS hy2 hy1 hyw0 hnot
  let hE := dD.t200inv1EAction hrel
  have hmem : ∀ w, dD.ofTorus w ∈
      D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e := fun w =>
    Subgroup.mem_sup_left (Subgroup.mem_sup_left (dD.ofTorus_mem w))
  obtain ⟨v, i, jb, l, k, rfl⟩ := hE.mem_sup_zpowers_iff.mp hyS
  have hjl : (l && jb) = false := by
    by_contra h
    have htrue : (l && jb) = true := by
      cases l <;> cases jb <;> simp_all
    cases k
    · simp only [bpow, Bool.false_eq_true, ↓reduceIte, mul_one] at hy2
      rw [dD.nf_mul_self, htrue, dD.d8_tff] at hy2
      have h' : dD.ofTorus (v + (StrothTypeIndex.t200 m).action.d8Act i jb l v) = dD.uv := by
        have h := eq_inv_of_mul_eq_one_left hy2
        simpa [dD.uv_inv] using h
      exact t200inv1_u4_uv_not_mem_D dD hm (by rw [← h']; exact dD.ofTorus_mem _)
    · simp only [bpow, ↓reduceIte] at hy2
      rw [hE.nfe_e_mul_self, htrue, dD.d8_tff] at hy2
      have h' : dD.ofTorus (hE.sqE v i jb l) = dD.uv := by
        have h := eq_inv_of_mul_eq_one_left hy2
        simpa [dD.uv_inv] using h
      exact t200inv1_u4_uv_not_mem_D dD hm (by rw [← h']; exact dD.ofTorus_mem _)
  have key : ∀ (w : Torus (StrothTypeIndex.t200 m).k) (i jb l k : Bool),
      (l && jb) = false →
      w - (if k then (dD.t200inv1EAction hrel).φe
        ((StrothTypeIndex.t200 m).action.d8Act i jb l w) else
          (StrothTypeIndex.t200 m).action.d8Act i jb l w) = om200 m ![0, 1, 1] →
      ∃ q ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
        q⁻¹ * (dD.ofTorus v * dD.d8 i jb l * bpow e k) * q =
          (dD.ofTorus v * dD.d8 i jb l * bpow e k) *
            ((dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1)) := by
    intro w i jb l k hjl htw
    exact ⟨dD.ofTorus w, hmem w, t200inv1_u4_conj_w0 dD hm hrel hjl htw⟩
  by_cases hD : i = false ∧ jb = false ∧ l = false ∧ k = false
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := hD
    simp only [dD.d8_fff, bpow, Bool.false_eq_true, ↓reduceIte, mul_one] at hy2 ⊢
    obtain ⟨ε, hε, hεv⟩ := dD.t200_eq_om_of_mul_self hm (dD.ofTorus_mem v) hy2
    have hv : v = om200 m ε := dD.ofTorus_inj hεv
    subst v
    have hy1' : dD.ofTorus (om200 m ε) ≠ 1 := by
      simpa [dD.d8_fff, bpow] using hy1
    have hyw0' : dD.ofTorus (om200 m ε) ≠
        dD.a ^ 2 ^ (m + 1) * dD.b ^ 2 ^ (m + 1) := by
      simpa [dD.d8_fff, bpow] using hyw0
    rw [← t200inv1_w0_eq] at hyw0'
    clear hy1 hyw0
    by_cases h0 : ε 0 = 1
    · have hφ : (StrothTypeIndex.t200 m).action.φuv (om200 m ε) =
          om200 m (ε + ![0, 1, 1]) := by
        rw [t200_φuv_om hm]
        apply (om200_eq_iff hm _ _).mpr
        rcases hε 1 with h1 | h1 <;> rcases hε 2 with h2 | h2 <;>
          (intro i
           fin_cases i <;> simp [h0, h1, h2] <;> norm_num)
      refine ⟨dD.uv, ?_, ?_⟩
      · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right
          (Subgroup.subset_closure (by simp)))
      · calc
          (dD.uv)⁻¹ * dD.ofTorus (om200 m ε) * dD.uv
              = dD.ofTorus ((StrothTypeIndex.t200 m).action.φuv (om200 m ε)) := by
                rw [dD.conj_ofTorus dD.uv_mem dD.uv_conj]
          _ = dD.ofTorus (om200 m (ε + ![0, 1, 1])) := by rw [hφ]
          _ = dD.ofTorus (om200 m ε) * dD.ofTorus (om200 m ![0, 1, 1]) := by
                rw [← dD.ofTorus_add, ← om200_add]
          _ = dD.ofTorus (om200 m ε) * (dD.a ^ 2 ^ (m + 1) * dD.b ^ 2 ^ (m + 1)) := by
                rw [t200inv1_w0_eq]
    · have h0' : ε 0 = 0 := by
        rcases hε 0 with h | h
        · exact h
        · exact absurd h h0
      have hnot00 : ¬(ε 1 = 0 ∧ ε 2 = 0) := by
        rintro ⟨h1, h2⟩
        apply hy1'
        rw [show ε = 0 by funext i; fin_cases i <;> simp [h0', h1, h2],
          om200_zero, dD.ofTorus_zero]
      have hnot11 : ¬(ε 1 = 1 ∧ ε 2 = 1) := by
        rintro ⟨h1, h2⟩
        apply hyw0'
        rw [show ε = ![0, 1, 1] by funext i; fin_cases i <;> simp [h0', h1, h2]]
      rcases hε 1 with h1 | h1 <;> rcases hε 2 with h2 | h2
      case inl.inl => exact absurd ⟨h1, h2⟩ hnot00
      case inr.inr => exact absurd ⟨h1, h2⟩ hnot11
      all_goals
        have hφ : (StrothTypeIndex.t200 m).action.φu (om200 m ε) =
              om200 m (ε + ![0, 1, 1]) := by
          rw [t200_φu_om]
          apply (om200_eq_iff hm _ _).mpr
          intro i
          fin_cases i <;> simp [h0', h1, h2]
          all_goals norm_num
        refine ⟨dD.u, ?_, ?_⟩
        · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right
            (Subgroup.subset_closure (by simp)))
        · calc
            (dD.u)⁻¹ * dD.ofTorus (om200 m ε) * dD.u
                = dD.ofTorus ((StrothTypeIndex.t200 m).action.φu (om200 m ε)) := by
                  rw [dD.conj_ofTorus dD.u_mem dD.u_conj]
            _ = dD.ofTorus (om200 m (ε + ![0, 1, 1])) := by rw [hφ]
            _ = dD.ofTorus (om200 m ε) * dD.ofTorus (om200 m ![0, 1, 1]) := by
                  rw [← dD.ofTorus_add, ← om200_add]
            _ = dD.ofTorus (om200 m ε) * (dD.a ^ 2 ^ (m + 1) * dD.b ^ 2 ^ (m + 1)) := by
                  rw [t200inv1_w0_eq]
  · cases i
    · cases jb
      · cases l
        · cases k
          · exfalso
            exact hD ⟨rfl, rfl, rfl, rfl⟩
          · exact key (Torus.ofInt _ ![(2 : ℤ) ^ m, (2 : ℤ) ^ m, (2 : ℤ) ^ m])
              false false false true (by simp)
              (by simpa [SigmaFourAction.d8Act] using
                t200inv1_u4_twist_e dD hm hrel hj)
        · cases k
          · exact key (Torus.ofInt _ ![0, 0, (2 : ℤ) ^ (m + 1)])
              false false true false (by simp)
              (by simpa [SigmaFourAction.d8Act] using t200inv1_u4_twist_u (m := m))
          · exact key (Torus.ofInt _ ![0, 0, (2 : ℤ) ^ (m + 1)])
              false false true true (by simp)
              (by simpa [SigmaFourAction.d8Act] using
                t200inv1_u4_twist_ue dD hm hrel hj)
      · cases l
        · cases k
          · exact key (Torus.ofInt _ ![0, 0, (2 : ℤ) ^ m]) false true false false
              (by simp)
              (by simpa [SigmaFourAction.d8Act] using t200inv1_u4_twist_t (m := m))
          · exfalso
            exact hnot v false (by simp [bpow])
        · exfalso
          simp at hjl
    · cases jb
      · cases l
        · cases k
          · exact key (Torus.ofInt _ ![(2 : ℤ) ^ m, (2 : ℤ) ^ m, (2 : ℤ) ^ m])
              true false false false (by simp)
              (by simpa [SigmaFourAction.d8Act] using t200inv1_u4_twist_uv (m := m))
          · exact key (Torus.ofInt _ ![0, (2 : ℤ) ^ m, 0]) true false false true
              (by simp)
              (by simpa [SigmaFourAction.d8Act] using
                t200inv1_u4_twist_uve dD hm hrel hj)
        · cases k
          · exact key (Torus.ofInt _ ![0, (2 : ℤ) ^ (m + 1), 0])
              true false true false (by simp)
              (by simpa [SigmaFourAction.d8Act] using t200inv1_u4_twist_uvu (m := m))
          · exact key (Torus.ofInt _ ![0, 0, (2 : ℤ) ^ (m + 1)])
              true false true true (by simp)
              (by simpa [SigmaFourAction.d8Act] using
                t200inv1_u4_twist_uvue dD hm hrel hj)
      · cases l
        · cases k
          · exact key (Torus.ofInt _ ![0, (2 : ℤ) ^ m, 0]) true true false false
              (by simp)
              (by simpa [SigmaFourAction.d8Act] using t200inv1_u4_twist_uvt (m := m))
          · exfalso
            exact hnot v true (by simp [bpow])
        · exfalso
          simp at hjl

theorem t200inv1_sqE_te_false {p : ℕ} (hrel : Rel34inv dD e 0 1 p) (x0 x1 x2 : ℤ) :
    (dD.t200inv1EAction hrel).sqE (Torus.ofInt _ ![x0, x1, x2]) false true false =
      Torus.ofInt _ ![x2, 2 * x1 - 4 * x0 + (p : ℤ) + 2 * x2, 2 * x2] := by
  have hφe : (dD.t200inv1EAction hrel).φe (Torus.ofInt _ ![x0, x1, x2]) =
      -Torus.ofInt _ ![x0, x1, x2] := by
    rw [StrothWeakTypeData.t200inv1_φe]
    rw [t200_neg_vec]
    congr 1
    funext i
    fin_cases i <;> simp
  have htw : (dD.t200inv1EAction hrel).twist false true =
      Torus.ofInt _ ![0, -(p : ℤ), 0] := by
    simp [StrothWeakTypeData.EAction.twist, StrothWeakTypeData.t200inv1EAction,
      SigmaFourAction.d8Act]
  have hsq : (dD.t200inv1EAction hrel).ve = 0 := rfl
  rw [StrothWeakTypeData.EAction.sqE, hsq, htw]
  simp only [map_zero, zero_add, sub_zero]
  rw [hφe]
  simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte,
    AddMonoidHom.comp_apply, AddMonoidHom.id_apply, t200_φt_vec, t200_add_vec, t200_neg_vec]
  funext i
  fin_cases i <;> ring_nf

theorem t200inv1_sqE_te_true {p : ℕ} (hrel : Rel34inv dD e 0 1 p) (x0 x1 x2 : ℤ) :
    (dD.t200inv1EAction hrel).sqE (Torus.ofInt _ ![x0, x1, x2]) true true false =
      Torus.ofInt _ ![x1, 2 * x1, -4 * x0 + 2 * x1 + 2 * x2 + (p : ℤ)] := by
  have hφe : (dD.t200inv1EAction hrel).φe (Torus.ofInt _ ![x0, x1, x2]) =
      -Torus.ofInt _ ![x0, x1, x2] := by
    rw [StrothWeakTypeData.t200inv1_φe]
    rw [t200_neg_vec]
    congr 1
    funext i
    fin_cases i <;> simp
  have htw : (dD.t200inv1EAction hrel).twist true true =
      Torus.ofInt _ ![0, 0, -(p : ℤ)] := by
    simp [StrothWeakTypeData.EAction.twist, StrothWeakTypeData.t200inv1EAction,
      SigmaFourAction.d8Act, t200_φuv_vec, t200_add_vec]
    congr 1
    funext i
    fin_cases i <;> ring_nf
  have hsq : (dD.t200inv1EAction hrel).ve = 0 := rfl
  rw [StrothWeakTypeData.EAction.sqE, hsq, htw]
  simp only [map_zero, zero_add, sub_zero]
  rw [hφe]
  simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte,
    AddMonoidHom.comp_apply, AddMonoidHom.id_apply, t200_φuv_vec, t200_φt_vec, t200_add_vec,
    t200_neg_vec]
  funext i
  fin_cases i <;> ring_nf

theorem t200inv1_te_mul_self_ne {p : ℕ} (hm : 1 ≤ m) (hp : Odd p) (hrel : Rel34inv dD e 0 1 p)
    (v : Torus (StrothTypeIndex.t200 m).k) (i : Bool) :
    dD.ofTorus v * dD.d8 i true false * e * (dD.ofTorus v * dD.d8 i true false * e) ≠ 1 := by
  have _ := hm
  intro h
  let hE := dD.t200inv1EAction hrel
  obtain ⟨x0, x1, x2, rfl⟩ := t200_exists_vec v
  have hsq := hE.nfe_e_mul_self (Torus.ofInt _ ![x0, x1, x2]) i true false
  rw [show (false && true) = false from rfl, dD.d8_fff, mul_one] at hsq
  rw [h] at hsq
  have hzero : hE.sqE (Torus.ofInt _ ![x0, x1, x2]) i true false = 0 :=
    dD.ofTorus_eq_one_iff.mp hsq.symm
  obtain ⟨k, hk⟩ := hp
  have hp' : Odd p := ⟨k, hk⟩
  have hk' : (p : ℤ) = 2 * (k : ℤ) + 1 := by omega
  cases i
  · rw [t200inv1_sqE_te_false dD hrel x0 x1 x2] at hzero
    rw [t200_ofInt_eq_zero_iff] at hzero
    obtain ⟨-, hdiv, -⟩ := hzero
    have hexpr : 2 * x1 - 4 * x0 + (p : ℤ) + 2 * x2 =
        2 * (x1 - 2 * x0 + x2) + (p : ℤ) := by ring
    obtain ⟨t, ht⟩ := hdiv
    have h2 : (2 : ℤ) ∣ 2 ^ (m + 2) * t := ⟨2 ^ (m + 1) * t, by ring⟩
    rw [← ht] at h2
    rw [hexpr] at h2
    obtain ⟨s, hs⟩ := h2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hs
    have hpeven : Even (p : ℤ) := ⟨s - (x1 - 2 * x0 + x2), by omega⟩
    have hpZ : Odd (p : ℤ) := by exact_mod_cast hp'
    exact (Int.not_even_iff_odd.mpr hpZ) hpeven
  · rw [t200inv1_sqE_te_true dD hrel x0 x1 x2] at hzero
    rw [t200_ofInt_eq_zero_iff] at hzero
    obtain ⟨-, -, hdiv⟩ := hzero
    have hexpr : -4 * x0 + 2 * x1 + 2 * x2 + (p : ℤ) =
        2 * (-2 * x0 + x1 + x2) + (p : ℤ) := by ring
    obtain ⟨t, ht⟩ := hdiv
    have h2 : (2 : ℤ) ∣ 2 ^ (m + 2) * t := ⟨2 ^ (m + 1) * t, by ring⟩
    rw [← ht] at h2
    rw [hexpr] at h2
    obtain ⟨s, hs⟩ := h2
    simp only [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hs
    have hpeven : Even (p : ℤ) := ⟨s - (-2 * x0 + x1 + x2), by omega⟩
    have hpZ : Odd (p : ℤ) := by exact_mod_cast hp'
    exact (Int.not_even_iff_odd.mpr hpZ) hpeven

theorem t200inv1_t78_conj_mul_three {g a b c : G} (hg : g * g = 1) :
    (g * a * g) * (g * b * g) * (g * c * g) = g * (a * b * c) * g := by
  calc (g * a * g) * (g * b * g) * (g * c * g)
      = g * a * (g * g) * b * (g * g) * c * g := by group
    _ = g * (a * b * c) * g := by rw [hg]; group

theorem t200inv1_t78_conj_mul_four {g a b c d : G} (hg : g * g = 1) :
    (g * a * g) * (g * b * g) * (g * c * g) * (g * d * g) = g * (a * b * c * d) * g := by
  calc (g * a * g) * (g * b * g) * (g * c * g) * (g * d * g)
      = g * a * (g * g) * b * (g * g) * c * (g * g) * d * g := by group
    _ = g * (a * b * c * d) * g := by rw [hg]; group

theorem t200inv1_t78_ue_mul_self {j p : ℕ} (hrel : Rel34inv dD e j 1 p) :
    (dD.u * e) * (dD.u * e) = 1 := by
  have heu := t200inv1_e_comm_u dD hrel
  calc (dD.u * e) * (dD.u * e) = dD.u * (e * dD.u) * e := by group
    _ = dD.u * (dD.u * e) * e := by rw [heu]
    _ = (dD.u * dD.u) * (e * e) := by group
    _ = 1 := by rw [dD.u_sq, hrel.e_sq, one_mul]

theorem t200inv1_t78_conj_ue {j p : ℕ} (hrel : Rel34inv dD e j 1 p)
    (v : Torus (StrothTypeIndex.t200 m).k) :
    (dD.u * e)⁻¹ * dD.ofTorus v * (dD.u * e) =
      dD.ofTorus ((dD.t200inv1EAction hrel).φe
        ((StrothTypeIndex.t200 m).action.φu v)) := by
  have hui : dD.u⁻¹ = dD.u := dD.u_inv
  have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_right hrel.e_sq
  have huw : dD.u * dD.ofTorus v * dD.u =
      dD.ofTorus ((StrothTypeIndex.t200 m).action.φu v) := by
    calc dD.u * dD.ofTorus v * dD.u
        = dD.ofTorus ((StrothTypeIndex.t200 m).action.φu v) * dD.u * dD.u := by
          rw [dD.u_mul_ofTorus]
      _ = dD.ofTorus ((StrothTypeIndex.t200 m).action.φu v) := by
          rw [mul_assoc, dD.u_sq, mul_one]
  calc (dD.u * e)⁻¹ * dD.ofTorus v * (dD.u * e)
      = e * (dD.u * dD.ofTorus v * dD.u) * e := by rw [mul_inv_rev, hui, hei]; group
    _ = e * dD.ofTorus ((StrothTypeIndex.t200 m).action.φu v) * e := by rw [huw]
    _ = dD.ofTorus ((dD.t200inv1EAction hrel).φe
          ((StrothTypeIndex.t200 m).action.φu v)) := by
        have h := (dD.t200inv1EAction hrel).conj_ofTorus
          ((StrothTypeIndex.t200 m).action.φu v)
        rwa [hei] at h

theorem t200inv1_t78_conj_uv {p : ℕ} (hrel : Rel34inv dD e 0 1 p)
    (v : Torus (StrothTypeIndex.t200 m).k) :
    dD.uv * (dD.ofTorus v * (dD.u * e)) * dD.uv =
      dD.ofTorus ((StrothTypeIndex.t200 m).action.φuv v -
        Torus.ofInt _ ![(p : ℤ), (p : ℤ), (p : ℤ)]) * (dD.u * e) := by
  let hE := dD.t200inv1EAction hrel
  have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_right hrel.e_sq
  have huv : dD.uv * dD.ofTorus v * dD.uv =
      dD.ofTorus ((StrothTypeIndex.t200 m).action.φuv v) := by
    calc dD.uv * dD.ofTorus v * dD.uv
        = dD.ofTorus ((StrothTypeIndex.t200 m).action.φuv v) * dD.uv * dD.uv := by
          rw [dD.uv_mul_ofTorus]
      _ = dD.ofTorus ((StrothTypeIndex.t200 m).action.φuv v) := by
          rw [mul_assoc, dD.uv_sq, mul_one]
  have hu : dD.uv * dD.u * dD.uv = dD.u := by
    calc dD.uv * dD.u * dD.uv = dD.u * dD.uv * dD.uv := by rw [dD.uv_comm_u]
      _ = dD.u := by rw [mul_assoc, dD.uv_sq, mul_one]
  have hwuv : hE.wuv = Torus.ofInt _ ![(p : ℤ), (p : ℤ), (p : ℤ)] := rfl
  have hφe : hE.φe hE.wuv = -hE.wuv := by
    rw [hwuv, StrothWeakTypeData.t200inv1_φe dD hrel, t200_neg_vec]
    congr 1
    funext i
    fin_cases i <;> simp
  have hφu : (StrothTypeIndex.t200 m).action.φu (-hE.wuv) = -hE.wuv := by
    rw [hwuv, map_neg, t200_φu_vec]
  have heuv : dD.uv * e * dD.uv = e * dD.ofTorus hE.wuv := by
    have h : e * dD.uv * e = dD.ofTorus hE.wuv * dD.uv := by
      have := hE.conj_uv
      rwa [hei] at this
    calc dD.uv * e * dD.uv = e * (e * dD.uv * e) * dD.uv := by
          rw [show e * (e * dD.uv * e) * dD.uv = (e * e) * (dD.uv * e * dD.uv) by group,
            hrel.e_sq, one_mul]
      _ = e * (dD.ofTorus hE.wuv * dD.uv) * dD.uv := by rw [h]
      _ = e * dD.ofTorus hE.wuv := by
          rw [show e * (dD.ofTorus hE.wuv * dD.uv) * dD.uv =
            e * dD.ofTorus hE.wuv * (dD.uv * dD.uv) by group, dD.uv_sq, mul_one]
  calc dD.uv * (dD.ofTorus v * (dD.u * e)) * dD.uv
      = (dD.uv * dD.ofTorus v * dD.uv) * (dD.uv * dD.u * dD.uv) *
          (dD.uv * e * dD.uv) := by
        rw [t200inv1_t78_conj_mul_three dD.uv_sq]
        group
    _ = dD.ofTorus ((StrothTypeIndex.t200 m).action.φuv v) * dD.u *
          (e * dD.ofTorus hE.wuv) := by rw [huv, hu, heuv]
    _ = dD.ofTorus ((StrothTypeIndex.t200 m).action.φuv v) * dD.u *
          (dD.ofTorus (hE.φe hE.wuv) * e) := by rw [hE.e_mul_ofTorus]
    _ = dD.ofTorus ((StrothTypeIndex.t200 m).action.φuv v) *
          (dD.u * dD.ofTorus (hE.φe hE.wuv)) * e := by group
    _ = dD.ofTorus ((StrothTypeIndex.t200 m).action.φuv v) *
          (dD.ofTorus ((StrothTypeIndex.t200 m).action.φu (hE.φe hE.wuv)) * dD.u) * e := by
        rw [dD.u_mul_ofTorus]
    _ = (dD.ofTorus ((StrothTypeIndex.t200 m).action.φuv v) *
          dD.ofTorus ((StrothTypeIndex.t200 m).action.φu (hE.φe hE.wuv))) * dD.u * e := by
        group
    _ = dD.ofTorus ((StrothTypeIndex.t200 m).action.φuv v +
          (StrothTypeIndex.t200 m).action.φu (hE.φe hE.wuv)) * dD.u * e := by
        rw [← dD.ofTorus_add]
    _ = dD.ofTorus ((StrothTypeIndex.t200 m).action.φuv v - hE.wuv) * (dD.u * e) := by
        rw [hφe, hφu, sub_eq_add_neg]
        rw [mul_assoc]

theorem t200inv1_t78_conj_t {p : ℕ} (hrel : Rel34inv dD e 0 1 p)
    (v : Torus (StrothTypeIndex.t200 m).k) :
    ∃ v' : Torus (StrothTypeIndex.t200 m).k,
      dD.t * (dD.ofTorus v * (dD.u * e)) * dD.t =
        dD.ofTorus v' * (dD.uv * dD.u * e) := by
  let hE := dD.t200inv1EAction hrel
  have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_right hrel.e_sq
  have hA : (dD.a : G) ^ p = dD.ofTorus (Torus.ofInt _ ![0, (p : ℤ), 0]) := by
    rw [dD.a_eq, ← dD.ofTorus_nsmul, a_eq_ofInt, ← natCast_zsmul, t200_zsmul_vec]
    congr 1
    funext i
    fin_cases i <;> simp
  have hAine : ((dD.a : G) ^ p)⁻¹ =
      dD.ofTorus (Torus.ofInt _ ![0, -(p : ℤ), 0]) := by
    rw [hA, ← dD.ofTorus_neg, t200_neg_vec]
    simp
  have htv : dD.t * dD.ofTorus v * dD.t =
      dD.ofTorus ((StrothTypeIndex.t200 m).action.φt v) := by
    calc dD.t * dD.ofTorus v * dD.t
        = dD.ofTorus ((StrothTypeIndex.t200 m).action.φt v) * dD.t * dD.t := by
          rw [dD.t_mul_ofTorus]
      _ = dD.ofTorus ((StrothTypeIndex.t200 m).action.φt v) := by
          rw [mul_assoc, dD.t_sq, mul_one]
  have htu : dD.t * dD.u * dD.t = dD.uv * dD.u := by
    calc dD.t * dD.u * dD.t = (dD.t * dD.u) * dD.t := rfl
      _ = (dD.u * dD.uv * dD.t) * dD.t := by rw [dD.t_u]
      _ = dD.u * dD.uv * (dD.t * dD.t) := by group
      _ = dD.u * dD.uv := by rw [dD.t_sq, mul_one]
      _ = dD.uv * dD.u := dD.uv_comm_u.symm
  have hte : dD.t * e * dD.t = dD.ofTorus (Torus.ofInt _ ![0, (p : ℤ), 0]) * e := by
    have h : e * dD.t * e = ((dD.a : G) ^ p)⁻¹ * dD.t := by
      have := hrel.t_conj
      rwa [hei] at this
    have h1 : dD.t * e * dD.t = e * ((dD.a : G) ^ p)⁻¹ := by
      calc dD.t * e * dD.t
          = (e * e) * (dD.t * e * dD.t) := by rw [hrel.e_sq, one_mul]
        _ = e * (e * dD.t * e) * dD.t := by group
        _ = e * (((dD.a : G) ^ p)⁻¹ * dD.t) * dD.t := by rw [h]
        _ = e * ((dD.a : G) ^ p)⁻¹ * (dD.t * dD.t) := by group
        _ = e * ((dD.a : G) ^ p)⁻¹ := by rw [dD.t_sq, mul_one]
    rw [h1, hAine, hE.e_mul_ofTorus]
    congr 1
    rw [StrothWeakTypeData.t200inv1_φe dD hrel]
    congr 1
    funext i
    fin_cases i <;> simp
  refine ⟨(StrothTypeIndex.t200 m).action.φt v +
    (StrothTypeIndex.t200 m).action.φuv
      ((StrothTypeIndex.t200 m).action.φu (Torus.ofInt _ ![0, (p : ℤ), 0])), ?_⟩
  calc dD.t * (dD.ofTorus v * (dD.u * e)) * dD.t
      = (dD.t * dD.ofTorus v * dD.t) * (dD.t * dD.u * dD.t) *
          (dD.t * e * dD.t) := by
        rw [t200inv1_t78_conj_mul_three dD.t_sq]
        group
    _ = dD.ofTorus ((StrothTypeIndex.t200 m).action.φt v) * (dD.uv * dD.u) *
          (dD.ofTorus (Torus.ofInt _ ![0, (p : ℤ), 0]) * e) := by rw [htv, htu, hte]
    _ = dD.ofTorus ((StrothTypeIndex.t200 m).action.φt v) *
          ((dD.uv * dD.u) * dD.ofTorus (Torus.ofInt _ ![0, (p : ℤ), 0])) * e := by group
    _ = dD.ofTorus ((StrothTypeIndex.t200 m).action.φt v) *
          (dD.ofTorus ((StrothTypeIndex.t200 m).action.φuv
            ((StrothTypeIndex.t200 m).action.φu (Torus.ofInt _ ![0, (p : ℤ), 0]))) *
            (dD.uv * dD.u)) * e := by
        rw [show dD.uv * dD.u = dD.d8 true false true from dD.d8_tft.symm,
          dD.d8_mul_ofTorus]
        congr 2
    _ = (dD.ofTorus ((StrothTypeIndex.t200 m).action.φt v) *
          dD.ofTorus ((StrothTypeIndex.t200 m).action.φuv
            ((StrothTypeIndex.t200 m).action.φu (Torus.ofInt _ ![0, (p : ℤ), 0])))) *
          (dD.uv * dD.u) * e := by group
    _ = dD.ofTorus ((StrothTypeIndex.t200 m).action.φt v +
          (StrothTypeIndex.t200 m).action.φuv
            ((StrothTypeIndex.t200 m).action.φu (Torus.ofInt _ ![0, (p : ℤ), 0]))) *
          (dD.uv * dD.u) * e := by rw [← dD.ofTorus_add]
    _ = dD.ofTorus ((StrothTypeIndex.t200 m).action.φt v +
          (StrothTypeIndex.t200 m).action.φuv
            ((StrothTypeIndex.t200 m).action.φu (Torus.ofInt _ ![0, (p : ℤ), 0]))) *
          (dD.uv * dD.u * e) := by rw [mul_assoc]

theorem t200inv1_t78_conj_u {j p : ℕ} (hrel : Rel34inv dD e j 1 p)
    (v : Torus (StrothTypeIndex.t200 m).k) :
    dD.u * (dD.ofTorus v * (dD.uv * dD.u * e)) * dD.u =
      dD.ofTorus ((StrothTypeIndex.t200 m).action.φu v) * (dD.uv * dD.u * e) := by
  have heu := t200inv1_e_comm_u dD hrel
  have hua : dD.u * dD.ofTorus v * dD.u =
      dD.ofTorus ((StrothTypeIndex.t200 m).action.φu v) := by
    calc dD.u * dD.ofTorus v * dD.u
        = dD.ofTorus ((StrothTypeIndex.t200 m).action.φu v) * dD.u * dD.u := by
          rw [dD.u_mul_ofTorus]
      _ = dD.ofTorus ((StrothTypeIndex.t200 m).action.φu v) := by
          rw [mul_assoc, dD.u_sq, mul_one]
  have huv : dD.u * dD.uv * dD.u = dD.uv := by
    calc dD.u * dD.uv * dD.u = dD.uv * dD.u * dD.u := by rw [dD.uv_comm_u]
      _ = dD.uv := by rw [mul_assoc, dD.u_sq, mul_one]
  have huu : dD.u * dD.u * dD.u = dD.u := by rw [dD.u_sq, one_mul]
  have hue : dD.u * e * dD.u = e := by
    calc dD.u * e * dD.u = e * dD.u * dD.u := by rw [← heu]
      _ = e := by rw [mul_assoc, dD.u_sq, mul_one]
  calc dD.u * (dD.ofTorus v * (dD.uv * dD.u * e)) * dD.u
      = (dD.u * dD.ofTorus v * dD.u) * (dD.u * dD.uv * dD.u) *
          (dD.u * dD.u * dD.u) * (dD.u * e * dD.u) := by
        rw [t200inv1_t78_conj_mul_four dD.u_sq]
        group
    _ = dD.ofTorus ((StrothTypeIndex.t200 m).action.φu v) * (dD.uv * dD.u * e) := by
        rw [hua, huv, huu, hue]
        group

theorem t200inv1_t78_conj_e {j p : ℕ} (hrel : Rel34inv dD e j 1 p)
    (v : Torus (StrothTypeIndex.t200 m).k) :
    ∃ v' : Torus (StrothTypeIndex.t200 m).k,
      e * (dD.ofTorus v * (dD.uv * dD.u * e)) * e =
        dD.ofTorus v' * (dD.uv * dD.u * e) := by
  let hE := dD.t200inv1EAction hrel
  have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_right hrel.e_sq
  have hev : e * dD.ofTorus v * e =
      dD.ofTorus ((dD.t200inv1EAction hrel).φe v) := by
    have h := hE.conj_ofTorus v
    rwa [hei] at h
  have heuv : e * dD.uv * e = dD.ofTorus hE.wuv * dD.uv := by
    have h := hE.conj_uv
    rwa [hei] at h
  have heu : e * dD.u * e = dD.u := by
    calc e * dD.u * e = dD.u * e * e := by rw [t200inv1_e_comm_u dD hrel]
      _ = dD.u := by rw [mul_assoc, hrel.e_sq, mul_one]
  have hee : e * e * e = e := by rw [hrel.e_sq, one_mul]
  have hwuv : hE.wuv = Torus.ofInt _ ![(p : ℤ), (p : ℤ), (p : ℤ)] := rfl
  refine ⟨hE.φe v + hE.wuv, ?_⟩
  calc e * (dD.ofTorus v * (dD.uv * dD.u * e)) * e
      = (e * dD.ofTorus v * e) * (e * dD.uv * e) * (e * dD.u * e) * (e * e * e) := by
        rw [t200inv1_t78_conj_mul_four hrel.e_sq]
        group
    _ = dD.ofTorus (hE.φe v) * (dD.ofTorus hE.wuv * dD.uv) * dD.u * e := by
        rw [hev, heuv, heu, hee]
    _ = dD.ofTorus (hE.φe v) * (((dD.ofTorus hE.wuv) * (dD.uv * dD.u))) * e := by group
    _ = (dD.ofTorus (hE.φe v) * dD.ofTorus hE.wuv) * dD.d8 true false true * e := by
        rw [dD.d8_tft]
        group
    _ = dD.ofTorus (hE.φe v + hE.wuv) * dD.d8 true false true * e := by
        rw [← dD.ofTorus_add]
    _ = dD.ofTorus (hE.φe v + hE.wuv) * (dD.uv * dD.u * e) := by
        rw [dD.d8_tft, mul_assoc]

theorem t200inv1_t78_involution_vec {p : ℕ} (hrel : Rel34inv dD e 0 1 p)
    (z : Fin 3 → ℤ)
    (h : (dD.ofTorus (Torus.ofInt _ z) * (dD.u * e)) *
      (dD.ofTorus (Torus.ofInt _ z) * (dD.u * e)) = 1) :
    (2 : ℤ) ∣ z 1 - z 2 := by
  have hsq : dD.ofTorus (Torus.ofInt _ z + (dD.t200inv1EAction hrel).φe
      ((StrothTypeIndex.t200 m).action.φu (Torus.ofInt _ z))) = 1 := by
    have hthis := mul_self_ofTorus_mul_of_action dD
      (σ := dD.u * e) (φ := (dD.t200inv1EAction hrel).φe.comp
        ((StrothTypeIndex.t200 m).action.φu))
      (t200inv1_t78_ue_mul_self dD hrel) (t200inv1_t78_conj_ue dD hrel)
      (Torus.ofInt _ z)
    rw [h] at hthis
    exact hthis.symm
  rw [dD.ofTorus_eq_one_iff] at hsq
  have hz : Torus.ofInt (StrothTypeIndex.t200 m).k z =
      Torus.ofInt (StrothTypeIndex.t200 m).k ![z 0, z 1, z 2] := by
    congr 1
    funext i
    fin_cases i <;> rfl
  have hvec : Torus.ofInt _ z + (dD.t200inv1EAction hrel).φe
      ((StrothTypeIndex.t200 m).action.φu (Torus.ofInt _ z)) =
      Torus.ofInt _ ![0, z 1 - z 2, z 2 - z 1] := by
    rw [hz, t200inv1_φue dD hrel, t200_add_vec]
    congr 1
    funext i
    fin_cases i <;> simp <;> ring_nf
  rw [hvec] at hsq
  rw [t200_ofInt_eq_zero_iff] at hsq
  obtain ⟨-, hdiv, -⟩ := hsq
  exact dvd_trans (dvd_pow_self 2 (by omega : m + 2 ≠ 0)) hdiv

theorem t200inv1_t78_uv_wstep {p : ℕ} (hrel : Rel34inv dD e 0 1 p)
    (z w : Fin 3 → ℤ) :
    (dD.ofTorus (Torus.ofInt _ w))⁻¹ *
        (dD.ofTorus (Torus.ofInt _ z) * (dD.u * e)) *
        dD.ofTorus (Torus.ofInt _ w) =
      dD.ofTorus (Torus.ofInt _ ![z 0 - 2 * w 0, z 1 - w 1 - w 2,
        z 2 - w 1 - w 2]) * (dD.u * e) := by
  have hw := conj_ofTorus_mul_of_action dD
    (σ := dD.u * e) (φ := (dD.t200inv1EAction hrel).φe.comp
      ((StrothTypeIndex.t200 m).action.φu))
    (t200inv1_t78_ue_mul_self dD hrel) (t200inv1_t78_conj_ue dD hrel)
    (Torus.ofInt _ w) (Torus.ofInt _ z)
  have hφw : (dD.t200inv1EAction hrel).φe
      ((StrothTypeIndex.t200 m).action.φu (Torus.ofInt _ w)) =
      Torus.ofInt _ ![-w 0, -w 2, -w 1] := by
    rw [t200inv1_φue dD hrel]
    congr 1
    funext i
    fin_cases i <;> simp
  simp only [AddMonoidHom.comp_apply] at hw
  rw [hφw] at hw
  have hz : Torus.ofInt (StrothTypeIndex.t200 m).k z =
      Torus.ofInt (StrothTypeIndex.t200 m).k ![z 0, z 1, z 2] := by
    congr 1
    funext i
    fin_cases i <;> rfl
  have hw0 : Torus.ofInt (StrothTypeIndex.t200 m).k w =
      Torus.ofInt (StrothTypeIndex.t200 m).k ![w 0, w 1, w 2] := by
    congr 1
    funext i
    fin_cases i <;> rfl
  have hvec : Torus.ofInt (StrothTypeIndex.t200 m).k z +
        Torus.ofInt (StrothTypeIndex.t200 m).k ![-w 0, -w 2, -w 1] -
        Torus.ofInt (StrothTypeIndex.t200 m).k w =
      Torus.ofInt (StrothTypeIndex.t200 m).k
        ![z 0 - 2 * w 0, z 1 - w 1 - w 2, z 2 - w 1 - w 2] := by
    rw [hz, hw0, t200_add_vec, t200_sub_vec]
    congr 1
    funext i
    fin_cases i <;> simp <;> ring
  rwa [hvec] at hw

theorem t200inv1_t78_uv_uvstep {p : ℕ} (hrel : Rel34inv dD e 0 1 p)
    (z w : Fin 3 → ℤ) :
    dD.uv * (dD.ofTorus (Torus.ofInt _ ![z 0 - 2 * w 0, z 1 - w 1 - w 2,
        z 2 - w 1 - w 2]) * (dD.u * e)) * dD.uv =
      dD.ofTorus (Torus.ofInt _ ![-3 * (z 0 - 2 * w 0) + (z 1 - w 1 - w 2) +
          (z 2 - w 1 - w 2) - (p : ℤ),
        -4 * (z 0 - 2 * w 0) + (z 1 - w 1 - w 2) + 2 * (z 2 - w 1 - w 2) - (p : ℤ),
        -4 * (z 0 - 2 * w 0) + 2 * (z 1 - w 1 - w 2) + (z 2 - w 1 - w 2) - (p : ℤ)]) *
        (dD.u * e) := by
  have h := t200inv1_t78_conj_uv dD hrel
    (Torus.ofInt _ ![z 0 - 2 * w 0, z 1 - w 1 - w 2, z 2 - w 1 - w 2])
  rw [h]
  congr 1
  rw [t200_φuv_vec, t200_sub_vec]

theorem t200inv1_t78_u_step {p : ℕ} (hrel : Rel34inv dD e 0 1 p)
    (v : Fin 3 → ℤ) :
    dD.u * (dD.ofTorus (Torus.ofInt _ v) * (dD.u * e)) * dD.u =
      dD.ofTorus (Torus.ofInt _ ![v 0, v 2, v 1]) * (dD.u * e) := by
  have hua : dD.u * dD.ofTorus (Torus.ofInt _ v) * dD.u =
      dD.ofTorus ((StrothTypeIndex.t200 m).action.φu (Torus.ofInt _ v)) := by
    calc dD.u * dD.ofTorus (Torus.ofInt _ v) * dD.u
        = dD.ofTorus ((StrothTypeIndex.t200 m).action.φu (Torus.ofInt _ v)) * dD.u * dD.u := by
          rw [dD.u_mul_ofTorus]
      _ = dD.ofTorus ((StrothTypeIndex.t200 m).action.φu (Torus.ofInt _ v)) := by
          rw [mul_assoc, dD.u_sq, mul_one]
  have huu : dD.u * dD.u * dD.u = dD.u := by rw [dD.u_sq, one_mul]
  have hue : dD.u * e * dD.u = e := by
    calc dD.u * e * dD.u = e * dD.u * dD.u := by rw [← t200inv1_e_comm_u dD hrel]
      _ = e := by rw [mul_assoc, dD.u_sq, mul_one]
  calc dD.u * (dD.ofTorus (Torus.ofInt _ v) * (dD.u * e)) * dD.u
      = (dD.u * dD.ofTorus (Torus.ofInt _ v) * dD.u) * (dD.u * dD.u * dD.u) *
          (dD.u * e * dD.u) := by
        rw [t200inv1_t78_conj_mul_three dD.u_sq]
        group
    _ = dD.ofTorus ((StrothTypeIndex.t200 m).action.φu (Torus.ofInt _ v)) * dD.u * e := by
        rw [hua, huu, hue]
    _ = dD.ofTorus (Torus.ofInt _ ![v 0, v 2, v 1]) * dD.u * e := by
        have hv : Torus.ofInt (StrothTypeIndex.t200 m).k v =
            Torus.ofInt (StrothTypeIndex.t200 m).k ![v 0, v 1, v 2] := by
          congr 1
          funext i
          fin_cases i <;> rfl
        rw [hv, t200_φu_vec]
    _ = dD.ofTorus (Torus.ofInt _ ![v 0, v 2, v 1]) * (dD.u * e) := by rw [mul_assoc]

theorem t200inv1_t78_e_step {p : ℕ} (hrel : Rel34inv dD e 0 1 p)
    (v : Fin 3 → ℤ) :
    e * (dD.ofTorus (Torus.ofInt _ v) * (dD.u * e)) * e =
      dD.ofTorus (Torus.ofInt _ ![-v 0, -v 1, -v 2]) * (dD.u * e) := by
  have hev : e * dD.ofTorus (Torus.ofInt _ v) * e =
      dD.ofTorus ((dD.t200inv1EAction hrel).φe (Torus.ofInt _ v)) := by
    have h := (dD.t200inv1EAction hrel).conj_ofTorus (Torus.ofInt _ v)
    rwa [inv_eq_of_mul_eq_one_right hrel.e_sq] at h
  have heu : e * dD.u * e = dD.u := by
    calc e * dD.u * e = dD.u * e * e := by rw [t200inv1_e_comm_u dD hrel]
      _ = dD.u := by rw [mul_assoc, hrel.e_sq, mul_one]
  have hee : e * e * e = e := by rw [hrel.e_sq, one_mul]
  calc e * (dD.ofTorus (Torus.ofInt _ v) * (dD.u * e)) * e
      = (e * dD.ofTorus (Torus.ofInt _ v) * e) * (e * dD.u * e) * (e * e * e) := by
        rw [t200inv1_t78_conj_mul_three hrel.e_sq]
        group
    _ = dD.ofTorus ((dD.t200inv1EAction hrel).φe (Torus.ofInt _ v)) * dD.u * e := by
        rw [hev, heu, hee]
    _ = dD.ofTorus (Torus.ofInt _ ![-v 0, -v 1, -v 2]) * dD.u * e := by
        rw [StrothWeakTypeData.t200inv1_φe dD hrel]
        have hv : (![-v 0, (-1 + ((0 : ℕ) : ℤ)) * v 1,
            (-1 + ((0 : ℕ) : ℤ)) * v 2] : Fin 3 → ℤ) = ![-v 0, -v 1, -v 2] := by
          funext i
          fin_cases i <;> norm_num
        rw [hv]
    _ = dD.ofTorus (Torus.ofInt _ ![-v 0, -v 1, -v 2]) * (dD.u * e) := by rw [mul_assoc]

theorem t200inv1_t78_uv_A_parity {p : ℕ} (hp : Odd p) (z w : Fin 3 → ℤ)
    (hbc : (2 : ℤ) ∣ z 1 - z 2) :
    (¬ (2 : ℤ) ∣ z 0 - (-3 * (z 0 - 2 * w 0) + (z 1 - w 1 - w 2) +
        (z 2 - w 1 - w 2) - (p : ℤ))) ∧
      ¬ (2 : ℤ) ∣ z 0 + (-3 * (z 0 - 2 * w 0) + (z 1 - w 1 - w 2) +
        (z 2 - w 1 - w 2) - (p : ℤ)) := by
  obtain ⟨k1, hk1⟩ := hbc
  obtain ⟨k2, hk2⟩ := hp
  have hk2' : (p : ℤ) = 2 * (k2 : ℤ) + 1 := by omega
  constructor
  · intro hd
    obtain ⟨c, hc⟩ := hd
    omega
  · intro hd
    obtain ⟨c, hc⟩ := hd
    omega

theorem t200inv1_t78_uv_contra {p : ℕ} (hm : 1 ≤ m) (hp : Odd p)
    (hrel : Rel34inv dD e 0 1 p) (z w : Fin 3 → ℤ) (l k : Bool)
    (hbc : (2 : ℤ) ∣ z 1 - z 2)
    (hconj : (dD.ofTorus (Torus.ofInt _ w) * dD.d8 true false l * bpow e k)⁻¹ *
      (dD.ofTorus (Torus.ofInt _ z) * (dD.u * e)) *
      (dD.ofTorus (Torus.ofInt _ w) * dD.d8 true false l * bpow e k) =
      dD.ofTorus (Torus.ofInt _ z) * (dD.u * e)) : False := by
  let X := dD.ofTorus (Torus.ofInt _ z)
  let W := dD.ofTorus (Torus.ofInt _ w)
  set v2 : Fin 3 → ℤ := ![-3 * (z 0 - 2 * w 0) + (z 1 - w 1 - w 2) +
      (z 2 - w 1 - w 2) - (p : ℤ),
    -4 * (z 0 - 2 * w 0) + (z 1 - w 1 - w 2) + 2 * (z 2 - w 1 - w 2) - (p : ℤ),
    -4 * (z 0 - 2 * w 0) + 2 * (z 1 - w 1 - w 2) + (z 2 - w 1 - w 2) - (p : ℤ)] with hv2
  have hx : dD.ofTorus (Torus.ofInt _ w) * dD.d8 true false l * bpow e k =
      W * dD.uv * dD.d8 false false l * bpow e k := by
    rw [show dD.d8 true false l = dD.uv * dD.d8 false false l by
      simp [StrothWeakTypeData.d8]]
    rw [show W = dD.ofTorus (Torus.ofInt _ w) from rfl]
    group
  rw [hx] at hconj
  have hEinv : (bpow e k)⁻¹ = bpow e k := by
    cases k
    · simp [Stroth42Core.bpow]
    · simp only [Stroth42Core.bpow, ↓reduceIte]
      exact inv_eq_of_mul_eq_one_right hrel.e_sq
  have hUinv : (dD.d8 false false l)⁻¹ = dD.d8 false false l := by
    cases l
    · rw [dD.d8_fff]; simp
    · rw [dD.d8_fft]; exact dD.u_inv
  have hc : bpow e k * dD.d8 false false l *
      (dD.uv * (W⁻¹ * (X * (dD.u * e)) * W) * dD.uv) *
      dD.d8 false false l * bpow e k = X * (dD.u * e) := by
    calc bpow e k * dD.d8 false false l *
          (dD.uv * (W⁻¹ * (X * (dD.u * e)) * W) * dD.uv) *
          dD.d8 false false l * bpow e k
        = (W * dD.uv * dD.d8 false false l * bpow e k)⁻¹ * (X * (dD.u * e)) *
            (W * dD.uv * dD.d8 false false l * bpow e k) := by
          rw [mul_inv_rev, mul_inv_rev, mul_inv_rev, dD.uv_inv, hUinv, hEinv]
          group
      _ = X * (dD.u * e) := hconj
  rw [t200inv1_t78_uv_wstep dD hrel z w] at hc
  rw [t200inv1_t78_uv_uvstep dD hrel z w, ← hv2] at hc
  have hA : v2 0 = -3 * (z 0 - 2 * w 0) + (z 1 - w 1 - w 2) +
      (z 2 - w 1 - w 2) - (p : ℤ) := by rw [hv2]; rfl
  obtain ⟨hpar1, hpar2⟩ := t200inv1_t78_uv_A_parity hp z w hbc
  cases l <;> cases k
  · simp only [Stroth42Core.bpow, Bool.false_eq_true, ↓reduceIte, mul_one, one_mul,
      dD.d8_fff] at hc
    have hfin : dD.ofTorus (Torus.ofInt _ v2) = X := mul_right_cancel hc
    have hz : dD.ofTorus (Torus.ofInt _ v2) = dD.ofTorus (Torus.ofInt _ z) := hfin
    have hdiv : (2 : ℤ) ^ m ∣ z 0 - v2 0 :=
      (t200_ofInt_eq_iff v2 z).mp (dD.ofTorus_inj hz) |>.1
    exact hpar1 (by
      rw [hA] at hdiv
      exact dvd_trans (dvd_pow_self 2 (by omega : m ≠ 0)) hdiv)
  · simp only [Stroth42Core.bpow, ↓reduceIte, mul_one, dD.d8_fff] at hc
    rw [t200inv1_t78_e_step dD hrel v2] at hc
    have hfin : dD.ofTorus (Torus.ofInt _ ![-v2 0, -v2 1, -v2 2]) = X :=
      mul_right_cancel hc
    have hz : dD.ofTorus (Torus.ofInt _ ![-v2 0, -v2 1, -v2 2]) =
        dD.ofTorus (Torus.ofInt _ z) := hfin
    have hdiv : (2 : ℤ) ^ m ∣ z 0 - (-v2 0) :=
      (t200_ofInt_eq_iff ![-v2 0, -v2 1, -v2 2] z).mp (dD.ofTorus_inj hz) |>.1
    have hdiv' : (2 : ℤ) ^ m ∣ z 0 + v2 0 := by
      rwa [show z 0 - -v2 0 = z 0 + v2 0 by ring] at hdiv
    refine hpar2 ?_
    rw [hA] at hdiv'
    exact dvd_trans (dvd_pow_self 2 (by omega : m ≠ 0)) hdiv'
  · simp only [Stroth42Core.bpow, Bool.false_eq_true, ↓reduceIte, mul_one, one_mul,
      dD.d8_fft] at hc
    rw [t200inv1_t78_u_step dD hrel v2] at hc
    have hfin : dD.ofTorus (Torus.ofInt _ ![v2 0, v2 2, v2 1]) = X :=
      mul_right_cancel hc
    have hz : dD.ofTorus (Torus.ofInt _ ![v2 0, v2 2, v2 1]) =
        dD.ofTorus (Torus.ofInt _ z) := hfin
    have hdiv : (2 : ℤ) ^ m ∣ z 0 - v2 0 :=
      (t200_ofInt_eq_iff ![v2 0, v2 2, v2 1] z).mp (dD.ofTorus_inj hz) |>.1
    exact hpar1 (by
      rw [hA] at hdiv
      exact dvd_trans (dvd_pow_self 2 (by omega : m ≠ 0)) hdiv)
  · simp only [Stroth42Core.bpow, ↓reduceIte, dD.d8_fft] at hc
    rw [show e * dD.u * (dD.ofTorus (Torus.ofInt _ v2) * (dD.u * e)) * dD.u * e =
        e * (dD.u * (dD.ofTorus (Torus.ofInt _ v2) * (dD.u * e)) * dD.u) * e by
      group] at hc
    rw [t200inv1_t78_u_step dD hrel v2] at hc
    rw [t200inv1_t78_e_step dD hrel ![v2 0, v2 2, v2 1]] at hc
    have hfin : dD.ofTorus (Torus.ofInt _ ![-v2 0, -v2 2, -v2 1]) = X :=
      mul_right_cancel hc
    have hz : dD.ofTorus (Torus.ofInt _ ![-v2 0, -v2 2, -v2 1]) =
        dD.ofTorus (Torus.ofInt _ z) := hfin
    have hdiv : (2 : ℤ) ^ m ∣ z 0 - (-v2 0) :=
      (t200_ofInt_eq_iff ![-v2 0, -v2 2, -v2 1] z).mp (dD.ofTorus_inj hz) |>.1
    have hdiv' : (2 : ℤ) ^ m ∣ z 0 + v2 0 := by
      rwa [show z 0 - -v2 0 = z 0 + v2 0 by ring] at hdiv
    refine hpar2 ?_
    rw [hA] at hdiv'
    exact dvd_trans (dvd_pow_self 2 (by omega : m ≠ 0)) hdiv'

theorem t200inv1_t78_cancel_ue (hm : 1 ≤ m)
    (v : Torus (StrothTypeIndex.t200 m).k) (z : Fin 3 → ℤ)
    (h : dD.ofTorus v * (dD.uv * dD.u * e) =
      dD.ofTorus (Torus.ofInt _ z) * (dD.u * e)) : False := by
  have h1 : (dD.ofTorus v * dD.uv * dD.u) * e =
      (dD.ofTorus (Torus.ofInt _ z) * dD.u) * e := by
    rw [show (dD.ofTorus v * dD.uv * dD.u) * e =
        dD.ofTorus v * (dD.uv * dD.u * e) by group,
      show (dD.ofTorus (Torus.ofInt _ z) * dD.u) * e =
        dD.ofTorus (Torus.ofInt _ z) * (dD.u * e) by group, h]
  have h2 : dD.ofTorus v * dD.uv * dD.u = dD.ofTorus (Torus.ofInt _ z) * dD.u :=
    mul_right_cancel h1
  have h3 : (dD.ofTorus v * dD.uv) * dD.u =
      dD.ofTorus (Torus.ofInt _ z) * dD.u := h2
  have h4 : dD.ofTorus v * dD.uv = dD.ofTorus (Torus.ofInt _ z) := mul_right_cancel h3
  have h5 : dD.ofTorus v * dD.d8 true false false =
      dD.ofTorus (Torus.ofInt _ z) * dD.d8 false false false := by
    rw [dD.d8_tff, dD.d8_fff, mul_one]
    exact h4
  obtain ⟨-, hi, -, -⟩ := dD.nf_inj (t200_faithful hm) h5
  exact Bool.noConfusion hi

theorem t200inv1_t78_t_contra {p : ℕ} (hm : 1 ≤ m) (hrel : Rel34inv dD e 0 1 p)
    (z w : Fin 3 → ℤ) (l k : Bool)
    (hconj : (dD.ofTorus (Torus.ofInt _ w) * dD.d8 false true l * bpow e k)⁻¹ *
      (dD.ofTorus (Torus.ofInt _ z) * (dD.u * e)) *
      (dD.ofTorus (Torus.ofInt _ w) * dD.d8 false true l * bpow e k) =
      dD.ofTorus (Torus.ofInt _ z) * (dD.u * e)) : False := by
  have hx : dD.ofTorus (Torus.ofInt _ w) * dD.d8 false true l * bpow e k =
      dD.ofTorus (Torus.ofInt _ w) * dD.t * dD.d8 false false l * bpow e k := by
    rw [show dD.d8 false true l = dD.t * dD.d8 false false l by
      simp [StrothWeakTypeData.d8]]
    group
  rw [hx] at hconj
  have hEinv : (bpow e k)⁻¹ = bpow e k := by
    cases k
    · simp [Stroth42Core.bpow]
    · simp only [Stroth42Core.bpow, ↓reduceIte]
      exact inv_eq_of_mul_eq_one_right hrel.e_sq
  have hUinv : (dD.d8 false false l)⁻¹ = dD.d8 false false l := by
    cases l
    · rw [dD.d8_fff]; simp
    · rw [dD.d8_fft]; exact dD.u_inv
  have hc : bpow e k * dD.d8 false false l *
      (dD.t * ((dD.ofTorus (Torus.ofInt _ w))⁻¹ *
        (dD.ofTorus (Torus.ofInt _ z) * (dD.u * e)) *
        dD.ofTorus (Torus.ofInt _ w)) * dD.t) *
      dD.d8 false false l * bpow e k = dD.ofTorus (Torus.ofInt _ z) * (dD.u * e) := by
    calc bpow e k * dD.d8 false false l *
          (dD.t * ((dD.ofTorus (Torus.ofInt _ w))⁻¹ *
            (dD.ofTorus (Torus.ofInt _ z) * (dD.u * e)) *
            dD.ofTorus (Torus.ofInt _ w)) * dD.t) *
          dD.d8 false false l * bpow e k
        = (dD.ofTorus (Torus.ofInt _ w) * dD.t * dD.d8 false false l * bpow e k)⁻¹ *
            (dD.ofTorus (Torus.ofInt _ z) * (dD.u * e)) *
            (dD.ofTorus (Torus.ofInt _ w) * dD.t * dD.d8 false false l * bpow e k) := by
          rw [mul_inv_rev, mul_inv_rev, mul_inv_rev, dD.t_inv, hUinv, hEinv]
          group
      _ = dD.ofTorus (Torus.ofInt _ z) * (dD.u * e) := hconj
  rw [conj_ofTorus_mul_of_action dD
    (σ := dD.u * e) (φ := (dD.t200inv1EAction hrel).φe.comp
      ((StrothTypeIndex.t200 m).action.φu))
    (t200inv1_t78_ue_mul_self dD hrel) (t200inv1_t78_conj_ue dD hrel)
    (Torus.ofInt _ w) (Torus.ofInt _ z)] at hc
  obtain ⟨v1, hv1⟩ := t200inv1_t78_conj_t dD hrel
    (Torus.ofInt _ z + ((dD.t200inv1EAction hrel).φe.comp
      ((StrothTypeIndex.t200 m).action.φu)) (Torus.ofInt _ w) - Torus.ofInt _ w)
  rw [hv1] at hc
  cases l <;> cases k
  · simp only [Stroth42Core.bpow, Bool.false_eq_true, ↓reduceIte, mul_one, one_mul,
      dD.d8_fff] at hc
    exact t200inv1_t78_cancel_ue dD hm v1 z hc
  · simp only [Stroth42Core.bpow, ↓reduceIte, mul_one, dD.d8_fff] at hc
    obtain ⟨v2, hv2⟩ := t200inv1_t78_conj_e dD hrel v1
    rw [hv2] at hc
    exact t200inv1_t78_cancel_ue dD hm v2 z hc
  · simp only [Stroth42Core.bpow, Bool.false_eq_true, ↓reduceIte, mul_one, one_mul,
      dD.d8_fft] at hc
    rw [t200inv1_t78_conj_u dD hrel v1] at hc
    exact t200inv1_t78_cancel_ue dD hm _ z hc
  · simp only [Stroth42Core.bpow, ↓reduceIte, dD.d8_fft] at hc
    rw [show e * dD.u * (dD.ofTorus v1 * (dD.uv * dD.u * e)) * dD.u * e =
        e * (dD.u * (dD.ofTorus v1 * (dD.uv * dD.u * e)) * dD.u) * e by group] at hc
    rw [t200inv1_t78_conj_u dD hrel v1] at hc
    obtain ⟨v2, hv2⟩ := t200inv1_t78_conj_e dD hrel
      ((StrothTypeIndex.t200 m).action.φu v1)
    rw [hv2] at hc
    exact t200inv1_t78_cancel_ue dD hm v2 z hc

theorem t200inv1_t78_t_core {p : ℕ} (hm : 1 ≤ m) (hrel : Rel34inv dD e 0 1 p)
    (v : Torus (StrothTypeIndex.t200 m).k) (z : Fin 3 → ℤ) (l k : Bool)
    (h : bpow e k * dD.d8 false false l *
      (dD.t * (dD.ofTorus v * (dD.u * e)) * dD.t) *
      dD.d8 false false l * bpow e k =
      dD.ofTorus (Torus.ofInt _ z) * (dD.u * e)) : False := by
  obtain ⟨v1, hv1⟩ := t200inv1_t78_conj_t dD hrel v
  rw [hv1] at h
  cases l <;> cases k
  · simp only [Stroth42Core.bpow, Bool.false_eq_true, ↓reduceIte, mul_one, one_mul,
      dD.d8_fff] at h
    exact t200inv1_t78_cancel_ue dD hm v1 z h
  · simp only [Stroth42Core.bpow, ↓reduceIte, mul_one, dD.d8_fff] at h
    obtain ⟨v2, hv2⟩ := t200inv1_t78_conj_e dD hrel v1
    rw [hv2] at h
    exact t200inv1_t78_cancel_ue dD hm v2 z h
  · simp only [Stroth42Core.bpow, Bool.false_eq_true, ↓reduceIte, mul_one, one_mul,
      dD.d8_fft] at h
    rw [t200inv1_t78_conj_u dD hrel v1] at h
    exact t200inv1_t78_cancel_ue dD hm _ z h
  · simp only [Stroth42Core.bpow, ↓reduceIte, dD.d8_fft] at h
    rw [show e * dD.u * (dD.ofTorus v1 * (dD.uv * dD.u * e)) * dD.u * e =
        e * (dD.u * (dD.ofTorus v1 * (dD.uv * dD.u * e)) * dD.u) * e by group] at h
    rw [t200inv1_t78_conj_u dD hrel v1] at h
    obtain ⟨v2, hv2⟩ := t200inv1_t78_conj_e dD hrel
      ((StrothTypeIndex.t200 m).action.φu v1)
    rw [hv2] at h
    exact t200inv1_t78_cancel_ue dD hm v2 z h

theorem t200inv1_t78_t_contra_uv {p : ℕ} (hm : 1 ≤ m) (hrel : Rel34inv dD e 0 1 p)
    (z w : Fin 3 → ℤ) (l k : Bool)
    (hconj : (dD.ofTorus (Torus.ofInt _ w) * dD.d8 true true l * bpow e k)⁻¹ *
      (dD.ofTorus (Torus.ofInt _ z) * (dD.u * e)) *
      (dD.ofTorus (Torus.ofInt _ w) * dD.d8 true true l * bpow e k) =
      dD.ofTorus (Torus.ofInt _ z) * (dD.u * e)) : False := by
  have hx : dD.ofTorus (Torus.ofInt _ w) * dD.d8 true true l * bpow e k =
      dD.ofTorus (Torus.ofInt _ w) * dD.uv * dD.t * dD.d8 false false l * bpow e k := by
    rw [show dD.d8 true true l = dD.uv * dD.t * dD.d8 false false l by
      cases l <;> simp [StrothWeakTypeData.d8, mul_assoc]]
    group
  rw [hx] at hconj
  have hEinv : (bpow e k)⁻¹ = bpow e k := by
    cases k
    · simp [Stroth42Core.bpow]
    · simp only [Stroth42Core.bpow, ↓reduceIte]
      exact inv_eq_of_mul_eq_one_right hrel.e_sq
  have hUinv : (dD.d8 false false l)⁻¹ = dD.d8 false false l := by
    cases l
    · rw [dD.d8_fff]; simp
    · rw [dD.d8_fft]; exact dD.u_inv
  have hc : bpow e k * dD.d8 false false l *
      (dD.t * (dD.uv * ((dD.ofTorus (Torus.ofInt _ w))⁻¹ *
        (dD.ofTorus (Torus.ofInt _ z) * (dD.u * e)) *
        dD.ofTorus (Torus.ofInt _ w)) * dD.uv) * dD.t) *
      dD.d8 false false l * bpow e k = dD.ofTorus (Torus.ofInt _ z) * (dD.u * e) := by
    calc bpow e k * dD.d8 false false l *
          (dD.t * (dD.uv * ((dD.ofTorus (Torus.ofInt _ w))⁻¹ *
            (dD.ofTorus (Torus.ofInt _ z) * (dD.u * e)) *
            dD.ofTorus (Torus.ofInt _ w)) * dD.uv) * dD.t) *
          dD.d8 false false l * bpow e k
        = (dD.ofTorus (Torus.ofInt _ w) * dD.uv * dD.t * dD.d8 false false l *
            bpow e k)⁻¹ * (dD.ofTorus (Torus.ofInt _ z) * (dD.u * e)) *
            (dD.ofTorus (Torus.ofInt _ w) * dD.uv * dD.t * dD.d8 false false l *
              bpow e k) := by
          rw [mul_inv_rev, mul_inv_rev, mul_inv_rev, mul_inv_rev, dD.uv_inv, dD.t_inv,
            hUinv, hEinv]
          group
      _ = dD.ofTorus (Torus.ofInt _ z) * (dD.u * e) := hconj
  rw [conj_ofTorus_mul_of_action dD
    (σ := dD.u * e) (φ := (dD.t200inv1EAction hrel).φe.comp
      ((StrothTypeIndex.t200 m).action.φu))
    (t200inv1_t78_ue_mul_self dD hrel) (t200inv1_t78_conj_ue dD hrel)
    (Torus.ofInt _ w) (Torus.ofInt _ z)] at hc
  rw [t200inv1_t78_conj_uv dD hrel _] at hc
  exact t200inv1_t78_t_core dD hm hrel _ z l k hc

theorem t200inv1_t78_comm_c₁_Due {j p : ℕ} (hm : 1 ≤ m) (hrel : Rel34inv dD e j 1 p)
    (v : Torus (StrothTypeIndex.t200 m).k) (l k : Bool) :
    (dD.ofTorus v * dD.d8 false false l * bpow e k) * (dD.c : G) ^ 2 ^ (m - 1) =
      (dD.c : G) ^ 2 ^ (m - 1) * (dD.ofTorus v * dD.d8 false false l * bpow e k) := by
  set C := Subgroup.centralizer ({(dD.c : G) ^ 2 ^ (m - 1)} : Set G) with hC
  have hD : dD.ofTorus v ∈ C := by
    rw [hC, Subgroup.mem_centralizer_singleton_iff, dD.t200_c_pow]
    exact dD.ofTorus_comm v _
  have hu : dD.d8 false false l ∈ C := by
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    cases l
    · rw [dD.d8_fff]; simp
    · rw [dD.d8_fft]; exact t200inv1_u_comm_c₁ dD
  have he : bpow e k ∈ C := by
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    cases k
    · rw [bpow]; simp
    · rw [bpow]; exact t200inv1_e_comm_c₁ dD hm hrel
  exact Subgroup.mem_centralizer_singleton_iff.mp (C.mul_mem (C.mul_mem hD hu) he)

theorem t200inv1_comm_c₁_of_comm {p : ℕ} (hm : 1 ≤ m) (hp : Odd p) (hrel : Rel34inv dD e 0 1 p) :
    ∀ y ∈ D ⊔ Subgroup.zpowers (dD.u * e), y ∉ D ⊔ Subgroup.zpowers dD.u → y * y = 1 →
      ∀ x ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e, x * y = y * x →
        x * (dD.c : G) ^ 2 ^ (m - 1) = (dD.c : G) ^ 2 ^ (m - 1) * x := by
  intro y hy hynot hy2 x hxS hcomm
  let hE := dD.t200inv1EAction hrel
  have heN : e ∈ Subgroup.normalizer (D : Set G) := by
    rw [Subgroup.mem_normalizer_iff'']
    intro d
    constructor
    · intro hd
      obtain ⟨v, rfl⟩ := dD.exists_ofTorus hd
      rw [hE.conj_ofTorus]
      exact dD.ofTorus_mem _
    · intro hd
      obtain ⟨v, hv⟩ := dD.exists_ofTorus hd
      have hd' : d = e * dD.ofTorus v * e⁻¹ := by rw [← hv]; group
      rw [hd', hE.conj_inv_ofTorus]
      exact dD.ofTorus_mem _
  have hueN : dD.u * e ∈ Subgroup.normalizer (D : Set G) :=
    (Subgroup.normalizer (D : Set G)).mul_mem dD.u_mem heN
  have hue2D : (dD.u * e) * (dD.u * e) ∈ D := by
    rw [t200inv1_t78_ue_mul_self dD hrel]
    exact D.one_mem
  obtain ⟨d', hd'D, kb, hynf⟩ :=
    (Stroth47.mem_sup_zpowers_iff_of_mul_self_mem hueN hue2D).mp hy
  have hkb : kb = true := by
    cases kb
    · exfalso
      apply hynot
      rw [hynf]
      simp only [bpow, Bool.false_eq_true, ↓reduceIte, mul_one]
      exact Subgroup.mem_sup_left hd'D
    · rfl
  subst hkb
  simp only [bpow, ↓reduceIte] at hynf
  obtain ⟨d, rfl⟩ := dD.exists_ofTorus hd'D
  rw [hynf] at hcomm hy2
  obtain ⟨w, i, jb, l, k, rfl⟩ := hE.mem_sup_zpowers_iff.mp hxS
  obtain ⟨xvec, rfl⟩ := Torus.exists_ofInt d
  obtain ⟨wvec, rfl⟩ := Torus.exists_ofInt w
  have hbc : (2 : ℤ) ∣ xvec 1 - xvec 2 :=
    t200inv1_t78_involution_vec dD hrel xvec hy2
  have hconj : (dD.ofTorus (Torus.ofInt _ wvec) * dD.d8 i jb l * bpow e k)⁻¹ *
      (dD.ofTorus (Torus.ofInt _ xvec) * (dD.u * e)) *
      (dD.ofTorus (Torus.ofInt _ wvec) * dD.d8 i jb l * bpow e k) =
      dD.ofTorus (Torus.ofInt _ xvec) * (dD.u * e) := by
    calc (dD.ofTorus (Torus.ofInt _ wvec) * dD.d8 i jb l * bpow e k)⁻¹ *
          (dD.ofTorus (Torus.ofInt _ xvec) * (dD.u * e)) *
          (dD.ofTorus (Torus.ofInt _ wvec) * dD.d8 i jb l * bpow e k)
        = (dD.ofTorus (Torus.ofInt _ wvec) * dD.d8 i jb l * bpow e k)⁻¹ *
            ((dD.ofTorus (Torus.ofInt _ xvec) * (dD.u * e)) *
              (dD.ofTorus (Torus.ofInt _ wvec) * dD.d8 i jb l * bpow e k)) := by group
      _ = (dD.ofTorus (Torus.ofInt _ wvec) * dD.d8 i jb l * bpow e k)⁻¹ *
            ((dD.ofTorus (Torus.ofInt _ wvec) * dD.d8 i jb l * bpow e k) *
              (dD.ofTorus (Torus.ofInt _ xvec) * (dD.u * e))) := by rw [← hcomm]
      _ = dD.ofTorus (Torus.ofInt _ xvec) * (dD.u * e) := by group
  cases i <;> cases jb
  · exact t200inv1_t78_comm_c₁_Due dD hm hrel (Torus.ofInt _ wvec) l k
  · exfalso
    exact t200inv1_t78_t_contra dD hm hrel xvec wvec l k hconj
  · exfalso
    exact t200inv1_t78_uv_contra dD hm hp hrel xvec wvec l k hbc hconj
  · exfalso
    exact t200inv1_t78_t_contra_uv dD hm hrel xvec wvec l k hconj

theorem t200inv1_conj_ue {p : ℕ} (hm : 1 ≤ m) (hp : Odd p) (hrel : Rel34inv dD e 0 1 p) :
    ∃ q ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
      q⁻¹ * (dD.u * e) * q = (dD.c : G) ^ 2 ^ (m - 1) * (dD.u * e) := by
  let hE := dD.t200inv1EAction hrel
  by_cases hm2 : 2 ≤ m
  · refine ⟨(dD.c : G) ^ 2 ^ (m - 2), ?_, ?_⟩
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (D.pow_mem dD.c.2 _))
    · have hc₂u : ((dD.c : G) ^ 2 ^ (m - 2))⁻¹ * dD.u * (dD.c : G) ^ 2 ^ (m - 2) =
          dD.u := by
        have h := t200inv1_c₂_comm_u dD (by omega)
        calc
          ((dD.c : G) ^ 2 ^ (m - 2))⁻¹ * dD.u * (dD.c : G) ^ 2 ^ (m - 2)
              = ((dD.c : G) ^ 2 ^ (m - 2))⁻¹ *
                  (dD.u * (dD.c : G) ^ 2 ^ (m - 2)) := by group
          _ = ((dD.c : G) ^ 2 ^ (m - 2))⁻¹ *
                ((dD.c : G) ^ 2 ^ (m - 2) * dD.u) := by rw [h]
          _ = dD.u := by group
      have hc₂e := t200inv1_c₂_conj_e dD hm2 hrel
      calc
        ((dD.c : G) ^ 2 ^ (m - 2))⁻¹ * (dD.u * e) * (dD.c : G) ^ 2 ^ (m - 2)
            = (((dD.c : G) ^ 2 ^ (m - 2))⁻¹ * dD.u * (dD.c : G) ^ 2 ^ (m - 2)) *
                (((dD.c : G) ^ 2 ^ (m - 2))⁻¹ * e * (dD.c : G) ^ 2 ^ (m - 2)) := by
                group
        _ = dD.u * (e * (dD.c : G) ^ 2 ^ (m - 1)) := by rw [hc₂u, hc₂e]
        _ = (dD.c : G) ^ 2 ^ (m - 1) * (dD.u * e) := by
              rw [t200inv1_e_comm_c₁ dD (by omega) hrel, ← mul_assoc,
                t200inv1_u_comm_c₁, mul_assoc]
  · have hm1 : m = 1 := by omega
    subst hm1
    refine ⟨dD.uv * ((dD.a : G) ^ p)⁻¹, ?_, ?_⟩
    · have huvS : dD.uv ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔
          Subgroup.zpowers e :=
        Subgroup.mem_sup_left (Subgroup.mem_sup_right
          (Subgroup.subset_closure (by simp)))
      have haS : ((dD.a : G) ^ p)⁻¹ ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔
          Subgroup.zpowers e :=
        Subgroup.mem_sup_left (Subgroup.mem_sup_left (D.inv_mem (D.pow_mem dD.a.2 p)))
      exact Subgroup.mul_mem _ huvS haS
    · have he : e⁻¹ = e := inv_eq_of_mul_eq_one_right hrel.e_sq
      have ha_p : (dD.a : G) ^ p = dD.ofTorus (Torus.ofInt _ ![0, (p : ℤ), 0]) := by
        rw [dD.a_eq, ← dD.ofTorus_nsmul, a_eq_ofInt, ← natCast_zsmul, t200_zsmul_vec]
        congr 1
        funext i
        fin_cases i <;> simp
      have ha_inv : ((dD.a : G) ^ p)⁻¹ =
          dD.ofTorus (Torus.ofInt _ ![0, -(p : ℤ), 0]) := by
        rw [ha_p, ← dD.ofTorus_neg, t200_neg_vec]
        simp
      have hb_p : (dD.b : G) ^ p = dD.ofTorus (Torus.ofInt _ ![0, 0, (p : ℤ)]) := by
        rw [dD.b_eq, ← dD.ofTorus_nsmul, b_eq_ofInt, ← natCast_zsmul, t200_zsmul_vec]
        congr 1
        funext i
        fin_cases i <;> simp
      have hcab : (dD.cab) ^ p =
          dD.ofTorus (Torus.ofInt _ ![(p : ℤ), (p : ℤ), (p : ℤ)]) :=
        dD.t200x_cab_pow p
      have hcab_inv : ((dD.cab) ^ p)⁻¹ =
          dD.ofTorus (Torus.ofInt _ ![-(p : ℤ), -(p : ℤ), -(p : ℤ)]) := by
        rw [hcab, ← dD.ofTorus_neg, t200_neg_vec]
      have h1 : e * dD.uv = (dD.cab) ^ p * dD.uv * e := by
        have h := hrel.uv_conj
        rw [he] at h
        calc
          e * dD.uv = (e * dD.uv) * 1 := (mul_one _).symm
          _ = (e * dD.uv) * (e * e) := by rw [hrel.e_sq]
          _ = (e * dD.uv * e) * e := by group
          _ = ((dD.cab) ^ p * dD.uv) * e := by
                simpa [StrothWeakTypeData.cab] using h
      have h2 : ((dD.cab) ^ p)⁻¹ * e * dD.uv = dD.uv * e := by
        calc
          ((dD.cab) ^ p)⁻¹ * e * dD.uv = ((dD.cab) ^ p)⁻¹ * (e * dD.uv) := by group
          _ = ((dD.cab) ^ p)⁻¹ * (((dD.cab) ^ p * dD.uv) * e) := by rw [h1]
          _ = dD.uv * e := by group
      have huv_e : dD.uv * e * dD.uv = ((dD.cab) ^ p)⁻¹ * e := by
        calc
          dD.uv * e * dD.uv = (dD.uv * e) * dD.uv := rfl
          _ = (((dD.cab) ^ p)⁻¹ * e * dD.uv) * dD.uv := by rw [← h2]
          _ = ((dD.cab) ^ p)⁻¹ * e := by
                rw [mul_assoc, show dD.uv * dD.uv = 1 from dD.uv_sq, mul_one]
      have hux : dD.u * (dD.cab) ^ p = (dD.cab) ^ p * dD.u := by
        rw [hcab, dD.u_mul_ofTorus]
        have hv : (StrothTypeIndex.t200 1).action.φu
            (Torus.ofInt _ ![(p : ℤ), (p : ℤ), (p : ℤ)]) =
              Torus.ofInt _ ![(p : ℤ), (p : ℤ), (p : ℤ)] := by
          rw [t200_φu]
          simp
        rw [hv]
      have hux_inv : dD.u * ((dD.cab) ^ p)⁻¹ = ((dD.cab) ^ p)⁻¹ * dD.u := by
        have h : ((dD.cab) ^ p)⁻¹ * dD.u = dD.u * ((dD.cab) ^ p)⁻¹ := by
          have := congrArg Inv.inv hux
          simpa [mul_inv_rev, dD.u_inv, inv_inv] using this
        exact h.symm
      have hea : e * ((dD.a : G) ^ p)⁻¹ = (dD.a : G) ^ p * e := by
        rw [ha_inv, ha_p]
        rw [hE.e_mul_ofTorus]
        congr 1
        rw [StrothWeakTypeData.t200inv1_φe]
        congr 1
        funext i
        fin_cases i <;> simp
      have hua : dD.u * (dD.a : G) ^ p = (dD.b : G) ^ p * dD.u := by
        rw [ha_p, hb_p, dD.u_mul_ofTorus, t200_φu]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons]
      have hx : (dD.a : G) ^ p * ((dD.cab) ^ p)⁻¹ * (dD.b : G) ^ p =
          (dD.c : G) := by
        rw [ha_p, hcab_inv, hb_p]
        have hc : (dD.c : G) = dD.ofTorus (Torus.ofInt _ ![1, 0, 0]) := by
          rw [dD.ofTorus_ofInt]
          simp
        rw [hc, ← dD.ofTorus_add, ← dD.ofTorus_add, t200_add_vec, t200_add_vec,
          dD.ofTorus_inj.eq_iff, t200_ofInt_eq_iff]
        refine ⟨?_, by simp, by simp⟩
        obtain ⟨k, hk⟩ := hp
        have hk' : (p : ℤ) = 2 * (k : ℤ) + 1 := by omega
        simp only [Matrix.cons_val_zero]
        rw [show (2 : ℤ) ^ 1 = 2 by norm_num]
        omega
      have hqinv : (dD.uv * ((dD.a : G) ^ p)⁻¹)⁻¹ = (dD.a : G) ^ p * dD.uv := by
        rw [mul_inv_rev, dD.uv_inv, inv_inv]
      have hqinv : (dD.uv * ((dD.a : G) ^ p)⁻¹)⁻¹ = (dD.a : G) ^ p * dD.uv := by
        rw [mul_inv_rev, dD.uv_inv, inv_inv]
      set a : G := (dD.a : G) ^ p with ha
      set b : G := (dD.b : G) ^ p with hb
      set x : G := (dD.cab) ^ p with hxdef
      have hux_inv' : dD.u * x⁻¹ = x⁻¹ * dD.u := by
        rw [hxdef]; exact hux_inv
      have huv_e' : dD.uv * e * dD.uv = x⁻¹ * e := by
        rw [hxdef]; exact huv_e
      have hea' : e * a⁻¹ = a * e := by
        rw [ha]; exact hea
      have hua' : dD.u * a = b * dD.u := by
        rw [ha, hb]; exact hua
      have hx' : a * x⁻¹ * b = (dD.c : G) := by
        rw [ha, hxdef, hb]; exact hx
      rw [hqinv]
      calc
        (a * dD.uv) * (dD.u * e) * (dD.uv * a⁻¹)
            = a * (dD.uv * dD.u) * e * dD.uv * a⁻¹ := by group
        _ = a * (dD.u * dD.uv) * e * dD.uv * a⁻¹ := by rw [dD.uv_comm_u]
        _ = a * dD.u * (dD.uv * e * dD.uv) * a⁻¹ := by group
        _ = a * dD.u * (x⁻¹ * e) * a⁻¹ := by rw [huv_e']
        _ = a * (dD.u * x⁻¹) * e * a⁻¹ := by group
        _ = a * (x⁻¹ * dD.u) * e * a⁻¹ := by rw [hux_inv']
        _ = a * x⁻¹ * (dD.u * (e * a⁻¹)) := by group
        _ = a * x⁻¹ * (dD.u * (a * e)) := by rw [hea']
        _ = a * x⁻¹ * (dD.u * a) * e := by group
        _ = a * x⁻¹ * (b * dD.u) * e := by rw [hua']
        _ = (a * x⁻¹ * b) * dD.u * e := by group
        _ = (dD.c : G) * dD.u * e := by rw [hx']
        _ = (dD.c : G) ^ 2 ^ (1 - 1) * (dD.u * e) := by
              simp
              group

theorem t200inv1_conj_cab_uv {p : ℕ} (hm : 1 ≤ m) (hp : Odd p) (hrel : Rel34inv dD e 0 1 p) :
    ∃ q ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
      q⁻¹ * (dD.cab * dD.uv) * q = dD.uv := by
  have _ := hm
  let hE := dD.t200inv1EAction hrel
  obtain ⟨k, hk⟩ := hp
  set r : Torus (StrothTypeIndex.t200 m).k :=
    Torus.ofInt _ ![0, (k : ℤ), (k : ℤ)] with hr
  refine ⟨dD.ofTorus r * e, ?_, ?_⟩
  · have hrD : dD.ofTorus r ∈ D := dD.ofTorus_mem r
    have heS : e ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers e)
    exact Subgroup.mul_mem _
      (Subgroup.mem_sup_left (Subgroup.mem_sup_left hrD)) heS
  · have he : e⁻¹ = e := inv_eq_of_mul_eq_one_right hrel.e_sq
    have hcab : (dD.cab : G) = dD.ofTorus (Torus.ofInt _ ![1, 1, 1]) := by
      rw [dD.ofTorus_ofInt]
      simp [StrothWeakTypeData.cab]
    have hφuv : (StrothTypeIndex.t200 m).action.φuv
        (Torus.ofInt _ ![(p - 1 : ℕ), (p - 1 : ℕ), (p - 1 : ℕ)]) =
          -Torus.ofInt _ ![(p - 1 : ℕ), (p - 1 : ℕ), (p - 1 : ℕ)] := by
      rw [t200_φuv_vec, t200_neg_vec]
      congr 1
      funext i
      fin_cases i <;> ring_nf
    have huv_x : dD.uv * (dD.cab : G) ^ (p - 1) * dD.uv =
        ((dD.cab : G) ^ (p - 1))⁻¹ := by
      rw [show (dD.cab : G) = (dD.c : G) * dD.a * dD.b from rfl,
        dD.t200x_cab_pow (p - 1)]
      have hstep : dD.uv * dD.ofTorus
          (Torus.ofInt _ ![(p - 1 : ℕ), (p - 1 : ℕ), (p - 1 : ℕ)]) * dD.uv =
          dD.ofTorus ((StrothTypeIndex.t200 m).action.φuv
            (Torus.ofInt _ ![(p - 1 : ℕ), (p - 1 : ℕ), (p - 1 : ℕ)])) := by
        have h := dD.d8_mul_ofTorus true false false
          (Torus.ofInt _ ![(p - 1 : ℕ), (p - 1 : ℕ), (p - 1 : ℕ)])
        rw [dD.d8_tff] at h
        rw [show (StrothTypeIndex.t200 m).action.d8Act true false false
            (Torus.ofInt _ ![(p - 1 : ℕ), (p - 1 : ℕ), (p - 1 : ℕ)]) =
              (StrothTypeIndex.t200 m).action.φuv
                (Torus.ofInt _ ![(p - 1 : ℕ), (p - 1 : ℕ), (p - 1 : ℕ)]) from by
          simp [SigmaFourAction.d8Act]] at h
        calc
          dD.uv * dD.ofTorus (Torus.ofInt _ ![(p - 1 : ℕ), (p - 1 : ℕ),
              (p - 1 : ℕ)]) * dD.uv
              = (dD.ofTorus ((StrothTypeIndex.t200 m).action.φuv
                  (Torus.ofInt _ ![(p - 1 : ℕ), (p - 1 : ℕ), (p - 1 : ℕ)])) *
                    dD.uv) * dD.uv := by rw [h]
          _ = dD.ofTorus ((StrothTypeIndex.t200 m).action.φuv
                (Torus.ofInt _ ![(p - 1 : ℕ), (p - 1 : ℕ), (p - 1 : ℕ)])) := by
                  rw [mul_assoc, dD.uv_sq, mul_one]
      rw [hstep, hφuv, dD.ofTorus_neg]
    have htwist : dD.ofTorus (r - (StrothTypeIndex.t200 m).action.d8Act true false false r) =
        ((dD.cab : G) ^ (p - 1))⁻¹ := by
      have hvec : r - (StrothTypeIndex.t200 m).action.d8Act true false false r =
          -Torus.ofInt _ ![(p - 1 : ℕ), (p - 1 : ℕ), (p - 1 : ℕ)] := by
        rw [hr, show (StrothTypeIndex.t200 m).action.d8Act true false false
            (Torus.ofInt _ ![0, (k : ℤ), (k : ℤ)]) =
              (StrothTypeIndex.t200 m).action.φuv
                (Torus.ofInt _ ![0, (k : ℤ), (k : ℤ)]) from by
          simp [SigmaFourAction.d8Act]]
        rw [t200_φuv_vec, t200_sub_vec, t200_neg_vec]
        congr 1
        funext i
        fin_cases i <;>
          simp [show ((p - 1 : ℕ) : ℤ) = 2 * (k : ℤ) by omega]
        all_goals ring
      rw [hvec, dD.ofTorus_neg, show (dD.cab : G) = (dD.c : G) * dD.a * dD.b from rfl,
        dD.t200x_cab_pow (p - 1)]
    have hr : (dD.ofTorus r)⁻¹ * (dD.cab * dD.uv) * dD.ofTorus r =
        (dD.cab : G) ^ p * dD.uv := by
      have h := t200inv1_conj_nfe dD hrel (v := Torus.ofInt _ ![1, 1, 1])
        (w := r) (i := true) (jb := false) (l := false) (k := false) (by simp)
      simp only [Stroth42Core.bpow, Bool.false_eq_true, ↓reduceIte, mul_one] at h
      rw [hcab, ← dD.d8_tff]
      rw [h, htwist]
      have huv_inv : dD.uv * ((dD.cab : G) ^ (p - 1))⁻¹ =
          (dD.cab : G) ^ (p - 1) * dD.uv := by
        have hinv : dD.uv * ((dD.cab : G) ^ (p - 1))⁻¹ * dD.uv =
            (dD.cab : G) ^ (p - 1) := by
          calc
            dD.uv * ((dD.cab : G) ^ (p - 1))⁻¹ * dD.uv
                = (dD.uv * (dD.cab : G) ^ (p - 1) * dD.uv)⁻¹ := by
                    simp only [mul_inv_rev, dD.uv_inv, mul_assoc]
            _ = (((dD.cab : G) ^ (p - 1))⁻¹)⁻¹ := by rw [huv_x]
            _ = (dD.cab : G) ^ (p - 1) := inv_inv _
        calc
          dD.uv * ((dD.cab : G) ^ (p - 1))⁻¹
              = (dD.uv * ((dD.cab : G) ^ (p - 1))⁻¹ * dD.uv) * dD.uv := by
                  rw [mul_assoc, dD.uv_sq, mul_one]
          _ = (dD.cab : G) ^ (p - 1) * dD.uv := by rw [hinv]
      rw [dD.d8_tff]
      rw [mul_assoc, huv_inv, ← mul_assoc, hcab]
      congr 1
      rw [← pow_succ', show p - 1 + 1 = p by omega]
    have hfin : e * ((dD.cab : G) ^ p * dD.uv) * e = dD.uv := by
      have hcab_p : (dD.cab : G) ^ p =
          dD.ofTorus (Torus.ofInt _ ![(p : ℤ), (p : ℤ), (p : ℤ)]) :=
        dD.t200x_cab_pow p
      have hφe : hE.φe (Torus.ofInt _ ![(p : ℤ), (p : ℤ), (p : ℤ)]) =
          -Torus.ofInt _ ![(p : ℤ), (p : ℤ), (p : ℤ)] := by
        rw [StrothWeakTypeData.t200inv1_φe, t200_neg_vec]
        congr 1
        funext i
        fin_cases i <;> simp
      have he_cab : e * (dD.cab : G) ^ p = ((dD.cab : G) ^ p)⁻¹ * e := by
        rw [hcab_p, hE.e_mul_ofTorus, hφe, dD.ofTorus_neg]
      have heuv : e * dD.uv * e = (dD.cab : G) ^ p * dD.uv := by
        have h := hrel.uv_conj
        rwa [he] at h
      calc
        e * ((dD.cab : G) ^ p * dD.uv) * e
            = (e * (dD.cab : G) ^ p) * (dD.uv * e) := by group
        _ = (((dD.cab : G) ^ p)⁻¹ * e) * (dD.uv * e) := by rw [he_cab]
        _ = ((dD.cab : G) ^ p)⁻¹ * (e * dD.uv * e) := by group
        _ = ((dD.cab : G) ^ p)⁻¹ * ((dD.cab : G) ^ p * dD.uv) := by rw [heuv]
        _ = dD.uv := by group
    have hqinv : (dD.ofTorus r * e)⁻¹ = e * (dD.ofTorus r)⁻¹ := by
      rw [mul_inv_rev, he]
    rw [hqinv]
    calc
      e * (dD.ofTorus r)⁻¹ * (dD.cab * dD.uv) * (dD.ofTorus r * e)
          = e * ((dD.ofTorus r)⁻¹ * (dD.cab * dD.uv) * dD.ofTorus r) * e := by group
      _ = e * ((dD.cab : G) ^ p * dD.uv) * e := by rw [hr]
      _ = dD.uv := hfin

end Stroth47Core

end CFSG.CGT.Stroth77
