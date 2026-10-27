module

public import CFSG.CGT.Stroth77.Section47CoreK
public import CFSG.CGT.Stroth77.Section47HaradaConj

public section

namespace CFSG.CGT.Stroth77

open Matrix Stroth42Core Stroth34T200 StrothWeakTypeData

namespace Stroth47Core

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ}
  (dD : StrothWeakTypeData D (.t200 m)) {e f : G} {p : ℕ}

theorem torusDiag_neg_one (v : Torus (StrothTypeIndex.t200 m).k) :
    torusDiag (StrothTypeIndex.t200 m).k ![-1, -1, -1] v = -v := by
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
  rw [torusDiag_ofInt, ← Torus.ofInt_neg]
  congr 1
  funext i
  fin_cases i <;> simp

theorem t200k_not_word (hm : 1 ≤ m) (i j l : Bool)
    (h : ∀ v, ((torusDiag (StrothTypeIndex.t200 m).k ![-1, -1, -1]).comp
      (torusDiag _ ![1, 1 + 2 ^ (m + 1), 1 + 2 ^ (m + 1)])) v =
      (StrothTypeIndex.t200 m).action.d8Act i j l v) : False := by
  have hom : ∀ ε, ((torusDiag (StrothTypeIndex.t200 m).k ![-1, -1, -1]).comp
      (torusDiag _ ![1, 1 + 2 ^ (m + 1), 1 + 2 ^ (m + 1)])) (om200 m ε) = om200 m ε := by
    intro ε
    rw [AddMonoidHom.comp_apply, t200_i_φe_om hm, torusDiag_neg_one]
    exact (eq_neg_of_add_eq_zero_left (om200_add_self hm ε)).symm
  have hc := h (om200 m ![1, 0, 0])
  have ha := h (om200 m ![0, 1, 0])
  rw [hom] at hc ha
  obtain ⟨rfl, rfl, rfl⟩ := t200_faithful_om hm i j l hc.symm ha.symm
  have h1 := h (Torus.ofInt _ ![0, 1, 0])
  rw [AddMonoidHom.comp_apply, torusDiag_ofInt, torusDiag_ofInt] at h1
  simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
    AddMonoidHom.id_apply, t200_ofInt_eq_iff] at h1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at h1
  obtain ⟨-, ⟨k, hk⟩, -⟩ := h1
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have h2 : (2 : ℤ) * (1 + 2 * 2 ^ m' - 4 * 2 ^ m' * k) = 0 := by linear_combination hk
  have h3 : (1 : ℤ) = 2 * (2 * 2 ^ m' * k - 2 ^ m') := by linarith
  omega

theorem t200k_e_not_mem (hm : 1 ≤ m) (hrel_e : Rel34i dD e (2 ^ (m + 1)))
    (hrel_f : Rel34inv dD f 0 1 p) :
    e ∉ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers f := by
  intro he
  obtain ⟨v, i, j, l, k, hk⟩ := (dD.t200fEAction hrel_f).mem_sup_zpowers_iff.mp he
  cases k
  · simp only [bpow, Bool.false_eq_true, ↓reduceIte, mul_one] at hk
    exact t200_i_h2 dD hm hrel_e (hk ▸ dD.nf_mem v i j l)
  · simp only [bpow, ↓reduceIte] at hk
    have hef : e * f = dD.ofTorus v * dD.d8 i j l := by
      rw [hk, mul_assoc, hrel_f.e_sq, mul_one]
    refine dD.not_mem_sup_of_conj (g := e * f)
      (φ := (torusDiag _ ![-1, -1, -1]).comp (torusDiag _ ![1, 1 + 2 ^ (m + 1), 1 + 2 ^ (m + 1)]))
      (fun w => ?_) (fun i j l h => t200k_not_word hm i j l h) (hef ▸ dD.nf_mem v i j l)
    rw [show (e * f)⁻¹ * dD.ofTorus w * (e * f) = f⁻¹ * (e⁻¹ * dD.ofTorus w * e) * f by group,
      (dD.t200iAction hrel_e).conj_ofTorus, t200iAction_φe, dD.t200k_f_conj_ofTorus hrel_f]
    rfl

theorem t200k_conj_mul_inv_mem (heN : e ∈ Subgroup.normalizer (D : Set G))
    (hfN : f ∈ Subgroup.normalizer (D : Set G)) (hrel_e : Rel34i dD e (2 ^ (m + 1)))
    (hrel_f : Rel34inv dD f 0 1 p) (hconj : f⁻¹ * e * f = e⁻¹ * (dD.c : G) ^ 2 ^ (m - 1)) :
    ∀ x ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers f,
      e⁻¹ * x * e * x⁻¹ ∈ D := by
  refine Stroth47.conj_mul_inv_mem heN (dD.t200x_U_le_normalizer hfN) (dD.t200x_U_eq _) ?_
  intro x hx
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with (rfl | rfl | rfl) | rfl
  · rw [hrel_e.uv_conj, mul_inv_cancel_right]
    exact D.pow_mem (D.mul_mem (D.mul_mem dD.c.2 dD.a.2) dD.b.2) _
  · rw [hrel_e.t_conj, mul_inv_cancel_right]
    exact D.inv_mem (D.pow_mem dD.a.2 _)
  · rw [hrel_e.u_conj, mul_inv_cancel]
    exact one_mem _
  · have hfinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hrel_f.e_sq
    have h1 : e⁻¹ * x * e * x⁻¹ = e⁻¹ * (x⁻¹ * e * x) := by rw [hfinv]; group
    rw [h1, hconj, ← mul_assoc, ← _root_.mul_inv_rev, hrel_e.e_sq, inv_inv]
    exact D.mul_mem dD.c.2 (D.pow_mem dD.c.2 _)

theorem t200k_e_mul_self_mem (hrel_e : Rel34i dD e (2 ^ (m + 1))) :
    e * e ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers f := by
  rw [hrel_e.e_sq]
  exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (D.inv_mem dD.c.2))

theorem t200k_mem_normalizer (heN : e ∈ Subgroup.normalizer (D : Set G))
    (hfN : f ∈ Subgroup.normalizer (D : Set G)) (hrel_e : Rel34i dD e (2 ^ (m + 1)))
    (hrel_f : Rel34inv dD f 0 1 p) (hconj : f⁻¹ * e * f = e⁻¹ * (dD.c : G) ^ 2 ^ (m - 1)) :
    e ∈ Subgroup.normalizer
      ((D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers f : Subgroup G) : Set G) :=
  Stroth47.mem_normalizer_of_conj_mul_inv_mem (le_sup_left.trans le_sup_left)
    (t200k_e_mul_self_mem dD hrel_e) (t200k_conj_mul_inv_mem dD heN hfN hrel_e hrel_f hconj)

theorem t200k_c₁_mul_self (hm : 1 ≤ m) :
    (dD.c : G) ^ 2 ^ (m - 1) * (dD.c : G) ^ 2 ^ (m - 1) = 1 := by
  rw [dD.t200_c_pow, ← dD.ofTorus_add, om200_add_self hm, dD.ofTorus_zero]

theorem t200k_f_comm_c₁ (hm : 1 ≤ m) (hrel_f : Rel34inv dD f 0 1 p) :
    f * (dD.c : G) ^ 2 ^ (m - 1) = (dD.c : G) ^ 2 ^ (m - 1) * f := by
  have h1 : f⁻¹ * (dD.c : G) ^ 2 ^ (m - 1) * f = (dD.c : G) ^ 2 ^ (m - 1) := by
    have h2 : f⁻¹ * (dD.c : G) ^ 2 ^ (m - 1) * f = (f⁻¹ * (dD.c : G) * f) ^ 2 ^ (m - 1) := by
      simpa using (conj_pow (a := f⁻¹) (b := (dD.c : G)) (i := 2 ^ (m - 1))).symm
    rw [h2, hrel_f.c_conj, inv_pow]
    exact inv_eq_of_mul_eq_one_right (t200k_c₁_mul_self dD hm)
  calc f * (dD.c : G) ^ 2 ^ (m - 1) = f * (f⁻¹ * (dD.c : G) ^ 2 ^ (m - 1) * f) := by rw [h1]
    _ = _ := by group

theorem t200k_h4 (hm : 1 ≤ m) (hrel_f : Rel34inv dD f 0 1 p) :
    ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers f,
      y * (dD.c : G) ^ 2 ^ (m - 1) = (dD.c : G) ^ 2 ^ (m - 1) * y →
        y ^ 2 ^ m ≠ (dD.c : G) ^ 2 ^ (m - 1) := by
  intro y hy hcomm hpow
  obtain ⟨v, i, j, l, k, rfl⟩ := (dD.t200fEAction hrel_f).mem_sup_zpowers_iff.mp hy
  cases k
  · simp only [bpow, Bool.false_eq_true, ↓reduceIte, mul_one] at hcomm hpow
    exact dD.t200_h4 hm _ (dD.nf_mem v i j l) hcomm hpow
  simp only [bpow, ↓reduceIte] at hcomm hpow
  set z := (dD.c : G) ^ 2 ^ (m - 1) with hz
  set X := dD.ofTorus v * dD.d8 i j l with hXdef
  have hfc := t200k_f_comm_c₁ dD hm hrel_f
  rw [← hz] at hfc
  have hX : X * z = z * X := by
    have h1 : X * z * f = z * X * f := by
      rw [mul_assoc X z f, ← hfc, ← mul_assoc, hcomm, ← mul_assoc]
    exact mul_right_cancel h1
  obtain ⟨rfl, rfl⟩ := dD.t200_comm_z hm hX
  rw [hXdef, pow_two_pow_eq_mul_self _ hm, (dD.t200fEAction hrel_f).nfe_e_mul_self,
    Bool.and_false, d8_fff, mul_one, ← dD.ofTorus_nsmul, hz, dD.t200_c_pow] at hpow
  have h := dD.ofTorus_inj hpow
  obtain ⟨x0, x1, x2, rfl⟩ := t200_exists_vec v
  have hsq : ∃ s1 s2 : ℤ, (dD.t200fEAction hrel_f).sqE (Torus.ofInt _ ![x0, x1, x2]) false false l =
      Torus.ofInt _ ![0, s1, s2] := by
    cases l <;>
    simp only [EAction.sqE, EAction.twist, t200fEAction_φe, t200fEAction_ve, t200fEAction_wuv,
      t200fEAction_wt, SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte,
      AddMonoidHom.comp_apply, AddMonoidHom.id_apply, Bool.and_false, map_zero, add_zero,
      zero_add, sub_zero, torusDiag_neg_one, t200_φu, map_neg, ← Torus.ofInt_neg,
      ← Torus.ofInt_add]
    · exact ⟨0, 0, by congr 1; funext i; fin_cases i <;> simp⟩
    · exact ⟨x1 - x2, x2 - x1, by congr 1; funext i; fin_cases i <;> simp <;> ring⟩
  obtain ⟨s1, s2, hs⟩ := hsq
  rw [hs, ← natCast_zsmul, t200_zsmul_vec, om200_apply, t200_ofInt_eq_iff] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at h
  obtain ⟨⟨k, hk⟩, -, -⟩ := h
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hk
  push_cast at hk
  have h2 : (2 : ℤ) ^ m' * 1 = 2 ^ m' * (2 * k) := by linear_combination hk
  have h3 := mul_left_cancel₀ (pow_ne_zero m' (two_ne_zero : (2 : ℤ) ≠ 0)) h2
  omega

theorem t200k_h5 (heN : e ∈ Subgroup.normalizer (D : Set G))
    (hfN : f ∈ Subgroup.normalizer (D : Set G)) (hrel_e : Rel34i dD e (2 ^ (m + 1)))
    (hrel_f : Rel34inv dD f 0 1 p) (hconj : f⁻¹ * e * f = e⁻¹ * (dD.c : G) ^ 2 ^ (m - 1)) :
    ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers f ⊔ Subgroup.zpowers e,
      y * y ∈ D ∨ y * y * dD.uv ∈ D := by
  intro y hy
  by_cases hyU : y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers f
  · exact (dD.t200fEAction hrel_f).mul_self_mem_or y hyU
  obtain ⟨v, i, hv⟩ := (dD.t200fEAction hrel_f).mul_self_of_not_mem
    (dD.t200x_U_le_normalizer hfN) (t200k_mem_normalizer dD heN hfN hrel_e hrel_f hconj)
    (t200k_e_mul_self_mem dD hrel_e) (t200k_conj_mul_inv_mem dD heN hfN hrel_e hrel_f hconj)
    y hy hyU
  rw [hv, hrel_e.e_sq, show (dD.c : G)⁻¹ = dD.ofTorus (-Torus.c) by rw [dD.ofTorus_neg, ← c_eq],
    mul_assoc, dD.d8_mul_ofTorus, ← mul_assoc, ← dD.ofTorus_add]
  cases i
  · left
    rw [d8_fff, mul_one]
    exact dD.ofTorus_mem _
  · right
    rw [d8_tff, mul_assoc, dD.uv_sq, mul_one]
    exact dD.ofTorus_mem _

theorem t200k_conj_uv_ofTorus (w1 w2 : ℤ) :
    (dD.ofTorus (Torus.ofInt _ ![0, w1, w2]))⁻¹ * dD.uv * dD.ofTorus (Torus.ofInt _ ![0, w1, w2]) =
      dD.ofTorus (Torus.ofInt _ ![w1 + w2, 2 * w2, 2 * w1]) * dD.uv := by
  rw [← dD.ofTorus_neg, mul_assoc, dD.uv_mul_ofTorus, ← mul_assoc, ← dD.ofTorus_add, t200_φuv,
    ← Torus.ofInt_neg, ← Torus.ofInt_add]
  congr 3
  funext i
  fin_cases i <;> simp <;> ring

theorem t200k_isConj_uv_of_even (y0 y1 b : ℤ)
    (hyy : dD.ofTorus (Torus.ofInt _ ![y0, y1, b + b]) * dD.uv *
      (dD.ofTorus (Torus.ofInt _ ![y0, y1, b + b]) * dD.uv) = 1) :
    IsConj (dD.ofTorus (Torus.ofInt _ ![y0, y1, b + b]) * dD.uv) dD.uv := by
  have hsq := hyy
  rw [← d8_tff, nf_mul_self, Bool.and_false, d8_fff, mul_one, ofTorus_eq_one_iff] at hsq
  simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
    AddMonoidHom.id_apply, t200_φuv] at hsq
  rw [← Torus.ofInt_add, t200_ofInt_eq_zero_iff] at hsq
  obtain ⟨-, ⟨k1, hk1⟩, -⟩ := hsq
  simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at hk1
  rw [show (2 : ℤ) ^ (m + 2) = 4 * 2 ^ m by ring] at hk1
  have hA : y1 = 2 * (y0 - b + 2 ^ m * k1) := by linarith
  have hconj := t200k_conj_uv_ofTorus dD b (y0 - b + 2 ^ m * k1)
  have heq : dD.ofTorus (Torus.ofInt _ ![y0, y1, b + b]) =
      dD.ofTorus (Torus.ofInt _
        ![b + (y0 - b + 2 ^ m * k1), 2 * (y0 - b + 2 ^ m * k1), 2 * b]) := by
    congr 1
    rw [t200_ofInt_eq_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    exact ⟨⟨k1, by ring⟩, ⟨0, by rw [hA]; ring⟩, ⟨0, by ring⟩⟩
  rw [heq, ← hconj]
  exact isConj_iff.mpr ⟨dD.ofTorus (Torus.ofInt _ ![0, b, y0 - b + 2 ^ m * k1]), by group⟩

theorem t200k_isConj_uv (hp : p % 2 = 1) (hrel_f : Rel34inv dD f 0 1 p) :
    ∀ y : G, y * dD.uv ∈ D → y * y = 1 → IsConj y dD.uv := by
  intro y hy hyy
  obtain ⟨v, hv⟩ := dD.exists_ofTorus hy
  have hyv : y = dD.ofTorus v * dD.uv := by
    rw [← hv, mul_assoc, dD.uv_sq, mul_one]
  subst hyv
  obtain ⟨y0, y1, y2, rfl⟩ := t200_exists_vec v
  rcases Int.even_or_odd y2 with ⟨b, hb⟩ | ⟨b, hb⟩
  · subst hb
    exact t200k_isConj_uv_of_even dD y0 y1 b hyy
  ·
    obtain ⟨r, rfl⟩ : ∃ r, p = 2 * r + 1 := ⟨p / 2, by omega⟩
    have hf : f⁻¹ * (dD.ofTorus (Torus.ofInt _ ![y0, y1, y2]) * dD.uv) * f =
        dD.ofTorus (Torus.ofInt _ ![(2 * r + 1 : ℤ) - y0, (2 * r + 1 : ℤ) - y1,
          (r - b) + (r - b)]) * dD.uv := by
      rw [show f⁻¹ * (dD.ofTorus (Torus.ofInt _ ![y0, y1, y2]) * dD.uv) * f =
          (f⁻¹ * dD.ofTorus (Torus.ofInt _ ![y0, y1, y2]) * f) * (f⁻¹ * dD.uv * f) by group,
        dD.t200k_f_conj_ofTorus hrel_f, hrel_f.uv_conj, dD.t200x_cab_pow, ← mul_assoc,
        ← dD.ofTorus_add, torusDiag_ofInt, ← Torus.ofInt_add]
      congr 3
      funext i
      fin_cases i <;> simp <;> push_cast <;> linarith
    have hyy' : (f⁻¹ * (dD.ofTorus (Torus.ofInt _ ![y0, y1, y2]) * dD.uv) * f) *
        (f⁻¹ * (dD.ofTorus (Torus.ofInt _ ![y0, y1, y2]) * dD.uv) * f) = 1 := by
      rw [show (f⁻¹ * (dD.ofTorus (Torus.ofInt _ ![y0, y1, y2]) * dD.uv) * f) *
          (f⁻¹ * (dD.ofTorus (Torus.ofInt _ ![y0, y1, y2]) * dD.uv) * f) =
          f⁻¹ * ((dD.ofTorus (Torus.ofInt _ ![y0, y1, y2]) * dD.uv) *
            (dD.ofTorus (Torus.ofInt _ ![y0, y1, y2]) * dD.uv)) * f by group, hyy]
      group
    rw [hf] at hyy'
    have h1 := t200k_isConj_uv_of_even dD _ _ (r - b) hyy'
    rw [← hf] at h1
    exact (isConj_iff.mpr ⟨f⁻¹, by group⟩).trans h1

end Stroth47Core

end CFSG.CGT.Stroth77
