module

public import CFSG.CGT.Stroth77.Section47ExtremalH9

public section

namespace CFSG.CGT.Stroth77

open Matrix Stroth42Core Stroth34T200 Stroth47Core StrothWeakTypeData

variable {G : Type} [Group G] [Finite G]

namespace Stroth47Core

variable {D : Subgroup G} {m : ℕ} (dD : StrothWeakTypeData D (.t200 m)) {e : G} {p : ℕ}

theorem t200_u_mul_c : dD.u * (dD.c : G) = (dD.c : G) * dD.u := by
  have h := dD.conj_ofTorus dD.u_mem dD.u_conj Torus.c
  rw [show (StrothTypeIndex.t200 m).action.φu Torus.c = Torus.c from by
    rw [c_eq_ofInt, t200_φu_vec], ← dD.c_eq] at h
  calc dD.u * (dD.c : G) = dD.u * (dD.u⁻¹ * (dD.c : G) * dD.u) := by rw [h]
    _ = (dD.c : G) * dD.u := by group

theorem t200inv_e_conj_c₂ {p : ℕ}
    (hrel : Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) p) :
    e⁻¹ * (dD.c : G) ^ 2 ^ (m - 2) * e = ((dD.c : G) ^ 2 ^ (m - 2))⁻¹ := by
  rw [← Stroth43Sc.conj_pow_eq, hrel.c_conj, inv_pow]

theorem t200inv_c₂_ne_inv (hm : 2 ≤ m) :
    (dD.c : G) ^ 2 ^ (m - 2) ≠ ((dD.c : G) ^ 2 ^ (m - 2))⁻¹ := by
  intro h
  have h2 : (dD.c : G) ^ 2 ^ (m - 2) * (dD.c : G) ^ 2 ^ (m - 2) = 1 := by
    nth_rewrite 1 [h]
    exact inv_mul_cancel _
  have h1 : (dD.c : G) ^ 2 ^ (m - 1) = 1 := by
    rw [← H47_c₂_sq dD hm, h2]
  exact Stroth47Fus.t200_c₁_ne_one dD (by omega) h1

theorem t200inv_ofTorus_comm_c₂ (v : Torus (StrothTypeIndex.t200 m).k) :
    dD.ofTorus v * (dD.c : G) ^ 2 ^ (m - 2) =
      (dD.c : G) ^ 2 ^ (m - 2) * dD.ofTorus v :=
  congrArg Subtype.val (dD.isMulCommutative.is_comm.comm
    ⟨dD.ofTorus v, dD.ofTorus_mem v⟩ ⟨(dD.c : G) ^ 2 ^ (m - 2), D.pow_mem dD.c.2 _⟩)

theorem t200inv_u_comm_c₂ :
    dD.u * (dD.c : G) ^ 2 ^ (m - 2) = (dD.c : G) ^ 2 ^ (m - 2) * dD.u := by
  have h : Commute dD.u (dD.c : G) := by
    rw [commute_iff_eq]
    exact t200_u_mul_c dD
  exact (h.pow_right (2 ^ (m - 2))).eq

theorem t200inv_d8_comm_c₂ (l : Bool) :
    dD.d8 false false l * (dD.c : G) ^ 2 ^ (m - 2) =
      (dD.c : G) ^ 2 ^ (m - 2) * dD.d8 false false l := by
  cases l
  · simp [dD.d8_fff]
  · rw [dD.d8_fft]
    exact t200inv_u_comm_c₂ dD

theorem t200inv_comm_c₂_nf (hm : 2 ≤ m) {p : ℕ}
    (hrel : Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) p)
    {v : Torus (StrothTypeIndex.t200 m).k} {l k : Bool}
    (h : (dD.ofTorus v * dD.d8 false false l * bpow e k) *
        (dD.c : G) ^ 2 ^ (m - 2) =
      (dD.c : G) ^ 2 ^ (m - 2) * (dD.ofTorus v * dD.d8 false false l * bpow e k)) :
    k = false := by
  have hA : (dD.ofTorus v * dD.d8 false false l) * (dD.c : G) ^ 2 ^ (m - 2) =
      (dD.c : G) ^ 2 ^ (m - 2) * (dD.ofTorus v * dD.d8 false false l) := by
    rw [mul_assoc, t200inv_d8_comm_c₂ dD l, ← mul_assoc, t200inv_ofTorus_comm_c₂ dD v,
      mul_assoc]
  have h_ek : bpow e k * (dD.c : G) ^ 2 ^ (m - 2) =
      (dD.c : G) ^ 2 ^ (m - 2) * bpow e k := by
    refine mul_left_cancel (a := dD.ofTorus v * dD.d8 false false l) ?_
    calc dD.ofTorus v * dD.d8 false false l * (bpow e k * (dD.c : G) ^ 2 ^ (m - 2))
        = (dD.ofTorus v * dD.d8 false false l * bpow e k) * (dD.c : G) ^ 2 ^ (m - 2) := by
          group
      _ = (dD.c : G) ^ 2 ^ (m - 2) * (dD.ofTorus v * dD.d8 false false l * bpow e k) := h
      _ = (dD.ofTorus v * dD.d8 false false l) *
            ((dD.c : G) ^ 2 ^ (m - 2) * bpow e k) := by
          rw [← mul_assoc, ← hA, mul_assoc]
  cases k
  · rfl
  · exfalso
    simp only [bpow, ↓reduceIte] at h_ek
    have hce : e⁻¹ * (dD.c : G) ^ 2 ^ (m - 2) * e = (dD.c : G) ^ 2 ^ (m - 2) := by
      calc e⁻¹ * (dD.c : G) ^ 2 ^ (m - 2) * e
          = e⁻¹ * ((dD.c : G) ^ 2 ^ (m - 2) * e) := by rw [mul_assoc]
        _ = e⁻¹ * (e * (dD.c : G) ^ 2 ^ (m - 2)) := by rw [← h_ek]
        _ = (dD.c : G) ^ 2 ^ (m - 2) := by group
    rw [t200inv_e_conj_c₂ dD hrel] at hce
    exact t200inv_c₂_ne_inv dD hm hce.symm

theorem t200inv_mul_self_mem (hm : 2 ≤ m)
    (hrel : Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) p) :
    ∀ s ∈ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) ⊓
      Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)},
      s * (dD.c : G) ^ 2 ^ (m - 2) = (dD.c : G) ^ 2 ^ (m - 2) * s → s * s ∈ D := by
  intro s hs hsc
  obtain ⟨v, l, k, rfl⟩ := t200_inv_mem_CSc₁ dD hrel (by omega) hs
  have hk : k = false := t200inv_comm_c₂_nf dD hm hrel hsc
  subst hk
  simp only [bpow, Bool.false_eq_true, ↓reduceIte, mul_one]
  rw [dD.nf_mul_self]
  cases l <;> simp [dD.d8_fff, dD.ofTorus_mem]

theorem t200inv_w₀_eq :
    (dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1) =
      dD.ofTorus (om200 m ![0, 1, 1]) := by
  rw [dD.t200_a_pow, dD.t200_b_pow, ← dD.ofTorus_add, om200_add]
  congr 1
  funext i
  fin_cases i <;> simp

theorem t200inv_d₂_sq :
    ((dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m) *
        ((dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m) =
      (dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1) := by
  have hcomm : (dD.b : G) ^ 2 ^ m * (dD.a : G) ^ 2 ^ m =
      (dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m :=
    congrArg Subtype.val (dD.isMulCommutative.is_comm.comm
      ⟨(dD.b : G) ^ 2 ^ m, D.pow_mem dD.b.2 _⟩
      ⟨(dD.a : G) ^ 2 ^ m, D.pow_mem dD.a.2 _⟩)
  have h2 : 2 ^ m * 2 = 2 ^ (m + 1) := by rw [← pow_succ]
  calc ((dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m) *
        ((dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m)
      = ((dD.a : G) ^ 2 ^ m * ((dD.b : G) ^ 2 ^ m * (dD.a : G) ^ 2 ^ m)) *
          (dD.b : G) ^ 2 ^ m := by group
    _ = ((dD.a : G) ^ 2 ^ m * ((dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m)) *
          (dD.b : G) ^ 2 ^ m := by rw [hcomm]
    _ = ((dD.a : G) ^ 2 ^ m * (dD.a : G) ^ 2 ^ m) *
          ((dD.b : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m) := by group
    _ = ((dD.a : G) ^ 2 ^ m) ^ 2 * ((dD.b : G) ^ 2 ^ m) ^ 2 := by
        rw [← sq, ← sq]
    _ = (dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1) := by
        rw [← pow_mul, ← pow_mul, h2]

theorem t200inv_w₀_mul_self :
    ((dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1)) *
        ((dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1)) = 1 := by
  have hcomm : (dD.b : G) ^ 2 ^ (m + 1) * (dD.a : G) ^ 2 ^ (m + 1) =
      (dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1) :=
    congrArg Subtype.val (dD.isMulCommutative.is_comm.comm
      ⟨(dD.b : G) ^ 2 ^ (m + 1), D.pow_mem dD.b.2 _⟩
      ⟨(dD.a : G) ^ 2 ^ (m + 1), D.pow_mem dD.a.2 _⟩)
  calc (dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1) *
        ((dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1))
      = (dD.a : G) ^ 2 ^ (m + 1) *
          ((dD.b : G) ^ 2 ^ (m + 1) * (dD.a : G) ^ 2 ^ (m + 1)) *
          (dD.b : G) ^ 2 ^ (m + 1) := by group
    _ = (dD.a : G) ^ 2 ^ (m + 1) *
          ((dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1)) *
          (dD.b : G) ^ 2 ^ (m + 1) := by rw [hcomm]
    _ = ((dD.a : G) ^ 2 ^ (m + 1) * (dD.a : G) ^ 2 ^ (m + 1)) *
          ((dD.b : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1)) := by group
    _ = 1 := by
        rw [Stroth47Fus.t200_a₁_mul_self dD, Stroth47Fus.t200_b₁_mul_self dD, mul_one]

theorem t200inv_w₀_ne_one (hm : 1 ≤ m) :
    (dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1) ≠ 1 := by
  intro h
  rw [t200inv_w₀_eq dD, ← dD.ofTorus_zero] at h
  have hh : dD.ofTorus (om200 m ![0, 1, 1]) = dD.ofTorus (om200 m 0) := by
    simpa [om200_zero] using h
  have h' := (om200_eq_iff hm ![0, 1, 1] 0).mp (dD.ofTorus_inj hh)
  have h1 := h' 1
  simp only [Matrix.cons_val_one, Matrix.head_cons, Pi.zero_apply] at h1
  norm_num [Int.ModEq] at h1

theorem t200inv_w₀_ne_c₁ (hm : 1 ≤ m) :
    (dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1) ≠
      (dD.c : G) ^ 2 ^ (m - 1) := by
  intro h
  rw [t200inv_w₀_eq dD, dD.t200_c_pow] at h
  have h' := (om200_eq_iff hm ![0, 1, 1] ![1, 0, 0]).mp (dD.ofTorus_inj h)
  have h1 := h' 1
  simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero] at h1
  norm_num [Int.ModEq] at h1

theorem t200inv_u_a₁ :
    dD.u * (dD.a : G) ^ 2 ^ (m + 1) = (dD.b : G) ^ 2 ^ (m + 1) * dD.u := by
  calc dD.u * (dD.a : G) ^ 2 ^ (m + 1)
      = (dD.u * (dD.a : G) ^ 2 ^ (m + 1) * dD.u) * dD.u := by
        rw [mul_assoc, dD.u_sq, mul_one]
    _ = (dD.b : G) ^ 2 ^ (m + 1) * dD.u := by
        rw [show dD.u * (dD.a : G) ^ 2 ^ (m + 1) * dD.u =
          dD.u⁻¹ * (dD.a : G) ^ 2 ^ (m + 1) * dD.u from by rw [dD.u_inv],
          Stroth47Fus.t200_u_a₁ dD]

theorem t200inv_u_b₁ :
    dD.u * (dD.b : G) ^ 2 ^ (m + 1) = (dD.a : G) ^ 2 ^ (m + 1) * dD.u := by
  calc dD.u * (dD.b : G) ^ 2 ^ (m + 1)
      = (dD.u * (dD.b : G) ^ 2 ^ (m + 1) * dD.u) * dD.u := by
        rw [mul_assoc, dD.u_sq, mul_one]
    _ = (dD.a : G) ^ 2 ^ (m + 1) * dD.u := by
        rw [show dD.u * (dD.b : G) ^ 2 ^ (m + 1) * dD.u =
          dD.u⁻¹ * (dD.b : G) ^ 2 ^ (m + 1) * dD.u from by rw [dD.u_inv],
          ← Stroth43Sc.conj_pow_eq, Stroth47Fus.t200_u_conj_b]

theorem t200inv_u_w₀ :
    dD.u * ((dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1)) =
      ((dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1)) * dD.u := by
  have hcomm : (dD.b : G) ^ 2 ^ (m + 1) * (dD.a : G) ^ 2 ^ (m + 1) =
      (dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1) :=
    congrArg Subtype.val (dD.isMulCommutative.is_comm.comm
      ⟨(dD.b : G) ^ 2 ^ (m + 1), D.pow_mem dD.b.2 _⟩
      ⟨(dD.a : G) ^ 2 ^ (m + 1), D.pow_mem dD.a.2 _⟩)
  calc dD.u * ((dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1))
      = (dD.u * (dD.a : G) ^ 2 ^ (m + 1)) * (dD.b : G) ^ 2 ^ (m + 1) := by
        rw [mul_assoc]
    _ = ((dD.b : G) ^ 2 ^ (m + 1) * dD.u) * (dD.b : G) ^ 2 ^ (m + 1) := by
        rw [t200inv_u_a₁ dD]
    _ = (dD.b : G) ^ 2 ^ (m + 1) *
          (dD.u * (dD.b : G) ^ 2 ^ (m + 1)) := by rw [mul_assoc]
    _ = (dD.b : G) ^ 2 ^ (m + 1) * ((dD.a : G) ^ 2 ^ (m + 1) * dD.u) := by
        rw [t200inv_u_b₁ dD]
    _ = (dD.b : G) ^ 2 ^ (m + 1) * (dD.a : G) ^ 2 ^ (m + 1) * dD.u := by
        rw [mul_assoc]
    _ = ((dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1)) * dD.u := by
        rw [hcomm]

theorem t200inv_e_comm_om (hm : 1 ≤ m) {p : ℕ}
    (hrel : Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) p)
    (ε : Fin 3 → ℤ) :
    e * dD.ofTorus (om200 m ε) = dD.ofTorus (om200 m ε) * e := by
  have hconj : e⁻¹ * dD.ofTorus (om200 m ε) * e = dD.ofTorus (om200 m ε) := by
    rw [(dD.t200invEAction hrel).conj_ofTorus, t200inv_φe_om dD hrel hm]
  have h2 : dD.ofTorus (om200 m ε) * e = e * dD.ofTorus (om200 m ε) := by
    have := congrArg (fun x => e * x) hconj
    simpa [mul_assoc] using this
  exact h2.symm

theorem t200inv_e_a₁ (hm : 1 ≤ m) {p : ℕ}
    (hrel : Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) p) :
    e * (dD.a : G) ^ 2 ^ (m + 1) = (dD.a : G) ^ 2 ^ (m + 1) * e := by
  rw [dD.t200_a_pow]
  exact t200inv_e_comm_om dD hm hrel _

theorem t200inv_e_b₁ (hm : 1 ≤ m) {p : ℕ}
    (hrel : Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) p) :
    e * (dD.b : G) ^ 2 ^ (m + 1) = (dD.b : G) ^ 2 ^ (m + 1) * e := by
  rw [dD.t200_b_pow]
  exact t200inv_e_comm_om dD hm hrel _

theorem t200inv_e_w₀ (hm : 1 ≤ m) {p : ℕ}
    (hrel : Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) p) :
    e * ((dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1)) =
      ((dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1)) * e := by
  rw [t200inv_w₀_eq dD]
  exact t200inv_e_comm_om dD hm hrel _

theorem t200inv_e_conj_d₂ (hm : 1 ≤ m) {p : ℕ}
    (hrel : Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) p) :
    e⁻¹ * ((dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m) * e =
      ((dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m)⁻¹ := by
  have hL : e⁻¹ * ((dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m) * e =
      dD.ofTorus (Torus.ofInt _ ![0, (-1 + (2 : ℤ) ^ (m + 1)) * 2 ^ m,
        (-1 + (2 : ℤ) ^ (m + 1)) * 2 ^ m]) := by
    rw [Stroth47Fus.t200_d₂_eq, (dD.t200invEAction hrel).conj_ofTorus,
      StrothWeakTypeData.t200inv_φe dD hrel]
    congr 1
  have hR : ((dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m)⁻¹ =
      dD.ofTorus (Torus.ofInt _ ![0, -(2 : ℤ) ^ m, -(2 : ℤ) ^ m]) := by
    rw [Stroth47Fus.t200_d₂_eq, ← dD.ofTorus_neg, ← Torus.ofInt_neg]
    congr 1
    funext i
    fin_cases i <;> simp
  rw [hL, hR]
  congr 1
  rw [t200_ofInt_eq_iff]
  have hd : -((2 : ℤ) ^ m) - (-1 + (2 : ℤ) ^ (m + 1)) * 2 ^ m =
      -((2 : ℤ) ^ (m + 1) * 2 ^ m) := by ring
  have h1 : (2 : ℤ) ^ (m + 1) * 2 ^ m = (2 : ℤ) ^ (m + 2) * 2 ^ (m - 1) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  refine ⟨⟨0, by simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]; ring⟩, ⟨-(2 ^ (m - 1)), ?_⟩,
    ⟨-(2 ^ (m - 1)), ?_⟩⟩
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    rw [hd, h1]
    ring
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    rw [hd, h1]
    ring

theorem t200inv_conj_sq (hm : 2 ≤ m)
    (hrel : Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) p) :
    ∀ y ∈ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) ⊓
      Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)}, y ∉ D →
      y * (dD.c : G) ^ 2 ^ (m - 2) = (dD.c : G) ^ 2 ^ (m - 2) * y →
      ∃ x ∈ D, ∃ d ∈ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) ⊓
          Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)},
        d * y = y * d ∧ x⁻¹ * y * x = y * (d * d) ∧ d * d ≠ 1 ∧
          d * d ≠ (dD.c : G) ^ 2 ^ (m - 1) := by
  intro y hy hyD hyc
  have hm1 : 1 ≤ m := by omega
  obtain ⟨v, l, k, rfl⟩ := t200_inv_mem_CSc₁ dD hrel hm1 hy
  have hk : k = false := t200inv_comm_c₂_nf dD hm hrel hyc
  subst hk
  simp only [bpow, Bool.false_eq_true, ↓reduceIte, mul_one] at hyD ⊢
  have hl : l = true := by
    cases l
    · exfalso
      exact hyD (by simpa [dD.d8_fff] using dD.ofTorus_mem v)
    · rfl
  subst hl
  simp only [dD.d8_fft]
  set a₁ : G := (dD.a : G) ^ 2 ^ (m + 1) with ha₁
  set b₁ : G := (dD.b : G) ^ 2 ^ (m + 1) with hb₁
  set d₂ : G := (dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m with hd₂
  have hcommD : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (dD.isMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have ha₁D : a₁ ∈ D := by rw [ha₁]; exact D.pow_mem dD.a.2 _
  have hb₁D : b₁ ∈ D := by rw [hb₁]; exact D.pow_mem dD.b.2 _
  have hd₂D : d₂ ∈ D := by
    rw [hd₂]
    exact D.mul_mem (D.pow_mem dD.a.2 _) (D.pow_mem dD.b.2 _)
  have hc₁D : (dD.c : G) ^ 2 ^ (m - 1) ∈ D := D.pow_mem dD.c.2 _
  have hd₂sq : d₂ * d₂ = a₁ * b₁ := by
    rw [hd₂, ha₁, hb₁, t200inv_d₂_sq dD]
  have hud₂ : dD.u⁻¹ * d₂ * dD.u = d₂ := by
    have hua : dD.u⁻¹ * (dD.a : G) ^ 2 ^ m * dD.u = (dD.b : G) ^ 2 ^ m := by
      rw [← Stroth43Sc.conj_pow_eq, Stroth47Fus.t200_u_conj_a]
    have hub : dD.u⁻¹ * (dD.b : G) ^ 2 ^ m * dD.u = (dD.a : G) ^ 2 ^ m := by
      rw [← Stroth43Sc.conj_pow_eq, Stroth47Fus.t200_u_conj_b]
    rw [hd₂]
    calc dD.u⁻¹ * ((dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m) * dD.u
        = (dD.u⁻¹ * (dD.a : G) ^ 2 ^ m * dD.u) *
            (dD.u⁻¹ * (dD.b : G) ^ 2 ^ m * dD.u) := by group
      _ = (dD.b : G) ^ 2 ^ m * (dD.a : G) ^ 2 ^ m := by rw [hua, hub]
      _ = (dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m :=
          hcommD _ (D.pow_mem dD.b.2 _) _ (D.pow_mem dD.a.2 _)
  have hud₂' : dD.u * d₂ * dD.u = d₂ := by simpa [dD.u_inv] using hud₂
  have hd₂u : d₂ * dD.u = dD.u * d₂ := by
    have h := congrArg (fun x => dD.u * x) hud₂'
    calc d₂ * dD.u = (dD.u * dD.u) * d₂ * dD.u := by rw [dD.u_sq, one_mul]
      _ = dD.u * (dD.u * d₂ * dD.u) := by group
      _ = dD.u * d₂ := h
  have hd₂y : d₂ * (dD.ofTorus v * dD.u) = (dD.ofTorus v * dD.u) * d₂ := by
    have hX : d₂ * dD.ofTorus v = dD.ofTorus v * d₂ :=
      hcommD _ hd₂D _ (dD.ofTorus_mem v)
    calc d₂ * (dD.ofTorus v * dD.u) = d₂ * dD.ofTorus v * dD.u := by group
      _ = dD.ofTorus v * d₂ * dD.u := by rw [hX]
      _ = dD.ofTorus v * (d₂ * dD.u) := by group
      _ = dD.ofTorus v * (dD.u * d₂) := by rw [hd₂u]
      _ = (dD.ofTorus v * dD.u) * d₂ := by group
  have ha₁inv : a₁⁻¹ = a₁ := by
    rw [ha₁]
    exact inv_eq_of_mul_eq_one_right (Stroth47Fus.t200_a₁_mul_self dD)
  have hua₁ : a₁ * dD.u = dD.u * b₁ := by
    rw [ha₁, hb₁]
    exact (t200inv_u_b₁ dD).symm
  have hconj : a₁⁻¹ * (dD.ofTorus v * dD.u) * a₁ = (dD.ofTorus v * dD.u) * (d₂ * d₂) := by
    rw [ha₁inv]
    calc a₁ * (dD.ofTorus v * dD.u) * a₁
        = (a₁ * dD.ofTorus v) * dD.u * a₁ := by group
      _ = (dD.ofTorus v * a₁) * dD.u * a₁ := by
          rw [hcommD _ ha₁D _ (dD.ofTorus_mem v)]
      _ = dD.ofTorus v * (a₁ * dD.u * a₁) := by group
      _ = dD.ofTorus v * (dD.u * b₁ * a₁) := by rw [hua₁]
      _ = (dD.ofTorus v * dD.u) * (a₁ * b₁) := by
          have hb₁a₁ : b₁ * a₁ = a₁ * b₁ := hcommD _ hb₁D _ ha₁D
          calc dD.ofTorus v * (dD.u * b₁ * a₁)
              = (dD.ofTorus v * dD.u) * (b₁ * a₁) := by group
            _ = (dD.ofTorus v * dD.u) * (a₁ * b₁) := by rw [hb₁a₁]
      _ = (dD.ofTorus v * dD.u) * (d₂ * d₂) := by rw [← hd₂sq]
  refine ⟨a₁, ha₁D, d₂, Subgroup.mem_inf.2 ⟨?_, ?_⟩, hd₂y, hconj, ?_, ?_⟩
  · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left hd₂D)
  · exact Subgroup.mem_centralizer_singleton_iff.mpr (hcommD _ hd₂D _ hc₁D)
  · rw [hd₂sq]
    simpa [ha₁, hb₁] using t200inv_w₀_ne_one dD hm1
  · rw [hd₂sq]
    simpa [ha₁, hb₁] using t200inv_w₀_ne_c₁ dD hm1

theorem t200inv_conj_inv (hm : 2 ≤ m)
    (hrel : Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) p) :
    ∀ y ∈ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) ⊓
      Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)},
      y * (dD.c : G) ^ 2 ^ (m - 2) ≠ (dD.c : G) ^ 2 ^ (m - 2) * y →
      ∃ x ∈ D, ∃ w ∈ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) ⊓
          Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)},
        w * y = y * w ∧ x⁻¹ * y * x = y * w ∧ w * w = 1 ∧ w ≠ 1 ∧
          w ≠ (dD.c : G) ^ 2 ^ (m - 1) := by
  intro y hy hnc
  have hm1 : 1 ≤ m := by omega
  obtain ⟨v, l, k, rfl⟩ := t200_inv_mem_CSc₁ dD hrel hm1 hy
  have hA : (dD.ofTorus v * dD.d8 false false l) * (dD.c : G) ^ 2 ^ (m - 2) =
      (dD.c : G) ^ 2 ^ (m - 2) * (dD.ofTorus v * dD.d8 false false l) := by
    rw [mul_assoc, t200inv_d8_comm_c₂ dD l, ← mul_assoc, t200inv_ofTorus_comm_c₂ dD v,
      mul_assoc]
  have hk : k = true := by
    cases k
    · exfalso
      apply hnc
      simpa [bpow] using hA
    · rfl
  subst hk
  simp only [bpow, ↓reduceIte]
  set a₁ : G := (dD.a : G) ^ 2 ^ (m + 1) with ha₁
  set b₁ : G := (dD.b : G) ^ 2 ^ (m + 1) with hb₁
  set d₂ : G := (dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m with hd₂
  set w : G := a₁ * b₁ with hw
  have hcommD : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (dD.isMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have ha₁D : a₁ ∈ D := by rw [ha₁]; exact D.pow_mem dD.a.2 _
  have hb₁D : b₁ ∈ D := by rw [hb₁]; exact D.pow_mem dD.b.2 _
  have hd₂D : d₂ ∈ D := by
    rw [hd₂]
    exact D.mul_mem (D.pow_mem dD.a.2 _) (D.pow_mem dD.b.2 _)
  have hw_expr : w = (dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1) := by
    rw [hw, ha₁, hb₁]
  have hwD : w ∈ D := by rw [hw]; exact D.mul_mem ha₁D hb₁D
  have hww : w * w = 1 := by rw [hw_expr]; exact t200inv_w₀_mul_self dD
  have hw1 : w ≠ 1 := by rw [hw_expr]; exact t200inv_w₀_ne_one dD hm1
  have hwc : w ≠ (dD.c : G) ^ 2 ^ (m - 1) := by
    rw [hw_expr]
    exact t200inv_w₀_ne_c₁ dD hm1
  have hw_mem : w ∈ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) ⊓
      Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)} :=
    Subgroup.mem_inf.2 ⟨Subgroup.mem_sup_left (Subgroup.mem_sup_left hwD),
      Subgroup.mem_centralizer_singleton_iff.mpr
        (hcommD _ hwD _ (D.pow_mem dD.c.2 _))⟩
  have hwX : w * dD.ofTorus v = dD.ofTorus v * w :=
    hcommD _ hwD _ (dD.ofTorus_mem v)
  have hwW : w * dD.d8 false false l = dD.d8 false false l * w := by
    cases l
    · simp [dD.d8_fff]
    · rw [dD.d8_fft]
      exact (by rw [hw_expr]; exact (t200inv_u_w₀ dD).symm)
  have hwe : w * e = e * w := by
    rw [hw_expr]
    exact (t200inv_e_w₀ dD hm1 hrel).symm
  have hwcomm : w * (dD.ofTorus v * dD.d8 false false l * e) =
      (dD.ofTorus v * dD.d8 false false l * e) * w := by
    calc w * (dD.ofTorus v * dD.d8 false false l * e)
        = (w * dD.ofTorus v) * dD.d8 false false l * e := by group
      _ = (dD.ofTorus v * w) * dD.d8 false false l * e := by rw [hwX]
      _ = dD.ofTorus v * (w * dD.d8 false false l) * e := by group
      _ = dD.ofTorus v * (dD.d8 false false l * w) * e := by rw [hwW]
      _ = dD.ofTorus v * dD.d8 false false l * (w * e) := by group
      _ = dD.ofTorus v * dD.d8 false false l * (e * w) := by rw [hwe]
      _ = (dD.ofTorus v * dD.d8 false false l * e) * w := by group
  cases l
  · simp only [dD.d8_fff, mul_one] at hwcomm ⊢
    have hed₂ : e⁻¹ * d₂ * e = d₂⁻¹ := by
      rw [hd₂]
      exact t200inv_e_conj_d₂ dD hm1 hrel
    have hd₂sq : d₂ * d₂ = w := by
      rw [hd₂, hw_expr]
      exact t200inv_d₂_sq dD
    have hXinv : d₂⁻¹ * dD.ofTorus v = dD.ofTorus v * d₂⁻¹ :=
      hcommD _ (D.inv_mem hd₂D) _ (dD.ofTorus_mem v)
    have hed₂' : e⁻¹ * d₂⁻¹ * e = d₂ := by
      calc e⁻¹ * d₂⁻¹ * e = (e⁻¹ * d₂ * e)⁻¹ := by group
        _ = (d₂⁻¹)⁻¹ := by rw [hed₂]
        _ = d₂ := inv_inv d₂
    have hconj : d₂⁻¹ * (dD.ofTorus v * e) * d₂ = (dD.ofTorus v * e) * w := by
      calc d₂⁻¹ * (dD.ofTorus v * e) * d₂
          = (d₂⁻¹ * dD.ofTorus v) * e * d₂ := by group
        _ = (dD.ofTorus v * d₂⁻¹) * e * d₂ := by rw [hXinv]
        _ = dD.ofTorus v * (d₂⁻¹ * e * d₂) := by group
        _ = dD.ofTorus v * (e * (e⁻¹ * d₂⁻¹ * e) * d₂) := by group
        _ = dD.ofTorus v * (e * d₂ * d₂) := by rw [hed₂']
        _ = dD.ofTorus v * (e * (d₂ * d₂)) := by group
        _ = dD.ofTorus v * (e * w) := by rw [hd₂sq]
        _ = (dD.ofTorus v * e) * w := by group
    exact ⟨d₂, hd₂D, w, hw_mem, hwcomm, hconj, hww, hw1, hwc⟩
  · simp only [dD.d8_fft] at hwcomm ⊢
    have ha₁inv : a₁⁻¹ = a₁ := by
      rw [ha₁]
      exact inv_eq_of_mul_eq_one_right (Stroth47Fus.t200_a₁_mul_self dD)
    have hua₁ : a₁ * dD.u = dD.u * b₁ := by
      rw [ha₁, hb₁]
      exact (t200inv_u_b₁ dD).symm
    have hea₁ : e * a₁ = a₁ * e := by
      rw [ha₁]
      exact t200inv_e_a₁ dD hm1 hrel
    have heb₁ : e * b₁ = b₁ * e := by
      rw [hb₁]
      exact t200inv_e_b₁ dD hm1 hrel
    have hb₁a₁e : (b₁ * a₁) * e = e * (b₁ * a₁) := by
      calc (b₁ * a₁) * e = b₁ * (a₁ * e) := by group
        _ = b₁ * (e * a₁) := by rw [hea₁.symm]
        _ = (b₁ * e) * a₁ := by group
        _ = (e * b₁) * a₁ := by rw [heb₁.symm]
        _ = e * (b₁ * a₁) := by group
    have ha₁X : a₁ * dD.ofTorus v = dD.ofTorus v * a₁ :=
      hcommD _ ha₁D _ (dD.ofTorus_mem v)
    have hconj : a₁⁻¹ * (dD.ofTorus v * dD.u * e) * a₁ =
        (dD.ofTorus v * dD.u * e) * w := by
      rw [ha₁inv]
      calc a₁ * (dD.ofTorus v * dD.u * e) * a₁
          = (a₁ * dD.ofTorus v) * dD.u * e * a₁ := by group
        _ = (dD.ofTorus v * a₁) * dD.u * e * a₁ := by rw [ha₁X]
        _ = dD.ofTorus v * (a₁ * dD.u) * (e * a₁) := by group
        _ = dD.ofTorus v * (dD.u * b₁) * (a₁ * e) := by rw [hua₁, hea₁]
        _ = dD.ofTorus v * dD.u * ((b₁ * a₁) * e) := by group
        _ = dD.ofTorus v * dD.u * (e * (b₁ * a₁)) := by rw [hb₁a₁e]
        _ = dD.ofTorus v * dD.u * e * (b₁ * a₁) := by group
        _ = dD.ofTorus v * dD.u * e * (a₁ * b₁) := by
            rw [hcommD _ hb₁D _ ha₁D]
        _ = (dD.ofTorus v * dD.u * e) * w := by rw [← hw]
    exact ⟨a₁, ha₁D, w, hw_mem, hwcomm, hconj, hww, hw1, hwc⟩

end Stroth47Core

end CFSG.CGT.Stroth77
