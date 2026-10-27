module

public import CFSG.CGT.Stroth77.Section42Core

public section

namespace CFSG.CGT.Stroth77

open Matrix

namespace Type300

theorem uvM_mulVec (x : Fin 3 → ℤ) :
    uvM *ᵥ x = ![-3 * x 0 + 4 * x 1 + 4 * x 2, -x 0 + x 1 + 2 * x 2, -x 0 + 2 * x 1 + x 2] := by
  funext i
  fin_cases i <;> simp [uvM, uvA, tM, ρM] <;> ring

theorem tM_mulVec (x : Fin 3 → ℤ) :
    tM *ᵥ x = ![x 0 - 4 * x 2, x 0 - x 1 - 2 * x 2, -x 2] := by
  funext i
  fin_cases i <;> simp [uvA, tM, ρM] <;> ring

theorem uM_mulVec (x : Fin 3 → ℤ) : uM *ᵥ x = ![x 0, x 2, x 1] := by
  funext i
  fin_cases i <;> simp [uM, uMat]

theorem ρM_mulVec (x : Fin 3 → ℤ) : ρM *ᵥ x = ![x 0 - 4 * x 2, -x 2, x 1 - x 2] := by
  funext i
  fin_cases i <;> simp [ρM] <;> ring

end Type300

namespace Stroth42Core

theorem t300_k (n : ℕ) (i : Fin 3) : (StrothTypeIndex.t300 n).k i = n := by
  fin_cases i <;> rfl

variable {n : ℕ}

theorem t300_φuv (x : Fin 3 → ℤ) :
    (StrothTypeIndex.t300 n).action.φuv (Torus.ofInt _ x) = Torus.ofInt _
      ![-3 * x 0 + 4 * x 1 + 4 * x 2, -x 0 + x 1 + 2 * x 2, -x 0 + 2 * x 1 + x 2] := by
  have h := matAct_ofInt (k := (StrothTypeIndex.t300 n).k) Type300.uvM
    (StrothTypeIndex.t300 n).action.compat_uv x
  rw [Type300.uvM_mulVec] at h
  exact h

theorem t300_φt (x : Fin 3 → ℤ) :
    (StrothTypeIndex.t300 n).action.φt (Torus.ofInt _ x) =
      Torus.ofInt _ ![x 0 - 4 * x 2, x 0 - x 1 - 2 * x 2, -x 2] := by
  have h := matAct_ofInt (k := (StrothTypeIndex.t300 n).k) Type300.tM
    (StrothTypeIndex.t300 n).action.compat_t x
  rw [Type300.tM_mulVec] at h
  exact h

theorem t300_φu (x : Fin 3 → ℤ) :
    (StrothTypeIndex.t300 n).action.φu (Torus.ofInt _ x) = Torus.ofInt _ ![x 0, x 2, x 1] := by
  have h := matAct_ofInt (k := (StrothTypeIndex.t300 n).k) Type300.uM
    (StrothTypeIndex.t300 n).action.compat_u x
  rw [Type300.uM_mulVec] at h
  exact h

theorem t300_φρ (x : Fin 3 → ℤ) :
    (StrothTypeIndex.t300 n).action.φρ (Torus.ofInt _ x) =
      Torus.ofInt _ ![x 0 - 4 * x 2, -x 2, x 1 - x 2] := by
  have h := matAct_ofInt (k := (StrothTypeIndex.t300 n).k) Type300.ρM
    (StrothTypeIndex.t300 n).action.compat_ρ x
  rw [Type300.ρM_mulVec] at h
  exact h

theorem t300_ofInt_eq_iff (x y : Fin 3 → ℤ) :
    Torus.ofInt (StrothTypeIndex.t300 n).k x = Torus.ofInt _ y ↔
      (2 : ℤ) ^ n ∣ y 0 - x 0 ∧ (2 : ℤ) ^ n ∣ y 1 - x 1 ∧ (2 : ℤ) ^ n ∣ y 2 - x 2 := by
  rw [Torus.ofInt_eq_ofInt_iff, Fin.forall_fin_succ, Fin.forall_fin_succ, Fin.forall_fin_succ]
  simp [Int.modEq_iff_dvd, t300_k]

theorem t300_ofInt_eq_zero_iff (x : Fin 3 → ℤ) :
    Torus.ofInt (StrothTypeIndex.t300 n).k x = 0 ↔
      (2 : ℤ) ^ n ∣ x 0 ∧ (2 : ℤ) ^ n ∣ x 1 ∧ (2 : ℤ) ^ n ∣ x 2 := by
  rw [← Torus.ofInt_zero, t300_ofInt_eq_iff]
  simp

@[expose] def om300 (n : ℕ) (ε : Fin 3 → ℤ) : Torus (StrothTypeIndex.t300 n).k :=
  Torus.ofInt _ (fun i => ε i * 2 ^ (n - 1))

theorem om300_eq_iff (hn : 1 ≤ n) (ε ε' : Fin 3 → ℤ) :
    om300 n ε = om300 n ε' ↔ ∀ i, ε i ≡ ε' i [ZMOD 2] := by
  have h := ofInt_mul_two_pow_pred_eq_iff (k := (StrothTypeIndex.t300 n).k)
    (fun i => by rw [t300_k]; exact hn) ε ε'
  simp only [t300_k] at h
  exact h

theorem om300_zero : om300 n 0 = 0 := by
  rw [om300, ← Torus.ofInt_zero]
  congr 1
  funext i
  simp

theorem om300_add_self (hn : 1 ≤ n) (ε : Fin 3 → ℤ) : om300 n ε + om300 n ε = 0 := by
  rw [om300, ← Torus.ofInt_add, ← om300_zero, om300]
  rw [show (fun i => ε i * 2 ^ (n - 1)) + (fun i => ε i * 2 ^ (n - 1)) =
    fun i => (2 * ε i) * 2 ^ (n - 1) by funext i; simp; ring]
  exact (om300_eq_iff hn _ _).mpr fun i => by
    simp only [Pi.zero_apply]
    exact (Int.emod_emod_of_dvd _ (dvd_refl 2)).symm.trans (by simp)

theorem t300_φuv_om (ε : Fin 3 → ℤ) :
    (StrothTypeIndex.t300 n).action.φuv (om300 n ε) =
      om300 n ![-3 * ε 0 + 4 * ε 1 + 4 * ε 2, -ε 0 + ε 1 + 2 * ε 2, -ε 0 + 2 * ε 1 + ε 2] := by
  rw [om300, t300_φuv, om300]
  congr 1
  funext i
  fin_cases i <;> simp <;> ring

theorem t300_φt_om (ε : Fin 3 → ℤ) :
    (StrothTypeIndex.t300 n).action.φt (om300 n ε) =
      om300 n ![ε 0 - 4 * ε 2, ε 0 - ε 1 - 2 * ε 2, -ε 2] := by
  rw [om300, t300_φt, om300]
  congr 1
  funext i
  fin_cases i <;> simp <;> ring

theorem t300_φu_om (ε : Fin 3 → ℤ) :
    (StrothTypeIndex.t300 n).action.φu (om300 n ε) = om300 n ![ε 0, ε 2, ε 1] := by
  rw [om300, t300_φu, om300]
  congr 1
  funext i
  fin_cases i <;> simp

theorem t300_φρ_om (ε : Fin 3 → ℤ) :
    (StrothTypeIndex.t300 n).action.φρ (om300 n ε) =
      om300 n ![ε 0 - 4 * ε 2, -ε 2, ε 1 - ε 2] := by
  rw [om300, t300_φρ, om300]
  congr 1
  funext i
  fin_cases i <;> simp <;> ring

theorem t300_faithful (hn : 1 ≤ n) (i j l : Bool)
    (h : ∀ v, (StrothTypeIndex.t300 n).action.d8Act i j l v = v) :
    i = false ∧ j = false ∧ l = false := by
  have hc := h (om300 n ![1, 0, 0])
  have ha := h (om300 n ![0, 1, 0])
  cases i <;> cases j <;> cases l <;>
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte,
      AddMonoidHom.comp_apply, AddMonoidHom.id_apply, t300_φuv_om, t300_φt_om, t300_φu_om,
      om300_eq_iff hn] at hc ha <;>
    first
    | exact ⟨rfl, rfl, rfl⟩
    | exact absurd hc (by decide)
    | exact absurd ha (by decide)

theorem t300_parity (hn : 1 ≤ n) (i j l : Bool) (v : Torus (StrothTypeIndex.t300 n).k) :
    Even (((StrothTypeIndex.t300 n).action.d8Act i j l v) 0) ↔ Even (v 0) := by
  have hk : 1 ≤ (StrothTypeIndex.t300 n).k 0 := by rw [t300_k]; exact hn
  refine SigmaFourAction.even_d8Act_zero_iff _ ?_ ?_ ?_ i j l v
  · exact even_matAct_zero_iff hk Type300.uvM (Type300.compat_uv n) (by decide) (by decide)
      (by decide)
  · exact even_matAct_zero_iff hk Type300.tM (Type300.compat_t n) (by decide) (by decide)
      (by decide)
  · exact even_matAct_zero_iff hk Type300.uM (Type300.compat_u n) (by decide) (by decide)
      (by decide)

theorem t300_d8Act_ofInt (i j l : Bool) (x : Fin 3 → ℤ) :
    ∃ y : Fin 3 → ℤ, (StrothTypeIndex.t300 n).action.d8Act i j l (Torus.ofInt _ x) =
      Torus.ofInt _ y ∧ y 0 ≡ x 0 [ZMOD 4] := by
  cases i <;> cases j <;> cases l <;>
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, t300_φuv, t300_φt, t300_φu] <;>
    refine ⟨_, rfl, ?_⟩ <;> simp [Int.ModEq] <;> omega

end Stroth42Core

open Stroth42Core

namespace StrothWeakTypeData

variable {G : Type*} [Group G] {D : Subgroup G} {n : ℕ}
  (dD : StrothWeakTypeData D (.t300 n))

theorem t300_c_pow : (dD.c : G) ^ 2 ^ (n - 1) = dD.ofTorus (om300 n ![1, 0, 0]) := by
  rw [c_eq, ← ofTorus_nsmul]
  congr 1
  funext i
  fin_cases i <;> simp [om300, gen, Pi.single_apply]

theorem t300_a_pow : (dD.a : G) ^ 2 ^ (n - 1) = dD.ofTorus (om300 n ![0, 1, 0]) := by
  rw [a_eq, ← ofTorus_nsmul]
  congr 1
  funext i
  fin_cases i <;> simp [om300, gen, Pi.single_apply]

theorem t300_eq_om_of_mul_self (hn : 1 ≤ n) {y : G} (hy : y ∈ D) (h2 : y * y = 1) :
    ∃ ε : Fin 3 → ℤ, (∀ i, ε i = 0 ∨ ε i = 1) ∧ y = dD.ofTorus (om300 n ε) := by
  obtain ⟨v, rfl⟩ := dD.exists_ofTorus hy
  rw [ofTorus_mul_self, ofTorus_eq_one_iff] at h2
  have h2' : (2 : ℤ) • v = 0 := by rw [two_zsmul]; exact h2
  obtain ⟨ε, hε, rfl⟩ :=
    (Torus.two_zsmul_eq_zero_iff (fun i => by rw [t300_k]; exact hn) v).mp h2'
  refine ⟨ε, hε, ?_⟩
  congr 1
  funext i
  simp [om300, t300_k]

theorem t300_h1 (hn : 3 ≤ n) :
    (Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u}).relIndex
      (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}) = 2 :=
  dD.relIndex_S₁ (by rw [t300_k]; omega) (t300_faithful (by omega)) (t300_parity (by omega))

theorem t300_h2 (hn : 3 ≤ n) :
    (dD.c : G) ∉
      Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u} :=
  dD.c_not_mem_S₁ (by rw [t300_k]; omega) (t300_faithful (by omega)) (t300_parity (by omega))

theorem t300_h5 :
    ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}, y * y ∈ D ∨ y * y * dD.uv ∈ D :=
  dD.mul_self_mem_or

theorem t300_h3 (hn : 3 ≤ n) :
    ∀ y ∈ D, y * y = 1 → y ≠ 1 →
      (∃ p ∈ Subgroup.closure {dD.uv, dD.t, dD.u}, p⁻¹ * y * p = (dD.c : G) ^ 2 ^ (n - 1)) ∨
        ∃ g ∈ dD.L, g⁻¹ * y * g = (dD.a : G) ^ 2 ^ (n - 1) := by
  intro y hy h2 h1
  have hn1 : 1 ≤ n := by omega
  obtain ⟨ε, hε, rfl⟩ := dD.t300_eq_om_of_mul_self hn1 hy h2
  rw [dD.t300_c_pow, dD.t300_a_pow]
  have hW : ∀ x ∈ ({dD.uv, dD.t, dD.u} : Set G), x ∈ Subgroup.closure {dD.uv, dD.t, dD.u} :=
    fun x hx => Subgroup.subset_closure hx
  have hconj_uv := dD.conj_ofTorus dD.uv_mem dD.uv_conj
  have hconj_t := dD.conj_ofTorus dD.t_mem dD.t_conj
  have hconj_ρ := dD.conj_ofTorus dD.ρ_mem dD.ρ_conj
  have hε0 : ¬ (ε 0 = 0 ∧ ε 1 = 0 ∧ ε 2 = 0) := by
    rintro ⟨h0, h1', h2'⟩
    apply h1
    rw [← dD.ofTorus_zero, ← om300_zero]
    congr 1
    congr 1
    funext i
    fin_cases i <;> simp [h0, h1', h2']
  have hεv : ε = ![ε 0, ε 1, ε 2] := by
    funext i; fin_cases i <;> rfl
  rcases hε 0 with e0 | e0 <;> rcases hε 1 with e1 | e1 <;> rcases hε 2 with e2 | e2 <;>
    rw [hεv, e0, e1, e2]
  · exact absurd ⟨e0, e1, e2⟩ hε0
  ·
    right
    refine ⟨dD.ρ * dD.ρ, mul_mem dD.ρ_mem_L dD.ρ_mem_L, ?_⟩
    rw [mul_inv_rev, show (dD.ρ⁻¹ * dD.ρ⁻¹ * dD.ofTorus (om300 n ![0, 0, 1]) * (dD.ρ * dD.ρ)) =
      dD.ρ⁻¹ * (dD.ρ⁻¹ * dD.ofTorus (om300 n ![0, 0, 1]) * dD.ρ) * dD.ρ by group, hconj_ρ,
      hconj_ρ, t300_φρ_om, t300_φρ_om]
    exact congrArg dD.ofTorus ((om300_eq_iff hn1 _ _).mpr (by decide))
  ·
    right
    exact ⟨1, one_mem _, by simp⟩
  ·
    right
    refine ⟨dD.ρ, dD.ρ_mem_L, ?_⟩
    rw [hconj_ρ, t300_φρ_om]
    exact congrArg dD.ofTorus ((om300_eq_iff hn1 _ _).mpr (by decide))
  ·
    left
    exact ⟨1, one_mem _, by simp⟩
  ·
    left
    refine ⟨dD.uv * dD.t, mul_mem (hW _ (by simp)) (hW _ (by simp)), ?_⟩
    rw [mul_inv_rev, show dD.t⁻¹ * dD.uv⁻¹ * dD.ofTorus (om300 n ![1, 0, 1]) * (dD.uv * dD.t) =
      dD.t⁻¹ * (dD.uv⁻¹ * dD.ofTorus (om300 n ![1, 0, 1]) * dD.uv) * dD.t by group, hconj_uv,
      hconj_t, t300_φuv_om, t300_φt_om]
    exact congrArg dD.ofTorus ((om300_eq_iff hn1 _ _).mpr (by decide))
  ·
    left
    refine ⟨dD.t, hW _ (by simp), ?_⟩
    rw [hconj_t, t300_φt_om]
    exact congrArg dD.ofTorus ((om300_eq_iff hn1 _ _).mpr (by decide))
  ·
    left
    refine ⟨dD.uv, hW _ (by simp), ?_⟩
    rw [hconj_uv, t300_φuv_om]
    exact congrArg dD.ofTorus ((om300_eq_iff hn1 _ _).mpr (by decide))

theorem t300_comm_z (hn : 1 ≤ n) {v : Torus (StrothTypeIndex.t300 n).k} {i j l : Bool}
    (h : dD.ofTorus v * dD.d8 i j l * (dD.c : G) ^ 2 ^ (n - 1) =
      (dD.c : G) ^ 2 ^ (n - 1) * (dD.ofTorus v * dD.d8 i j l)) : i = false ∧ j = false := by
  rw [dD.t300_c_pow, nf_commute_iff] at h
  cases i <;> cases j <;> cases l <;>
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, t300_φuv_om, t300_φt_om, t300_φu_om, om300_eq_iff hn] at h <;>
    first
    | exact ⟨rfl, rfl⟩
    | exact absurd h (by decide)

theorem t300_h4 (hn : 3 ≤ n) :
    ∀ y ∈ Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u},
      y * (dD.c : G) ^ 2 ^ (n - 1) = (dD.c : G) ^ 2 ^ (n - 1) * y →
        y ^ 2 ^ (n - 1) ≠ (dD.c : G) ^ 2 ^ (n - 1) := by
  intro y hy hcomm hpow
  have hn1 : 1 ≤ n := by omega
  have hk : 1 ≤ (StrothTypeIndex.t300 n).k 0 := by rw [t300_k]; exact hn1
  obtain ⟨v, i, j, l, hv, rfl⟩ := (dD.mem_S₁_iff hk (t300_parity hn1)).mp hy
  obtain ⟨rfl, rfl⟩ := dD.t300_comm_z hn1 hcomm
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
  rw [Torus.ofInt_apply, even_intCast_iff hk] at hv
  obtain ⟨r, hr⟩ := hv
  have hd8 : dD.d8 (l && false) false false = 1 := by rw [Bool.and_false, d8_fff]
  rw [pow_two_pow_eq_mul_self _ (by omega : 1 ≤ n - 1), nf_mul_self, hd8, mul_one,
    ← ofTorus_nsmul, dD.t300_c_pow] at hpow
  have hpow' := dD.ofTorus_inj hpow
  have hu : (StrothTypeIndex.t300 n).action.d8Act false false l (Torus.ofInt _ x) =
      Torus.ofInt _ ![x 0, if l then x 2 else x 1, if l then x 1 else x 2] := by
    cases l <;> simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte,
      AddMonoidHom.comp_apply, AddMonoidHom.id_apply, t300_φu]
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [hu, ← Torus.ofInt_add, ← natCast_zsmul, ← Torus.ofInt_zsmul, om300,
    t300_ofInt_eq_iff] at hpow'
  obtain ⟨h0, -, -⟩ := hpow'
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero] at h0
  rw [hr] at h0
  exact not_two_pow_dvd_aux (n := n) (by omega) r (by push_cast at h0; exact h0)

theorem t300_odd_of_not_mem (hn1 : 1 ≤ n) {x : Fin 3 → ℤ} {i j l : Bool}
    (hy1 : dD.ofTorus (Torus.ofInt _ x) * dD.d8 i j l ∉
      Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u}) :
    x 0 % 2 = 1 := by
  have hk : 1 ≤ (StrothTypeIndex.t300 n).k 0 := by rw [t300_k]; exact hn1
  have hv : ¬ Even ((Torus.ofInt (StrothTypeIndex.t300 n).k x) 0) := fun h =>
    hy1 ((dD.mem_S₁_iff hk (t300_parity hn1)).mpr ⟨_, i, j, l, h, rfl⟩)
  rw [Torus.ofInt_apply, even_intCast_iff hk, Int.not_even_iff] at hv
  exact hv

theorem t300_h6' (hn : 3 ≤ n) :
    ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u},
      y ∉ Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u} →
      y * y ≠ 1 := by
  intro y hy hy1 hyy
  have hn1 : 1 ≤ n := by omega
  obtain ⟨v, i, j, l, rfl⟩ := dD.mem_sup_iff.mp hy
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
  have hodd := dD.t300_odd_of_not_mem hn1 hy1
  rw [nf_mul_self] at hyy
  cases hlj : (l && j)
  · rw [hlj, d8_fff, mul_one, ofTorus_eq_one_iff] at hyy
    obtain ⟨y', hy', hmod⟩ := t300_d8Act_ofInt i j l x
    rw [hy', ← Torus.ofInt_add, t300_ofInt_eq_zero_iff] at hyy
    obtain ⟨h0, -, -⟩ := hyy
    have h4 := two_pow_dvd_four (by omega : 2 ≤ n) h0
    simp only [Pi.add_apply] at h4
    unfold Int.ModEq at hmod
    omega
  · rw [hlj, d8_tff] at hyy
    have hnot := dD.d8_not_mem (t300_faithful hn1) (i := true) (j := false) (l := false)
      (by decide) (Torus.ofInt (StrothTypeIndex.t300 n).k x +
        (StrothTypeIndex.t300 n).action.d8Act i j l (Torus.ofInt _ x))
    rw [d8_tff, hyy] at hnot
    exact hnot (one_mem _)

theorem t300_h8 (hn : 3 ≤ n) :
    ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u},
      y ∉ Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u} →
      ∀ l : ℕ, 1 ≤ l → y ^ 2 ^ l = (dD.c : G) ^ 2 ^ (n - 1) → y ^ 2 ^ (n - 1) ≠ 1 := by
  intro y hy hy1 m hm hz
  have hn1 : 1 ≤ n := by omega
  obtain ⟨v, i, j, l, rfl⟩ := dD.mem_sup_iff.mp hy
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
  have hodd := dD.t300_odd_of_not_mem hn1 hy1
  cases hlj : (l && j)
  · intro h1
    rw [pow_two_pow_eq_mul_self _ (by omega : 1 ≤ n - 1), nf_mul_self, hlj, d8_fff, mul_one,
      ← ofTorus_nsmul, ofTorus_eq_one_iff] at h1
    obtain ⟨y', hy', hmod⟩ := t300_d8Act_ofInt i j l x
    rw [hy', ← Torus.ofInt_add, ← natCast_zsmul, ← Torus.ofInt_zsmul,
      t300_ofInt_eq_zero_iff] at h1
    obtain ⟨h0, -, -⟩ := h1
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at h0
    push_cast at h0
    have h4 := four_dvd_of_two_pow_dvd_mul (by omega : n - 1 - 1 + 2 = n) h0
    unfold Int.ModEq at hmod
    omega
  · exfalso
    have hl : l = true := (Bool.and_eq_true_iff.mp hlj).1
    have hj : j = true := (Bool.and_eq_true_iff.mp hlj).2
    subst hl hj
    have hsq : (dD.ofTorus (Torus.ofInt _ x) * dD.d8 i true true) *
        (dD.ofTorus (Torus.ofInt _ x) * dD.d8 i true true) =
        dD.ofTorus (Torus.ofInt _ x + (StrothTypeIndex.t300 n).action.d8Act i true true
          (Torus.ofInt _ x)) * dD.d8 true false false := by
      rw [nf_mul_self]; rfl
    have h4 : (dD.ofTorus (Torus.ofInt _ x) * dD.d8 i true true) *
        (dD.ofTorus (Torus.ofInt _ x) * dD.d8 i true true) *
        ((dD.ofTorus (Torus.ofInt _ x) * dD.d8 i true true) *
        (dD.ofTorus (Torus.ofInt _ x) * dD.d8 i true true)) = 1 := by
      rw [hsq, nf_mul_self, Bool.and_false, d8_fff, mul_one, ofTorus_eq_one_iff]
      cases i <;>
        simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte,
          AddMonoidHom.comp_apply, AddMonoidHom.id_apply, t300_φuv, t300_φt, t300_φu,
          ← Torus.ofInt_add] <;>
        rw [← Torus.ofInt_zero] <;> congr 1 <;> funext i <;> fin_cases i <;>
        simp [Matrix.vecHead, Matrix.vecTail] <;> ring
    have hz1 : (dD.c : G) ^ 2 ^ (n - 1) ≠ 1 := by
      rw [dD.t300_c_pow, Ne, ofTorus_eq_one_iff, ← om300_zero, om300_eq_iff hn1]
      decide
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    ·
      have hm1 : m = 1 := by omega
      subst hm1
      rw [pow_one, sq, hsq] at hz
      have hnot := dD.d8_not_mem (t300_faithful hn1) (i := true) (j := false) (l := false)
        (by decide) (Torus.ofInt (StrothTypeIndex.t300 n).k x +
          (StrothTypeIndex.t300 n).action.d8Act i true true (Torus.ofInt _ x))
      rw [hz] at hnot
      exact hnot (pow_mem dD.c.2 _)
    · rw [pow_two_pow_eq_mul_self _ hm, pow_two_pow_eq_mul_self _ (by omega : 1 ≤ m - 1), h4,
        one_pow] at hz
      exact hz1 hz.symm

theorem t300_om_comm {v : Torus (StrothTypeIndex.t300 n).k} {i j l : Bool} {ε : Fin 3 → ℤ}
    (h : (StrothTypeIndex.t300 n).action.d8Act i j l (om300 n ε) = om300 n ε) :
    dD.ofTorus (om300 n ε) * (dD.ofTorus v * dD.d8 i j l) =
      dD.ofTorus v * dD.d8 i j l * dD.ofTorus (om300 n ε) :=
  ((dD.nf_commute_iff v (om300 n ε) i j l).mpr h).symm

theorem t300_h6 (hn : 3 ≤ n) :
    ∀ y : G, y * dD.uv ∈ D → y * y = 1 → ∃ E : Subgroup G,
      E ≤ Subgroup.centralizer {y} ∧ (∀ e ∈ E, e * e = 1) ∧ Nat.card E = 16 := by
  intro y hy hyy
  have hn1 : 1 ≤ n := by omega
  have hF := t300_faithful (n := n) hn1
  obtain ⟨v, hv⟩ := dD.exists_ofTorus hy
  have hyv : y = dD.ofTorus v * dD.d8 true false false := by
    rw [d8_tff, ← hv, mul_assoc, dD.uv_sq, mul_one]
  subst hyv
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
  have hsq := hyy
  rw [nf_mul_self, Bool.and_false, d8_fff, mul_one, ofTorus_eq_one_iff] at hsq
  simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
    AddMonoidHom.id_apply, t300_φuv] at hsq
  rw [← Torus.ofInt_add, t300_ofInt_eq_zero_iff] at hsq
  obtain ⟨-, hsq1, -⟩ := hsq
  simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero] at hsq1
  set w : Fin 3 → ℤ := ![0, -x 2, 0] with hw
  have hdecide : ∀ (ε ε' : Fin 3 → ℤ), (∀ i, ε i ≡ ε' i [ZMOD 2]) → om300 n ε = om300 n ε' :=
    fun ε ε' h => (om300_eq_iff hn1 ε ε').mpr h
  refine Stroth42Core.exists_E16 (H := D) (x₁ := dD.ofTorus (om300 n ![0, 1, 0]))
    (x₂ := dD.ofTorus (om300 n ![0, 0, 1]))
    (y₃ := dD.ofTorus (Torus.ofInt _ x) * dD.d8 true false false)
    (y₄ := dD.ofTorus (Torus.ofInt _ w) * dD.d8 false true false)
    (dD.ofTorus_mem _) (dD.ofTorus_mem _) ?_ ?_ hyy ?_ (dD.ofTorus_comm _ _) ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?_
  · rw [ofTorus_mul_self, om300_add_self hn1, ofTorus_zero]
  · rw [ofTorus_mul_self, om300_add_self hn1, ofTorus_zero]
  · rw [nf_mul_self, Bool.and_true, d8_fff, mul_one, ofTorus_eq_one_iff]
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, t300_φt, ← Torus.ofInt_add]
    rw [← Torus.ofInt_zero]
    congr 1
    funext i
    fin_cases i <;> simp [hw]
  · refine dD.t300_om_comm ?_
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, t300_φuv_om]
    exact hdecide _ _ (by decide)
  · refine dD.t300_om_comm ?_
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, t300_φt_om]
    exact hdecide _ _ (by decide)
  · refine dD.t300_om_comm ?_
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, t300_φuv_om]
    exact hdecide _ _ (by decide)
  · refine dD.t300_om_comm ?_
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, t300_φt_om]
    exact hdecide _ _ (by decide)
  ·
    rw [nf_mul_nf, nf_mul_nf]
    congr 1
    congr 1
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, t300_φuv, t300_φt, ← Torus.ofInt_add]
    rw [t300_ofInt_eq_iff]
    simp only [hw, Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    refine ⟨⟨0, by ring⟩, ?_, ⟨0, by ring⟩⟩
    obtain ⟨c, hc⟩ := hsq1
    exact ⟨-c, by linear_combination -hc⟩
  · rw [Ne, ofTorus_eq_one_iff, ← om300_zero, om300_eq_iff hn1]
    decide
  · rw [Ne, ofTorus_eq_one_iff, ← om300_zero, om300_eq_iff hn1]
    decide
  · rw [Ne, dD.ofTorus_inj.eq_iff, om300_eq_iff hn1]
    decide
  · exact dD.d8_not_mem hF (by decide) _
  · exact dD.d8_not_mem hF (by decide) _
  · rw [nf_mul_nf]
    exact dD.d8_not_mem hF (by decide) _
  · refine dD.t300_om_comm ?_
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, t300_φuv_om]
    exact hdecide _ _ (by decide)
  · refine dD.t300_om_comm ?_
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, t300_φuv_om]
    exact hdecide _ _ (by decide)
  ·
    rw [nf_mul_nf, nf_mul_nf]
    congr 1
    congr 1
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, t300_φuv, t300_φt, ← Torus.ofInt_add]
    rw [t300_ofInt_eq_iff]
    simp only [hw, Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    refine ⟨⟨0, by ring⟩, ?_, ⟨0, by ring⟩⟩
    obtain ⟨c, hc⟩ := hsq1
    exact ⟨c, by linear_combination hc⟩

theorem t300_mem_CSz (hn1 : 1 ≤ n) {y : G}
    (hy : y ∈ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}) ⊓
      Subgroup.centralizer {(dD.c : G) ^ 2 ^ (n - 1)}) :
    ∃ (v : Torus (StrothTypeIndex.t300 n).k) (l : Bool), y = dD.ofTorus v * dD.d8 false false l := by
  obtain ⟨hyS, hyC⟩ := Subgroup.mem_inf.mp hy
  obtain ⟨v, i, j, l, rfl⟩ := dD.mem_sup_iff.mp hyS
  rw [Subgroup.mem_centralizer_iff] at hyC
  have hc := hyC _ (Set.mem_singleton _)
  obtain ⟨rfl, rfl⟩ := dD.t300_comm_z hn1 hc.symm
  exact ⟨v, l, rfl⟩

theorem t300_mem_CSz_of_not_mem (hn1 : 1 ≤ n) {y : G}
    (hy : y ∈ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}) ⊓
      Subgroup.centralizer {(dD.c : G) ^ 2 ^ (n - 1)}) (hyD : y ∉ D) :
    ∃ v : Torus (StrothTypeIndex.t300 n).k, y = dD.ofTorus v * dD.d8 false false true := by
  obtain ⟨v, l, rfl⟩ := dD.t300_mem_CSz hn1 hy
  cases l
  · exact absurd (by rw [d8_fff, mul_one]; exact dD.ofTorus_mem v) hyD
  · exact ⟨v, rfl⟩

theorem t300_h7 (hn : 3 ≤ n) :
    ∀ E : Subgroup G, E ≤ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}) ⊓
      Subgroup.centralizer {(dD.c : G) ^ 2 ^ (n - 1)} → (∀ e ∈ E, e * e = 1) →
        Nat.card E ≠ 16 := by
  intro E hE hinv hcard
  have hn1 : 1 ≤ n := by omega
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    have h1 := inv_eq_of_mul_eq_one_right (hinv a ha)
    have h2 := inv_eq_of_mul_eq_one_right (hinv b hb)
    have h3 := inv_eq_of_mul_eq_one_right (hinv _ (mul_mem ha hb))
    calc a * b = (a * b)⁻¹ := h3.symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [h1, h2]
  have hD1 : ∀ e ∈ E, e ∈ D → ∃ a b c : Bool,
      e = dD.ofTorus (om300 n ![(a.toNat : ℤ), b.toNat, c.toNat]) := by
    intro e he heD
    obtain ⟨ε, hε, rfl⟩ := dD.t300_eq_om_of_mul_self hn1 heD (hinv e he)
    refine ⟨decide (ε 0 = 1), decide (ε 1 = 1), decide (ε 2 = 1), ?_⟩
    congr 2
    funext i
    fin_cases i <;> simp [bool_toNat_cast_eq (hε _)]
  have h8 : Nat.card (Bool × Bool × Bool) = 8 := by simp [Nat.card_eq_fintype_card]
  by_cases hD : ∃ e₀ ∈ E, e₀ ∉ D
  · obtain ⟨e₀, he₀, he₀D⟩ := hD
    obtain ⟨v₀, hv₀⟩ := dD.t300_mem_CSz_of_not_mem hn1 (hE he₀) he₀D
    have hfix : ∀ d ∈ E, d ∈ D → ∃ a b : Bool,
        d = dD.ofTorus (om300 n ![(a.toNat : ℤ), b.toNat, b.toNat]) := by
      intro d hd hdD
      obtain ⟨a, b, c, rfl⟩ := hD1 d hd hdD
      have hc := hcomm _ hd _ he₀
      rw [hv₀] at hc
      have hω := (dD.nf_commute_iff v₀ _ false false true).mp hc.symm
      simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
        AddMonoidHom.id_apply, t300_φu_om, om300_eq_iff hn1] at hω
      have h1 := hω 1
      have hbc : c = b := by
        revert h1
        cases a <;> cases b <;> cases c <;> decide
      exact ⟨a, b, by rw [hbc]⟩
    let f : Bool × Bool × Bool → G := fun w =>
      dD.ofTorus (om300 n ![(w.2.1.toNat : ℤ), w.2.2.toNat, w.2.2.toNat]) *
        (if w.1 then e₀ else 1)
    have hcov : ∀ e ∈ E, ∃ w, f w = e := by
      intro e he
      by_cases heD : e ∈ D
      · obtain ⟨a, b, hd⟩ := hfix e he heD
        exact ⟨(false, a, b), by simp [f, hd]⟩
      · obtain ⟨v, hv⟩ := dD.t300_mem_CSz_of_not_mem hn1 (hE he) heD
        have hmem : e * e₀⁻¹ ∈ D := by
          rw [hv, hv₀]
          exact dD.nf_u_mul_inv_mem v₀ v
        obtain ⟨a, b, hd⟩ := hfix (e * e₀⁻¹) (mul_mem he (inv_mem he₀)) hmem
        refine ⟨(true, a, b), ?_⟩
        simp only [f, if_true]
        rw [← hd, inv_mul_cancel_right]
    have hle := Stroth42Core.natCard_le_of_subset_range f hcov
    rw [hcard, h8] at hle
    omega
  · simp only [not_exists, not_and, not_not] at hD
    let f : Bool × Bool × Bool → G := fun w =>
      dD.ofTorus (om300 n ![(w.1.toNat : ℤ), w.2.1.toNat, w.2.2.toNat])
    have hcov : ∀ e ∈ E, ∃ w, f w = e := by
      intro e he
      obtain ⟨a, b, c, hd⟩ := hD1 e he (hD e he)
      exact ⟨(a, b, c), hd.symm⟩
    have hle := Stroth42Core.natCard_le_of_subset_range f hcov
    rw [hcard, h8] at hle
    omega

theorem t300_h9 (hn : 3 ≤ n) :
    ∀ X : Subgroup G, X ≤ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}) ⊓
      Subgroup.centralizer {(dD.c : G) ^ 2 ^ (n - 1)} → IsMulCommutative X →
        Nat.card X = Nat.card D → X = D := by
  intro X hX hab hcard
  have hn1 : 1 ≤ n := by omega
  have hDcard : Nat.card D = 2 ^ (n + n + n) := by
    rw [dD.card, t300_k, t300_k, t300_k]
  by_cases hD : ∃ x₀ ∈ X, x₀ ∉ D
  · exfalso
    obtain ⟨x₀, hx₀, hx₀D⟩ := hD
    obtain ⟨v₀, hv₀⟩ := dD.t300_mem_CSz_of_not_mem hn1 (hX hx₀) hx₀D
    have hcomm : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := fun a ha b hb =>
      congrArg Subtype.val (hab.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    haveI : NeZero (2 ^ n) := ⟨by positivity⟩
    have hfix : ∀ d ∈ X, d ∈ D → ∃ p q : ZMod (2 ^ n),
        d = dD.ofTorus (Torus.ofInt _ ![(p.val : ℤ), (q.val : ℤ), (q.val : ℤ)]) := by
      intro d hd hdD
      obtain ⟨v, rfl⟩ := dD.exists_ofTorus hdD
      have hc := hcomm _ hd _ hx₀
      rw [hv₀] at hc
      have hfv := (dD.nf_commute_iff v₀ v false false true).mp hc.symm
      simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
        AddMonoidHom.id_apply] at hfv
      obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
      rw [t300_φu, t300_ofInt_eq_iff] at hfv
      obtain ⟨-, h1, -⟩ := hfv
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at h1
      refine ⟨((x 0 : ℤ) : ZMod (2 ^ n)), ((x 1 : ℤ) : ZMod (2 ^ n)), ?_⟩
      congr 1
      rw [t300_ofInt_eq_iff]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, ZMod.val_intCast]
      have hm : ((2 ^ n : ℕ) : ℤ) = 2 ^ n := by push_cast; rfl
      rw [hm]
      refine ⟨⟨-(x 0 / 2 ^ n), by rw [Int.emod_def]; ring⟩, ⟨-(x 1 / 2 ^ n), by
        rw [Int.emod_def]; ring⟩, ?_⟩
      obtain ⟨c, hc⟩ := h1
      exact ⟨c - x 1 / 2 ^ n, by rw [Int.emod_def]; linear_combination hc⟩
    let f : Bool × ZMod (2 ^ n) × ZMod (2 ^ n) → G := fun w =>
      dD.ofTorus (Torus.ofInt _ ![(w.2.1.val : ℤ), (w.2.2.val : ℤ), (w.2.2.val : ℤ)]) *
        (if w.1 then x₀ else 1)
    have hcov : ∀ e ∈ X, ∃ w, f w = e := by
      intro e he
      by_cases heD : e ∈ D
      · obtain ⟨p, q, hd⟩ := hfix e he heD
        exact ⟨(false, p, q), by simp [f, hd]⟩
      · obtain ⟨v, hv⟩ := dD.t300_mem_CSz_of_not_mem hn1 (hX he) heD
        have hmem : e * x₀⁻¹ ∈ D := by
          rw [hv, hv₀]
          exact dD.nf_u_mul_inv_mem v₀ v
        obtain ⟨p, q, hd⟩ := hfix (e * x₀⁻¹) (mul_mem he (inv_mem hx₀)) hmem
        refine ⟨(true, p, q), ?_⟩
        simp only [f, if_true]
        rw [← hd, inv_mul_cancel_right]
    have hle := Stroth42Core.natCard_le_of_subset_range f hcov
    rw [hcard, hDcard, Nat.card_prod, Nat.card_prod, Nat.card_zmod] at hle
    have h2 : Nat.card Bool = 2 := by simp [Nat.card_eq_fintype_card]
    rw [h2, show 2 * (2 ^ n * 2 ^ n) = 2 ^ (n + n + 1) by ring] at hle
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
    omega
  · simp only [not_exists, not_and, not_not] at hD
    haveI : Finite D := Nat.finite_of_card_ne_zero (by rw [hDcard]; positivity)
    exact Subgroup.eq_of_le_of_card_ge (fun x hx => hD x hx) hcard.ge

end StrothWeakTypeData

end CFSG.CGT.Stroth77
