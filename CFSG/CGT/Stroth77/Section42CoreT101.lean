module

public import CFSG.CGT.Stroth77.Section42Core

public section

namespace CFSG.CGT.Stroth77

open Matrix

namespace Type101

theorem uvM_mulVec (s : ℕ) (x : Fin 3 → ℤ) :
    uvM s *ᵥ x = ![-3 * x 0 + 2 * x 1 + 2 * x 2,
      -2 * x 0 + x 1 + (4 * (2 ^ s) ^ 2 + 6 * 2 ^ s + 2) * x 2,
      -2 * x 0 + (2 * 2 ^ s + 2) * x 1 + x 2] := by
  funext i
  fin_cases i <;> simp [uvM, uvA, tM, ρM, ofCols_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three, -mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring

theorem tM_mulVec (s : ℕ) (x : Fin 3 → ℤ) :
    tM s *ᵥ x = ![x 0 + (-4 * 2 ^ s - 2) * x 2,
      2 * x 0 + (2 * 2 ^ s - 1) * x 1 + (-2 * 2 ^ s - 2) * x 2, (-2 * 2 ^ s - 1) * x 2] := by
  funext i
  fin_cases i <;> simp [uvA, tM, ρM, ofCols_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three, -mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring

theorem uM_mulVec (s : ℕ) (x : Fin 3 → ℤ) : uM s *ᵥ x = ![x 0, x 2, x 1] := by
  funext i
  fin_cases i <;> simp [uM, uMat, ofCols_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem ρM_mulVec (s : ℕ) (x : Fin 3 → ℤ) : ρM s *ᵥ x = ![x 0 - 2 * x 2, -x 2, x 1 - x 2] := by
  funext i
  fin_cases i <;> simp [ρM, ofCols_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

end Type101

namespace Stroth42Core

variable {s : ℕ}

theorem t101_φuv (x : Fin 3 → ℤ) :
    (StrothTypeIndex.t101 s).action.φuv (Torus.ofInt _ x) = Torus.ofInt _
      ![-3 * x 0 + 2 * x 1 + 2 * x 2, -2 * x 0 + x 1 + (4 * (2 ^ s) ^ 2 + 6 * 2 ^ s + 2) * x 2,
        -2 * x 0 + (2 * 2 ^ s + 2) * x 1 + x 2] := by
  have h := matAct_ofInt (k := (StrothTypeIndex.t101 s).k) (Type101.uvM s)
    (StrothTypeIndex.t101 s).action.compat_uv x
  rw [Type101.uvM_mulVec] at h
  exact h

theorem t101_φt (x : Fin 3 → ℤ) :
    (StrothTypeIndex.t101 s).action.φt (Torus.ofInt _ x) = Torus.ofInt _
      ![x 0 + (-4 * 2 ^ s - 2) * x 2, 2 * x 0 + (2 * 2 ^ s - 1) * x 1 + (-2 * 2 ^ s - 2) * x 2,
        (-2 * 2 ^ s - 1) * x 2] := by
  have h := matAct_ofInt (k := (StrothTypeIndex.t101 s).k) (Type101.tM s)
    (StrothTypeIndex.t101 s).action.compat_t x
  rw [Type101.tM_mulVec] at h
  exact h

theorem t101_φu (x : Fin 3 → ℤ) :
    (StrothTypeIndex.t101 s).action.φu (Torus.ofInt _ x) = Torus.ofInt _ ![x 0, x 2, x 1] := by
  have h := matAct_ofInt (k := (StrothTypeIndex.t101 s).k) (Type101.uM s)
    (StrothTypeIndex.t101 s).action.compat_u x
  rw [Type101.uM_mulVec] at h
  exact h

theorem t101_φρ (x : Fin 3 → ℤ) :
    (StrothTypeIndex.t101 s).action.φρ (Torus.ofInt _ x) =
      Torus.ofInt _ ![x 0 - 2 * x 2, -x 2, x 1 - x 2] := by
  have h := matAct_ofInt (k := (StrothTypeIndex.t101 s).k) (Type101.ρM s)
    (StrothTypeIndex.t101 s).action.compat_ρ x
  rw [Type101.ρM_mulVec] at h
  exact h

theorem t101_ofInt_eq_iff (x y : Fin 3 → ℤ) :
    Torus.ofInt (StrothTypeIndex.t101 s).k x = Torus.ofInt _ y ↔
      (2 : ℤ) ^ (s + 1) ∣ y 0 - x 0 ∧ (2 : ℤ) ^ (s + 2) ∣ y 1 - x 1 ∧
        (2 : ℤ) ^ (s + 2) ∣ y 2 - x 2 := by
  rw [Torus.ofInt_eq_ofInt_iff]
  constructor
  · intro h
    exact ⟨Int.modEq_iff_dvd.mp (h 0), Int.modEq_iff_dvd.mp (h 1), Int.modEq_iff_dvd.mp (h 2)⟩
  · rintro ⟨h0, h1, h2⟩ i
    fin_cases i
    · exact Int.modEq_iff_dvd.mpr h0
    · exact Int.modEq_iff_dvd.mpr h1
    · exact Int.modEq_iff_dvd.mpr h2

theorem t101_ofInt_eq_zero_iff (x : Fin 3 → ℤ) :
    Torus.ofInt (StrothTypeIndex.t101 s).k x = 0 ↔
      (2 : ℤ) ^ (s + 1) ∣ x 0 ∧ (2 : ℤ) ^ (s + 2) ∣ x 1 ∧ (2 : ℤ) ^ (s + 2) ∣ x 2 := by
  rw [← Torus.ofInt_zero, t101_ofInt_eq_iff]
  simp

@[expose] def om101 (s : ℕ) (ε : Fin 3 → ℤ) : Torus (StrothTypeIndex.t101 s).k :=
  Torus.ofInt _ (fun i => ε i * 2 ^ ((StrothTypeIndex.t101 s).k i - 1))

theorem t101_one_le_k (i : Fin 3) : 1 ≤ (StrothTypeIndex.t101 s).k i := by
  fin_cases i
  · show 1 ≤ s + 1; omega
  · show 1 ≤ s + 2; omega
  · show 1 ≤ s + 2; omega

theorem om101_eq_iff (ε ε' : Fin 3 → ℤ) :
    om101 s ε = om101 s ε' ↔ ∀ i, ε i ≡ ε' i [ZMOD 2] :=
  ofInt_mul_two_pow_pred_eq_iff t101_one_le_k ε ε'

theorem om101_zero : om101 s 0 = 0 := by
  rw [om101, ← Torus.ofInt_zero]
  congr 1
  funext i
  simp

theorem om101_add_self (ε : Fin 3 → ℤ) : om101 s ε + om101 s ε = 0 := by
  rw [om101, ← Torus.ofInt_add, ← om101_zero, om101]
  rw [show (fun i => ε i * 2 ^ ((StrothTypeIndex.t101 s).k i - 1)) +
      (fun i => ε i * 2 ^ ((StrothTypeIndex.t101 s).k i - 1)) =
      fun i => (2 * ε i) * 2 ^ ((StrothTypeIndex.t101 s).k i - 1) by funext i; simp; ring]
  exact (om101_eq_iff _ _).mpr fun i => by
    simp only [Pi.zero_apply]
    exact (Int.emod_emod_of_dvd _ (dvd_refl 2)).symm.trans (by simp)

theorem om101_eq_ofInt (ε : Fin 3 → ℤ) :
    om101 s ε = Torus.ofInt _ ![ε 0 * 2 ^ s, ε 1 * 2 ^ (s + 1), ε 2 * 2 ^ (s + 1)] := by
  rw [om101]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem om101_congr {ε ε' : Fin 3 → ℤ} (h0 : (2 : ℤ) ∣ ε' 0 - ε 0) (h1 : (2 : ℤ) ∣ ε' 1 - ε 1)
    (h2 : (2 : ℤ) ∣ ε' 2 - ε 2) : om101 s ε = om101 s ε' := by
  refine (om101_eq_iff _ _).mpr fun i => ?_
  fin_cases i
  · exact Int.modEq_iff_dvd.mpr h0
  · exact Int.modEq_iff_dvd.mpr h1
  · exact Int.modEq_iff_dvd.mpr h2

theorem t101_φuv_om (ε : Fin 3 → ℤ) :
    (StrothTypeIndex.t101 s).action.φuv (om101 s ε) = om101 s ![ε 0, ε 0 + ε 1, ε 0 + ε 2] := by
  rw [om101_eq_ofInt, t101_φuv]
  have h : Torus.ofInt (StrothTypeIndex.t101 s).k
      ![-3 * (![ε 0 * 2 ^ s, ε 1 * 2 ^ (s + 1), ε 2 * 2 ^ (s + 1)] : Fin 3 → ℤ) 0 +
          2 * ![ε 0 * 2 ^ s, ε 1 * 2 ^ (s + 1), ε 2 * 2 ^ (s + 1)] 1 +
          2 * ![ε 0 * 2 ^ s, ε 1 * 2 ^ (s + 1), ε 2 * 2 ^ (s + 1)] 2,
        -2 * ![ε 0 * 2 ^ s, ε 1 * 2 ^ (s + 1), ε 2 * 2 ^ (s + 1)] 0 +
          ![ε 0 * 2 ^ s, ε 1 * 2 ^ (s + 1), ε 2 * 2 ^ (s + 1)] 1 +
          (4 * (2 ^ s) ^ 2 + 6 * 2 ^ s + 2) *
            ![ε 0 * 2 ^ s, ε 1 * 2 ^ (s + 1), ε 2 * 2 ^ (s + 1)] 2,
        -2 * ![ε 0 * 2 ^ s, ε 1 * 2 ^ (s + 1), ε 2 * 2 ^ (s + 1)] 0 +
          (2 * 2 ^ s + 2) * ![ε 0 * 2 ^ s, ε 1 * 2 ^ (s + 1), ε 2 * 2 ^ (s + 1)] 1 +
          ![ε 0 * 2 ^ s, ε 1 * 2 ^ (s + 1), ε 2 * 2 ^ (s + 1)] 2] =
      om101 s ![-3 * ε 0 + 4 * ε 1 + 4 * ε 2, -ε 0 + ε 1 + (4 * (2 ^ s) ^ 2 + 6 * 2 ^ s + 2) * ε 2,
        -ε 0 + (2 * 2 ^ s + 2) * ε 1 + ε 2] := by
    rw [om101_eq_ofInt]
    congr 1
    funext i
    fin_cases i <;> simp <;> ring
  rw [h]
  refine om101_congr ?_ ?_ ?_ <;> simp
  · exact ⟨2 * ε 0 - 2 * ε 1 - 2 * ε 2, by ring⟩
  · exact ⟨ε 0 - (2 * (2 ^ s) ^ 2 + 3 * 2 ^ s + 1) * ε 2, by ring⟩
  · exact ⟨ε 0 - (2 ^ s + 1) * ε 1, by ring⟩

theorem t101_φt_om (ε : Fin 3 → ℤ) :
    (StrothTypeIndex.t101 s).action.φt (om101 s ε) = om101 s ![ε 0, ε 0 + ε 1, ε 2] := by
  rw [om101_eq_ofInt, t101_φt]
  have h : Torus.ofInt (StrothTypeIndex.t101 s).k
      ![(![ε 0 * 2 ^ s, ε 1 * 2 ^ (s + 1), ε 2 * 2 ^ (s + 1)] : Fin 3 → ℤ) 0 +
          (-4 * 2 ^ s - 2) * ![ε 0 * 2 ^ s, ε 1 * 2 ^ (s + 1), ε 2 * 2 ^ (s + 1)] 2,
        2 * ![ε 0 * 2 ^ s, ε 1 * 2 ^ (s + 1), ε 2 * 2 ^ (s + 1)] 0 +
          (2 * 2 ^ s - 1) * ![ε 0 * 2 ^ s, ε 1 * 2 ^ (s + 1), ε 2 * 2 ^ (s + 1)] 1 +
          (-2 * 2 ^ s - 2) * ![ε 0 * 2 ^ s, ε 1 * 2 ^ (s + 1), ε 2 * 2 ^ (s + 1)] 2,
        (-2 * 2 ^ s - 1) * ![ε 0 * 2 ^ s, ε 1 * 2 ^ (s + 1), ε 2 * 2 ^ (s + 1)] 2] =
      om101 s ![ε 0 + (-8 * 2 ^ s - 4) * ε 2, ε 0 + (2 * 2 ^ s - 1) * ε 1 + (-2 * 2 ^ s - 2) * ε 2,
        (-2 * 2 ^ s - 1) * ε 2] := by
    rw [om101_eq_ofInt]
    congr 1
    funext i
    fin_cases i <;> simp <;> ring
  rw [h]
  refine om101_congr ?_ ?_ ?_ <;> simp
  · exact ⟨-((4 * 2 ^ s + 2) * ε 2), by ring⟩
  · exact ⟨(1 - 2 ^ s) * ε 1 + (2 ^ s + 1) * ε 2, by ring⟩
  · exact ⟨(2 ^ s + 1) * ε 2, by ring⟩

theorem t101_φu_om (ε : Fin 3 → ℤ) :
    (StrothTypeIndex.t101 s).action.φu (om101 s ε) = om101 s ![ε 0, ε 2, ε 1] := by
  rw [om101, t101_φu, om101]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem t101_φρ_om (ε : Fin 3 → ℤ) :
    (StrothTypeIndex.t101 s).action.φρ (om101 s ε) = om101 s ![ε 0 - 4 * ε 2, -ε 2, ε 1 - ε 2] := by
  rw [om101_eq_ofInt, t101_φρ, om101_eq_ofInt]
  congr 1
  funext i
  fin_cases i <;> simp <;> ring

theorem t101_faithful (i j l : Bool)
    (h : ∀ v, (StrothTypeIndex.t101 s).action.d8Act i j l v = v) :
    i = false ∧ j = false ∧ l = false := by
  have hc := h (om101 s ![1, 0, 0])
  have ha := h (om101 s ![0, 1, 0])
  cases i <;> cases j <;> cases l <;>
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte,
      AddMonoidHom.comp_apply, AddMonoidHom.id_apply, t101_φuv_om, t101_φt_om,
      t101_φu_om, om101_eq_iff] at hc ha <;>
    first
    | exact ⟨rfl, rfl, rfl⟩
    | exact absurd hc (by decide)
    | exact absurd ha (by decide)

theorem t101_parity (i j l : Bool) (v : Torus (StrothTypeIndex.t101 s).k) :
    Even (((StrothTypeIndex.t101 s).action.d8Act i j l v) 0) ↔ Even (v 0) := by
  have hk : 1 ≤ (StrothTypeIndex.t101 s).k 0 := t101_one_le_k 0
  refine SigmaFourAction.even_d8Act_zero_iff _ ?_ ?_ ?_ i j l v
  · refine even_matAct_zero_iff hk (Type101.uvM s) (Type101.compat_uv s) ⟨-2, ?_⟩ ⟨1, ?_⟩
      ⟨1, ?_⟩ <;>
      simp [Type101.uvM, Type101.uvA, Type101.tM, Type101.ρM, ofCols_apply, Matrix.mulVec,
        dotProduct, Fin.sum_univ_three, -mul_eq_zero, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff] <;> ring
  · refine even_matAct_zero_iff hk (Type101.tM s) (Type101.compat_t s) ?_ ?_ ?_ <;>
      simp [Type101.uvA, Type101.tM, Type101.ρM, ofCols_apply, Matrix.mulVec, dotProduct,
        Fin.sum_univ_three, -mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    exact ⟨-2 * 2 ^ s - 1, by ring⟩
  · refine even_matAct_zero_iff hk (Type101.uM s) (Type101.compat_u s) ?_ ?_ ?_ <;>
      simp [Type101.uM, uMat, ofCols_apply]

end Stroth42Core

open Stroth42Core

namespace StrothWeakTypeData

variable {G : Type*} [Group G] {D : Subgroup G} {s : ℕ}
  (dD : StrothWeakTypeData D (.t101 s))

theorem t101_c_pow : (dD.c : G) ^ 2 ^ s = dD.ofTorus (om101 s ![1, 0, 0]) := by
  rw [c_eq, ← ofTorus_nsmul]
  congr 1
  funext i
  fin_cases i <;> simp [om101, gen, Pi.single_apply] <;> rfl

theorem t101_a_pow : (dD.a : G) ^ 2 ^ (s + 1) = dD.ofTorus (om101 s ![0, 1, 0]) := by
  rw [a_eq, ← ofTorus_nsmul]
  congr 1
  funext i
  fin_cases i <;> simp [om101, gen, Pi.single_apply] <;> rfl

theorem t101_eq_om_of_mul_self {y : G} (hy : y ∈ D) (h2 : y * y = 1) :
    ∃ ε : Fin 3 → ℤ, (∀ i, ε i = 0 ∨ ε i = 1) ∧ y = dD.ofTorus (om101 s ε) := by
  obtain ⟨v, rfl⟩ := dD.exists_ofTorus hy
  rw [ofTorus_mul_self, ofTorus_eq_one_iff] at h2
  have h2' : (2 : ℤ) • v = 0 := by rw [two_zsmul]; exact h2
  obtain ⟨ε, hε, rfl⟩ := (Torus.two_zsmul_eq_zero_iff t101_one_le_k v).mp h2'
  exact ⟨ε, hε, rfl⟩

theorem t101_h1 :
    (Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u}).relIndex
      (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}) = 2 :=
  dD.relIndex_S₁ (t101_one_le_k 0) t101_faithful t101_parity

theorem t101_h2 :
    (dD.c : G) ∉
      Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u} :=
  dD.c_not_mem_S₁ (t101_one_le_k 0) t101_faithful t101_parity

theorem t101_h3 :
    ∀ y ∈ D, y * y = 1 → y ≠ 1 →
      (∃ p ∈ Subgroup.closure {dD.uv, dD.t, dD.u}, p⁻¹ * y * p = (dD.c : G) ^ 2 ^ s) ∨
        ∃ g ∈ dD.L, g⁻¹ * y * g = (dD.a : G) ^ 2 ^ (s + 1) := by
  intro y hy h2 h1
  obtain ⟨ε, hε, rfl⟩ := dD.t101_eq_om_of_mul_self hy h2
  rw [dD.t101_c_pow, dD.t101_a_pow]
  have hW : ∀ x ∈ ({dD.uv, dD.t, dD.u} : Set G), x ∈ Subgroup.closure {dD.uv, dD.t, dD.u} :=
    fun x hx => Subgroup.subset_closure hx
  have hconj_uv := dD.conj_ofTorus dD.uv_mem dD.uv_conj
  have hconj_t := dD.conj_ofTorus dD.t_mem dD.t_conj
  have hconj_ρ := dD.conj_ofTorus dD.ρ_mem dD.ρ_conj
  have hε0 : ¬ (ε 0 = 0 ∧ ε 1 = 0 ∧ ε 2 = 0) := by
    rintro ⟨h0, h1', h2'⟩
    apply h1
    rw [← dD.ofTorus_zero, ← om101_zero]
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
    rw [mul_inv_rev, show (dD.ρ⁻¹ * dD.ρ⁻¹ * dD.ofTorus (om101 s ![0, 0, 1]) * (dD.ρ * dD.ρ)) =
      dD.ρ⁻¹ * (dD.ρ⁻¹ * dD.ofTorus (om101 s ![0, 0, 1]) * dD.ρ) * dD.ρ by group, hconj_ρ,
      hconj_ρ, t101_φρ_om, t101_φρ_om]
    exact congrArg dD.ofTorus ((om101_eq_iff _ _).mpr (by decide))
  ·
    right
    exact ⟨1, one_mem _, by simp⟩
  ·
    right
    refine ⟨dD.ρ, dD.ρ_mem_L, ?_⟩
    rw [hconj_ρ, t101_φρ_om]
    exact congrArg dD.ofTorus ((om101_eq_iff _ _).mpr (by decide))
  ·
    left
    exact ⟨1, one_mem _, by simp⟩
  ·
    left
    refine ⟨dD.uv * dD.t, mul_mem (hW _ (by simp)) (hW _ (by simp)), ?_⟩
    rw [mul_inv_rev, show dD.t⁻¹ * dD.uv⁻¹ * dD.ofTorus (om101 s ![1, 0, 1]) * (dD.uv * dD.t) =
      dD.t⁻¹ * (dD.uv⁻¹ * dD.ofTorus (om101 s ![1, 0, 1]) * dD.uv) * dD.t by group, hconj_uv,
      hconj_t, t101_φuv_om, t101_φt_om]
    exact congrArg dD.ofTorus ((om101_eq_iff _ _).mpr (by decide))
  ·
    left
    refine ⟨dD.t, hW _ (by simp), ?_⟩
    rw [hconj_t, t101_φt_om]
    exact congrArg dD.ofTorus ((om101_eq_iff _ _).mpr (by decide))
  ·
    left
    refine ⟨dD.uv, hW _ (by simp), ?_⟩
    rw [hconj_uv, t101_φuv_om]
    exact congrArg dD.ofTorus ((om101_eq_iff _ _).mpr (by decide))

theorem t101_comm_z {v : Torus (StrothTypeIndex.t101 s).k} {i j l : Bool}
    (h : dD.ofTorus v * dD.d8 i j l * (dD.c : G) ^ 2 ^ s =
      (dD.c : G) ^ 2 ^ s * (dD.ofTorus v * dD.d8 i j l)) : i = false ∧ j = false := by
  rw [dD.t101_c_pow, nf_commute_iff] at h
  cases i <;> cases j <;> cases l <;>
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, t101_φuv_om, t101_φt_om, t101_φu_om, om101_eq_iff] at h <;>
    first
    | exact ⟨rfl, rfl⟩
    | exact absurd h (by decide)

theorem t101_d8Act_u (l : Bool) (x : Fin 3 → ℤ) :
    (StrothTypeIndex.t101 s).action.d8Act false false l (Torus.ofInt _ x) =
      Torus.ofInt _ ![x 0, if l then x 2 else x 1, if l then x 1 else x 2] := by
  cases l <;> simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte,
    AddMonoidHom.comp_apply, AddMonoidHom.id_apply, t101_φu]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem t101_not_dvd (hs : 1 ≤ s) (r : ℤ) :
    ¬ (2 : ℤ) ^ (s + 1) ∣ 1 * 2 ^ s - 2 ^ (s - 1) * (r + r + (r + r)) := by
  have h := not_two_pow_dvd_aux (n := s + 1) (by omega) r
  rwa [show s + 1 - 1 = s by omega] at h

theorem t101_h4 (hs : 1 ≤ s) :
    ∀ y ∈ Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u},
      y * (dD.c : G) ^ 2 ^ s = (dD.c : G) ^ 2 ^ s * y → y ^ 2 ^ s ≠ (dD.c : G) ^ 2 ^ s := by
  intro y hy hcomm hpow
  have hk : 1 ≤ (StrothTypeIndex.t101 s).k 0 := t101_one_le_k 0
  obtain ⟨v, i, j, l, hv, rfl⟩ := (dD.mem_S₁_iff hk t101_parity).mp hy
  obtain ⟨rfl, rfl⟩ := dD.t101_comm_z hcomm
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
  rw [Torus.ofInt_apply, even_intCast_iff hk] at hv
  obtain ⟨r, hr⟩ := hv
  have hd8 : dD.d8 (l && false) false false = 1 := by rw [Bool.and_false, d8_fff]
  rw [pow_two_pow_eq_mul_self _ hs, nf_mul_self, hd8, mul_one, ← ofTorus_nsmul,
    dD.t101_c_pow] at hpow
  have hpow' := dD.ofTorus_inj hpow
  rw [t101_d8Act_u, ← Torus.ofInt_add, ← natCast_zsmul, ← Torus.ofInt_zsmul, om101_eq_ofInt,
    t101_ofInt_eq_iff] at hpow'
  obtain ⟨h0, -, -⟩ := hpow'
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero] at h0
  rw [hr] at h0
  exact t101_not_dvd hs r (by push_cast at h0; exact h0)

theorem t101_odd_of_not_mem {x : Fin 3 → ℤ} {i j l : Bool}
    (hy1 : dD.ofTorus (Torus.ofInt _ x) * dD.d8 i j l ∉
      Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u}) :
    x 0 % 2 = 1 := by
  have hk : 1 ≤ (StrothTypeIndex.t101 s).k 0 := t101_one_le_k 0
  have hv : ¬ Even ((Torus.ofInt (StrothTypeIndex.t101 s).k x) 0) := fun h =>
    hy1 ((dD.mem_S₁_iff hk t101_parity).mpr ⟨_, i, j, l, h, rfl⟩)
  rw [Torus.ofInt_apply, even_intCast_iff hk, Int.not_even_iff] at hv
  exact hv

end StrothWeakTypeData

namespace Stroth42Core

variable {s : ℕ}

private theorem two_dvd_of_two_pow_succ_succ_dvd {e : ℤ} (h : (2 : ℤ) ^ (s + 2) ∣ 2 ^ (s + 1) * e) :
    2 ∣ e := by
  rw [show (2 : ℤ) ^ (s + 2) = 2 ^ (s + 1) * 2 by ring] at h
  exact (mul_dvd_mul_iff_left (pow_ne_zero _ two_ne_zero)).mp h

theorem t101_add_d8Act_ne_zero (hs : 1 ≤ s) {x : Fin 3 → ℤ} (hx : x 0 % 2 = 1) (i j l : Bool)
    (hlj : (l && j) = false) :
    Torus.ofInt (StrothTypeIndex.t101 s).k x +
      (StrothTypeIndex.t101 s).action.d8Act i j l (Torus.ofInt _ x) ≠ 0 := by
  have h4 : ∀ {e : ℤ}, (2 : ℤ) ^ (s + 1) ∣ e → 4 ∣ e := fun h =>
    two_pow_dvd_four (n := s + 1) (by omega) h
  have h2 : ∀ {e : ℤ}, (2 : ℤ) ^ (s + 2) ∣ e → 2 ∣ e := fun h =>
    (dvd_pow_self 2 (by omega : s + 2 ≠ 0)).trans h
  cases i <;> cases j <;> cases l <;> simp at hlj <;>
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, t101_φuv, t101_φt, t101_φu, ← Torus.ofInt_add, Ne,
      t101_ofInt_eq_zero_iff] <;>
    rintro ⟨d0, d1, d2⟩ <;>
    simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at d0 d1 d2
  ·
    have := h4 d0
    omega
  ·
    have := h4 d0
    omega
  ·
    have hx2 : (2 : ℤ) ∣ -x 2 :=
      two_dvd_of_two_pow_succ_succ_dvd (by convert d2 using 1; ring)
    have hc : (4 : ℤ) ∣ 2 * x 0 - 2 * x 2 := by
      have e : 2 * x 0 - 2 * x 2 =
          (x 0 + (x 0 + (-4 * 2 ^ s - 2) * x 2)) + 4 * (2 ^ s * x 2) := by ring
      rw [e]
      exact dvd_add (h4 d0) (dvd_mul_right _ _)
    omega
  ·
    obtain ⟨k0, hk0⟩ := d0
    have h1' : (2 : ℤ) ∣ k0 + (2 * 2 ^ s + 3) * x 2 :=
      two_dvd_of_two_pow_succ_succ_dvd (by convert d1 using 1; linear_combination -hk0)
    have h2' : (2 : ℤ) ∣ k0 + x 1 :=
      two_dvd_of_two_pow_succ_succ_dvd (by convert d2 using 1; linear_combination -hk0)
    have h1'' : (2 : ℤ) ∣ k0 + x 2 := by
      have e : k0 + x 2 = (k0 + (2 * 2 ^ s + 3) * x 2) - 2 * ((2 ^ s + 1) * x 2) := by ring
      rw [e]
      exact dvd_sub h1' (dvd_mul_right _ _)
    have h0' : (2 : ℤ) ∣ -x 0 + x 1 + x 2 := by
      obtain ⟨q, hq⟩ : ∃ q : ℤ, (2 : ℤ) ^ s = 2 * q :=
        ⟨2 ^ (s - 1), by rw [← pow_succ']; congr 1; omega⟩
      have hpow : (2 : ℤ) ^ (s + 1) = 2 * 2 ^ s := by ring
      refine ⟨q * k0, mul_left_cancel₀ (two_ne_zero : (2 : ℤ) ≠ 0) ?_⟩
      linear_combination hk0 + k0 * hpow + 2 * k0 * hq
    omega
  ·
    have hd1 := h2 d1
    have h12 : (2 : ℤ) ∣ x 1 + x 2 := by
      have e : x 1 + x 2 = (x 1 + (-2 * x 0 + x 2 + (4 * (2 ^ s) ^ 2 + 6 * 2 ^ s + 2) * x 1)) -
          2 * (-x 0 + (2 * (2 ^ s) ^ 2 + 3 * 2 ^ s + 1) * x 1) := by ring
      rw [e]
      exact dvd_sub hd1 (dvd_mul_right _ _)
    have := h4 d0
    omega
  ·
    have hx1 : (2 : ℤ) ∣ x 1 - (4 * (2 ^ s) ^ 2 + 8 * 2 ^ s + 2) * x 2 :=
      two_dvd_of_two_pow_succ_succ_dvd (by convert d1 using 1; ring)
    have hx1' : (2 : ℤ) ∣ x 1 := by
      have e : x 1 = (x 1 - (4 * (2 ^ s) ^ 2 + 8 * 2 ^ s + 2) * x 2) +
          2 * ((2 * (2 ^ s) ^ 2 + 4 * 2 ^ s + 1) * x 2) := by ring
      rw [e]
      exact dvd_add hx1 (dvd_mul_right _ _)
    have hc : (4 : ℤ) ∣ 2 * x 0 - 2 * x 1 := by
      have e : 2 * x 0 - 2 * x 1 = (x 0 + (-3 * (x 0 + (-4 * 2 ^ s - 2) * x 2) +
          2 * (2 * x 0 + (2 * 2 ^ s - 1) * x 1 + (-2 * 2 ^ s - 2) * x 2) +
          2 * ((-2 * 2 ^ s - 1) * x 2))) - 4 * (2 ^ s * x 1 + 2 ^ s * x 2) := by ring
      rw [e]
      exact dvd_sub (h4 d0) (dvd_mul_right _ _)
    omega

end Stroth42Core

open Stroth42Core

namespace StrothWeakTypeData

variable {G : Type*} [Group G] {D : Subgroup G} {s : ℕ}
  (dD : StrothWeakTypeData D (.t101 s))

theorem t101_mul_self_ne_one (hs : 1 ≤ s) :
    ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u},
      y ∉ Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u} →
      y * y ≠ 1 := by
  intro y hy hy1 hyy
  obtain ⟨v, i, j, l, rfl⟩ := dD.mem_sup_iff.mp hy
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
  have hodd := dD.t101_odd_of_not_mem hy1
  rw [nf_mul_self] at hyy
  cases hlj : (l && j)
  · rw [hlj, d8_fff, mul_one, ofTorus_eq_one_iff] at hyy
    exact t101_add_d8Act_ne_zero hs hodd i j l hlj hyy
  · rw [hlj, d8_tff] at hyy
    have hnot := dD.d8_not_mem t101_faithful (i := true) (j := false) (l := false)
      (by decide) (Torus.ofInt (StrothTypeIndex.t101 s).k x +
        (StrothTypeIndex.t101 s).action.d8Act i j l (Torus.ofInt _ x))
    rw [d8_tff, hyy] at hnot
    exact hnot (one_mem _)

theorem t101_h6' (hs : 1 ≤ s) :
    ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u},
      y ∉ Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u} →
      y * y = 1 → ∃ E : Subgroup G,
        E ≤ Subgroup.centralizer {y} ∧ (∀ e ∈ E, e * e = 1) ∧ Nat.card E = 16 :=
  fun y hy hy1 hyy => absurd hyy (dD.t101_mul_self_ne_one hs y hy hy1)

theorem t101_h8 (hs : 1 ≤ s) :
    ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u},
      y ∉ Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u} →
      ∀ l : ℕ, 1 ≤ l → y ^ 2 ^ l = (dD.c : G) ^ 2 ^ s → y ^ 2 ^ s ≠ 1 := by
  intro y hy hy1 m _ hz hone
  obtain ⟨v, i, j, l, rfl⟩ := dD.mem_sup_iff.mp hy
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
  have hodd := dD.t101_odd_of_not_mem hy1
  have hc : dD.ofTorus (Torus.ofInt _ x) * dD.d8 i j l * (dD.c : G) ^ 2 ^ s =
      (dD.c : G) ^ 2 ^ s * (dD.ofTorus (Torus.ofInt _ x) * dD.d8 i j l) := by
    rw [← hz]
    exact (Commute.self_pow _ _).eq
  obtain ⟨rfl, rfl⟩ := dD.t101_comm_z hc
  have hd8 : dD.d8 (l && false) false false = 1 := by rw [Bool.and_false, d8_fff]
  rw [pow_two_pow_eq_mul_self _ hs, nf_mul_self, hd8, mul_one, ← ofTorus_nsmul,
    ofTorus_eq_one_iff, t101_d8Act_u, ← Torus.ofInt_add, ← natCast_zsmul, ← Torus.ofInt_zsmul,
    t101_ofInt_eq_zero_iff] at hone
  obtain ⟨h0, -, -⟩ := hone
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero] at h0
  push_cast at h0
  have h0' : (2 : ℤ) ^ s * 2 ∣ 2 ^ s * x 0 := by
    convert h0 using 1
    · ring
    · rw [show (2 : ℤ) ^ s = 2 ^ (s - 1) * 2 by rw [← pow_succ]; congr 1; omega]
      ring
  have h2 := (mul_dvd_mul_iff_left (pow_ne_zero s (two_ne_zero : (2 : ℤ) ≠ 0))).mp h0'
  omega

theorem t101_om_comm {v : Torus (StrothTypeIndex.t101 s).k} {i j l : Bool} {ε : Fin 3 → ℤ}
    (h : (StrothTypeIndex.t101 s).action.d8Act i j l (om101 s ε) = om101 s ε) :
    dD.ofTorus (om101 s ε) * (dD.ofTorus v * dD.d8 i j l) =
      dD.ofTorus v * dD.d8 i j l * dD.ofTorus (om101 s ε) :=
  ((dD.nf_commute_iff v (om101 s ε) i j l).mpr h).symm

theorem t101_h6 (hs : 1 ≤ s) :
    ∀ y : G, y * dD.uv ∈ D → y * y = 1 → ∃ E : Subgroup G,
      E ≤ Subgroup.centralizer {y} ∧ (∀ e ∈ E, e * e = 1) ∧ Nat.card E = 16 := by
  intro y hy hyy
  have hF := t101_faithful (s := s)
  obtain ⟨v, hv⟩ := dD.exists_ofTorus hy
  have hyv : y = dD.ofTorus v * dD.d8 true false false := by
    rw [d8_tff, ← hv, mul_assoc, dD.uv_sq, mul_one]
  subst hyv
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
  have hsq := hyy
  rw [nf_mul_self, Bool.and_false, d8_fff, mul_one, ofTorus_eq_one_iff] at hsq
  simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
    AddMonoidHom.id_apply, t101_φuv] at hsq
  rw [← Torus.ofInt_add, t101_ofInt_eq_zero_iff] at hsq
  obtain ⟨-, ⟨c1, hc1⟩, ⟨c2, hc2⟩⟩ := hsq
  simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at hc1 hc2
  have hx1 : -x 1 + (2 * 2 ^ s + 3) * x 2 = 2 * (c1 - c2) :=
    mul_left_cancel₀ (show (2 * 2 ^ s : ℤ) ≠ 0 by positivity) (by linear_combination hc1 - hc2)
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  set w : Fin 3 → ℤ := ![2 ^ (s' + 1) * x 2, (2 ^ (s' + 1) - 1) * x 2, 0] with hw
  have h34 : dD.ofTorus (Torus.ofInt _ x) * dD.d8 true false false *
      (dD.ofTorus (Torus.ofInt _ w) * dD.d8 false true false) =
      dD.ofTorus (Torus.ofInt _ w) * dD.d8 false true false *
        (dD.ofTorus (Torus.ofInt _ x) * dD.d8 true false false) := by
    rw [nf_mul_nf, nf_mul_nf]
    congr 1
    congr 1
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, t101_φuv, t101_φt, ← Torus.ofInt_add]
    rw [t101_ofInt_eq_iff]
    simp only [hw, Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    refine ⟨⟨-x 2, by ring⟩, ⟨(2 * 2 ^ (s' + 1) + 3) * x 2 - 2 * c1 + c2, ?_⟩,
      ⟨-(2 ^ s' * x 2), by ring⟩⟩
    linear_combination (-1 : ℤ) * hc1 + (-(2 * 2 ^ (s' + 1))) * hx1
  refine Stroth42Core.exists_E16 (H := D) (x₁ := dD.ofTorus (om101 (s' + 1) ![0, 1, 0]))
    (x₂ := dD.ofTorus (om101 (s' + 1) ![0, 0, 1]))
    (y₃ := dD.ofTorus (Torus.ofInt _ x) * dD.d8 true false false)
    (y₄ := dD.ofTorus (Torus.ofInt _ w) * dD.d8 false true false)
    (dD.ofTorus_mem _) (dD.ofTorus_mem _) ?_ ?_ hyy ?_ (dD.ofTorus_comm _ _) ?_ ?_ ?_ ?_ h34
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl h34.symm
  · rw [ofTorus_mul_self, om101_add_self, ofTorus_zero]
  · rw [ofTorus_mul_self, om101_add_self, ofTorus_zero]
  · rw [nf_mul_self, Bool.and_true, d8_fff, mul_one, ofTorus_eq_one_iff]
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, t101_φt, ← Torus.ofInt_add]
    rw [t101_ofInt_eq_zero_iff]
    simp only [hw, Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    exact ⟨⟨x 2, by ring⟩, ⟨2 ^ s' * x 2, by ring⟩, ⟨0, by ring⟩⟩
  · refine dD.t101_om_comm ?_
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, t101_φuv_om]
    exact (om101_eq_iff _ _).mpr (by decide)
  · refine dD.t101_om_comm ?_
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, t101_φt_om]
    exact (om101_eq_iff _ _).mpr (by decide)
  · refine dD.t101_om_comm ?_
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, t101_φuv_om]
    exact (om101_eq_iff _ _).mpr (by decide)
  · refine dD.t101_om_comm ?_
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, t101_φt_om]
    exact (om101_eq_iff _ _).mpr (by decide)
  · rw [Ne, ofTorus_eq_one_iff, ← om101_zero, om101_eq_iff]
    decide
  · rw [Ne, ofTorus_eq_one_iff, ← om101_zero, om101_eq_iff]
    decide
  · rw [Ne, dD.ofTorus_inj.eq_iff, om101_eq_iff]
    decide
  · exact dD.d8_not_mem hF (by decide) _
  · exact dD.d8_not_mem hF (by decide) _
  · rw [nf_mul_nf]
    exact dD.d8_not_mem hF (by decide) _
  · refine dD.t101_om_comm ?_
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, t101_φuv_om]
    exact (om101_eq_iff _ _).mpr (by decide)
  · refine dD.t101_om_comm ?_
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, t101_φuv_om]
    exact (om101_eq_iff _ _).mpr (by decide)

theorem t101_mem_CSz {y : G}
    (hy : y ∈ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}) ⊓
      Subgroup.centralizer {(dD.c : G) ^ 2 ^ s}) :
    ∃ (v : Torus (StrothTypeIndex.t101 s).k) (l : Bool),
      y = dD.ofTorus v * dD.d8 false false l := by
  obtain ⟨hyS, hyC⟩ := Subgroup.mem_inf.mp hy
  obtain ⟨v, i, j, l, rfl⟩ := dD.mem_sup_iff.mp hyS
  rw [Subgroup.mem_centralizer_iff] at hyC
  have hc := hyC _ (Set.mem_singleton _)
  obtain ⟨rfl, rfl⟩ := dD.t101_comm_z hc.symm
  exact ⟨v, l, rfl⟩

theorem t101_mem_CSz_of_not_mem {y : G}
    (hy : y ∈ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}) ⊓
      Subgroup.centralizer {(dD.c : G) ^ 2 ^ s}) (hyD : y ∉ D) :
    ∃ v : Torus (StrothTypeIndex.t101 s).k, y = dD.ofTorus v * dD.d8 false false true := by
  obtain ⟨v, l, rfl⟩ := dD.t101_mem_CSz hy
  cases l
  · exact absurd (by rw [d8_fff, mul_one]; exact dD.ofTorus_mem v) hyD
  · exact ⟨v, rfl⟩

theorem t101_h7 :
    ∀ E : Subgroup G, E ≤ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}) ⊓
      Subgroup.centralizer {(dD.c : G) ^ 2 ^ s} → (∀ e ∈ E, e * e = 1) → Nat.card E ≠ 16 := by
  intro E hE hinv hcard
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    have h1 := inv_eq_of_mul_eq_one_right (hinv a ha)
    have h2 := inv_eq_of_mul_eq_one_right (hinv b hb)
    have h3 := inv_eq_of_mul_eq_one_right (hinv _ (mul_mem ha hb))
    calc a * b = (a * b)⁻¹ := h3.symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [h1, h2]
  have hD1 : ∀ e ∈ E, e ∈ D → ∃ a b c : Bool,
      e = dD.ofTorus (om101 s ![(a.toNat : ℤ), b.toNat, c.toNat]) := by
    intro e he heD
    obtain ⟨ε, hε, rfl⟩ := dD.t101_eq_om_of_mul_self heD (hinv e he)
    refine ⟨decide (ε 0 = 1), decide (ε 1 = 1), decide (ε 2 = 1), ?_⟩
    congr 2
    funext i
    fin_cases i <;> simp [bool_toNat_cast_eq (hε _)]
  have h8 : Nat.card (Bool × Bool × Bool) = 8 := by simp [Nat.card_eq_fintype_card]
  by_cases hD : ∃ e₀ ∈ E, e₀ ∉ D
  · obtain ⟨e₀, he₀, he₀D⟩ := hD
    obtain ⟨v₀, hv₀⟩ := dD.t101_mem_CSz_of_not_mem (hE he₀) he₀D
    have hfix : ∀ d ∈ E, d ∈ D → ∃ a b : Bool,
        d = dD.ofTorus (om101 s ![(a.toNat : ℤ), b.toNat, b.toNat]) := by
      intro d hd hdD
      obtain ⟨a, b, c, rfl⟩ := hD1 d hd hdD
      have hc := hcomm _ hd _ he₀
      rw [hv₀] at hc
      have hω := (dD.nf_commute_iff v₀ _ false false true).mp hc.symm
      simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
        AddMonoidHom.id_apply, t101_φu_om, om101_eq_iff] at hω
      have h1 := hω 1
      have hbc : c = b := by
        revert h1
        cases a <;> cases b <;> cases c <;> decide
      exact ⟨a, b, by rw [hbc]⟩
    let f : Bool × Bool × Bool → G := fun w =>
      dD.ofTorus (om101 s ![(w.2.1.toNat : ℤ), w.2.2.toNat, w.2.2.toNat]) *
        (if w.1 then e₀ else 1)
    have hcov : ∀ e ∈ E, ∃ w, f w = e := by
      intro e he
      by_cases heD : e ∈ D
      · obtain ⟨a, b, hd⟩ := hfix e he heD
        exact ⟨(false, a, b), by simp [f, hd]⟩
      · obtain ⟨v, hv⟩ := dD.t101_mem_CSz_of_not_mem (hE he) heD
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
      dD.ofTorus (om101 s ![(w.1.toNat : ℤ), w.2.1.toNat, w.2.2.toNat])
    have hcov : ∀ e ∈ E, ∃ w, f w = e := by
      intro e he
      obtain ⟨a, b, c, hd⟩ := hD1 e he (hD e he)
      exact ⟨(a, b, c), hd.symm⟩
    have hle := Stroth42Core.natCard_le_of_subset_range f hcov
    rw [hcard, h8] at hle
    omega

theorem t101_h9 :
    ∀ X : Subgroup G, X ≤ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}) ⊓
      Subgroup.centralizer {(dD.c : G) ^ 2 ^ s} → IsMulCommutative X →
        Nat.card X = Nat.card D → X = D := by
  intro X hX hab hcard
  have hDcard : Nat.card D = 2 ^ ((s + 1) + (s + 2) + (s + 2)) := by
    rw [dD.card]
    rfl
  by_cases hD : ∃ x₀ ∈ X, x₀ ∉ D
  · exfalso
    obtain ⟨x₀, hx₀, hx₀D⟩ := hD
    obtain ⟨v₀, hv₀⟩ := dD.t101_mem_CSz_of_not_mem (hX hx₀) hx₀D
    have hcomm : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := fun a ha b hb =>
      congrArg Subtype.val (hab.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    haveI : NeZero (2 ^ (s + 1)) := ⟨by positivity⟩
    haveI : NeZero (2 ^ (s + 2)) := ⟨by positivity⟩
    have hfix : ∀ d ∈ X, d ∈ D → ∃ (p : ZMod (2 ^ (s + 1))) (q : ZMod (2 ^ (s + 2))),
        d = dD.ofTorus (Torus.ofInt _ ![(p.val : ℤ), (q.val : ℤ), (q.val : ℤ)]) := by
      intro d hd hdD
      obtain ⟨v, rfl⟩ := dD.exists_ofTorus hdD
      have hc := hcomm _ hd _ hx₀
      rw [hv₀] at hc
      have hfv := (dD.nf_commute_iff v₀ v false false true).mp hc.symm
      simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
        AddMonoidHom.id_apply] at hfv
      obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
      rw [t101_φu, t101_ofInt_eq_iff] at hfv
      obtain ⟨-, h1, -⟩ := hfv
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at h1
      refine ⟨((x 0 : ℤ) : ZMod (2 ^ (s + 1))), ((x 1 : ℤ) : ZMod (2 ^ (s + 2))), ?_⟩
      congr 1
      rw [t101_ofInt_eq_iff]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, ZMod.val_intCast]
      have hm1 : ((2 ^ (s + 1) : ℕ) : ℤ) = 2 ^ (s + 1) := by push_cast; rfl
      have hm2 : ((2 ^ (s + 2) : ℕ) : ℤ) = 2 ^ (s + 2) := by push_cast; rfl
      rw [hm1, hm2]
      refine ⟨⟨-(x 0 / 2 ^ (s + 1)), by rw [Int.emod_def]; ring⟩, ⟨-(x 1 / 2 ^ (s + 2)), by
        rw [Int.emod_def]; ring⟩, ?_⟩
      obtain ⟨c, hc⟩ := h1
      exact ⟨c - x 1 / 2 ^ (s + 2), by rw [Int.emod_def]; linear_combination hc⟩
    let f : Bool × ZMod (2 ^ (s + 1)) × ZMod (2 ^ (s + 2)) → G := fun w =>
      dD.ofTorus (Torus.ofInt _ ![(w.2.1.val : ℤ), (w.2.2.val : ℤ), (w.2.2.val : ℤ)]) *
        (if w.1 then x₀ else 1)
    have hcov : ∀ e ∈ X, ∃ w, f w = e := by
      intro e he
      by_cases heD : e ∈ D
      · obtain ⟨p, q, hd⟩ := hfix e he heD
        exact ⟨(false, p, q), by simp [f, hd]⟩
      · obtain ⟨v, hv⟩ := dD.t101_mem_CSz_of_not_mem (hX he) heD
        have hmem : e * x₀⁻¹ ∈ D := by
          rw [hv, hv₀]
          exact dD.nf_u_mul_inv_mem v₀ v
        obtain ⟨p, q, hd⟩ := hfix (e * x₀⁻¹) (mul_mem he (inv_mem hx₀)) hmem
        refine ⟨(true, p, q), ?_⟩
        simp only [f, if_true]
        rw [← hd, inv_mul_cancel_right]
    have hle := Stroth42Core.natCard_le_of_subset_range f hcov
    rw [hcard, hDcard, Nat.card_prod, Nat.card_prod, Nat.card_zmod, Nat.card_zmod] at hle
    have h2 : Nat.card Bool = 2 := by simp [Nat.card_eq_fintype_card]
    rw [h2, show 2 * (2 ^ (s + 1) * 2 ^ (s + 2)) = 2 ^ (2 * s + 4) by ring] at hle
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
    omega
  · simp only [not_exists, not_and, not_not] at hD
    haveI : Finite D := Nat.finite_of_card_ne_zero (by rw [hDcard]; positivity)
    exact Subgroup.eq_of_le_of_card_ge (fun x hx => hD x hx) hcard.ge

end StrothWeakTypeData

end CFSG.CGT.Stroth77
