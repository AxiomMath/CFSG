module

public import CFSG.CGT.Stroth77.Stroth34T200Facts
public import CFSG.CGT.Stroth77.Section42Core

public section

namespace CFSG.CGT.Stroth77

open Matrix Stroth34T200

namespace Stroth47Core

variable {m : ℕ}

theorem t200_one_le_k (hm : 1 ≤ m) (i : Fin 3) : 1 ≤ (StrothTypeIndex.t200 m).k i := by
  fin_cases i
  · exact hm
  · show 1 ≤ m + 2; omega
  · show 1 ≤ m + 2; omega

@[expose] def om200 (m : ℕ) (ε : Fin 3 → ℤ) : Torus (StrothTypeIndex.t200 m).k :=
  Torus.ofInt _ (fun i => ε i * 2 ^ ((StrothTypeIndex.t200 m).k i - 1))

theorem om200_eq_iff (hm : 1 ≤ m) (ε ε' : Fin 3 → ℤ) :
    om200 m ε = om200 m ε' ↔ ∀ i, ε i ≡ ε' i [ZMOD 2] :=
  Stroth42Core.ofInt_mul_two_pow_pred_eq_iff (t200_one_le_k hm) ε ε'

theorem om200_zero : om200 m 0 = 0 := by
  rw [om200, ← Torus.ofInt_zero]
  congr 1
  funext i
  simp

theorem om200_add_self (hm : 1 ≤ m) (ε : Fin 3 → ℤ) : om200 m ε + om200 m ε = 0 := by
  rw [om200, ← Torus.ofInt_add, ← om200_zero, om200]
  rw [show (fun i => ε i * 2 ^ ((StrothTypeIndex.t200 m).k i - 1)) +
      (fun i => ε i * 2 ^ ((StrothTypeIndex.t200 m).k i - 1)) =
      fun i => (2 * ε i) * 2 ^ ((StrothTypeIndex.t200 m).k i - 1) by funext i; simp; ring]
  exact (om200_eq_iff hm _ _).mpr fun i => by
    simp only [Pi.zero_apply]
    exact (Int.emod_emod_of_dvd _ (dvd_refl 2)).symm.trans (by simp)

theorem om200_apply (ε : Fin 3 → ℤ) :
    om200 m ε = Torus.ofInt _ ![ε 0 * 2 ^ (m - 1), ε 1 * 2 ^ (m + 1), ε 2 * 2 ^ (m + 1)] := by
  rw [om200]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem om200_succ (m' : ℕ) (ε : Fin 3 → ℤ) :
    om200 (m' + 1) ε =
      Torus.ofInt _ ![ε 0 * 2 ^ m', ε 1 * 2 ^ (m' + 2), ε 2 * 2 ^ (m' + 2)] := by
  rw [om200]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem t200_φuv_om (hm : 1 ≤ m) (ε : Fin 3 → ℤ) :
    (StrothTypeIndex.t200 m).action.φuv (om200 m ε) =
      om200 m ![-3 * ε 0 + 4 * ε 1 + 4 * ε 2, -ε 0 + ε 1 + 2 * ε 2, -ε 0 + 2 * ε 1 + ε 2] := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [om200_succ, t200_φuv, om200_succ]
  congr 1
  funext i
  fin_cases i <;> simp <;> ring

theorem t200_φt_om (hm : 1 ≤ m) (ε : Fin 3 → ℤ) :
    (StrothTypeIndex.t200 m).action.φt (om200 m ε) =
      om200 m ![ε 0 - 4 * ε 2, ε 0 - ε 1 - 2 * ε 2, -ε 2] := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [om200_succ, t200_φt, om200_succ]
  congr 1
  funext i
  fin_cases i <;> simp <;> ring

theorem t200_φu_om (ε : Fin 3 → ℤ) :
    (StrothTypeIndex.t200 m).action.φu (om200 m ε) = om200 m ![ε 0, ε 2, ε 1] := by
  rw [om200, t200_φu, om200]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem t200_φρ_om (hm : 1 ≤ m) (ε : Fin 3 → ℤ) :
    (StrothTypeIndex.t200 m).action.φρ (om200 m ε) =
      om200 m ![ε 0 - 4 * ε 2, -ε 2, ε 1 - ε 2] := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [om200_succ, t200_φρ, om200_succ]
  congr 1
  funext i
  fin_cases i <;> simp <;> ring

theorem t200_faithful (hm : 1 ≤ m) (i j l : Bool)
    (h : ∀ v, (StrothTypeIndex.t200 m).action.d8Act i j l v = v) :
    i = false ∧ j = false ∧ l = false := by
  have hc := h (om200 m ![1, 0, 0])
  have ha := h (om200 m ![0, 1, 0])
  cases i <;> cases j <;> cases l <;>
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte,
      AddMonoidHom.comp_apply, AddMonoidHom.id_apply, t200_φuv_om hm, t200_φt_om hm,
      t200_φu_om, om200_eq_iff hm] at hc ha <;>
    first
    | exact ⟨rfl, rfl, rfl⟩
    | exact absurd hc (by decide)
    | exact absurd ha (by decide)

theorem t200_faithful_om (hm : 1 ≤ m) (i j l : Bool)
    (hc : (StrothTypeIndex.t200 m).action.d8Act i j l (om200 m ![1, 0, 0]) = om200 m ![1, 0, 0])
    (ha : (StrothTypeIndex.t200 m).action.d8Act i j l (om200 m ![0, 1, 0]) =
      om200 m ![0, 1, 0]) :
    i = false ∧ j = false ∧ l = false := by
  cases i <;> cases j <;> cases l <;>
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte,
      AddMonoidHom.comp_apply, AddMonoidHom.id_apply, t200_φuv_om hm, t200_φt_om hm,
      t200_φu_om, om200_eq_iff hm] at hc ha <;>
    first
    | exact ⟨rfl, rfl, rfl⟩
    | exact absurd hc (by decide)
    | exact absurd ha (by decide)

end Stroth47Core

open Stroth47Core

namespace StrothWeakTypeData

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ}
  (dD : StrothWeakTypeData D (.t200 m))

theorem t200_c_pow : (dD.c : G) ^ 2 ^ (m - 1) = dD.ofTorus (om200 m ![1, 0, 0]) := by
  rw [c_eq, ← ofTorus_nsmul]
  congr 1
  funext i
  fin_cases i <;> simp [om200, gen, Pi.single_apply] <;> rfl

theorem t200_a_pow : (dD.a : G) ^ 2 ^ (m + 1) = dD.ofTorus (om200 m ![0, 1, 0]) := by
  rw [a_eq, ← ofTorus_nsmul]
  congr 1
  funext i
  fin_cases i <;> simp [om200, gen, Pi.single_apply] <;> rfl

theorem t200_b_pow : (dD.b : G) ^ 2 ^ (m + 1) = dD.ofTorus (om200 m ![0, 0, 1]) := by
  rw [b_eq, ← ofTorus_nsmul]
  congr 1
  funext i
  fin_cases i <;> simp [om200, gen, Pi.single_apply] <;> rfl

theorem t200_eq_om_of_mul_self (hm : 1 ≤ m) {y : G} (hy : y ∈ D) (h2 : y * y = 1) :
    ∃ ε : Fin 3 → ℤ, (∀ i, ε i = 0 ∨ ε i = 1) ∧ y = dD.ofTorus (om200 m ε) := by
  obtain ⟨v, rfl⟩ := dD.exists_ofTorus hy
  rw [ofTorus_mul_self, ofTorus_eq_one_iff] at h2
  have h2' : (2 : ℤ) • v = 0 := by rw [two_zsmul]; exact h2
  obtain ⟨ε, hε, rfl⟩ := (Torus.two_zsmul_eq_zero_iff (t200_one_le_k hm) v).mp h2'
  exact ⟨ε, hε, rfl⟩

theorem t200_h3 (hm : 1 ≤ m) :
    ∀ y ∈ D, y * y = 1 → y ≠ 1 →
      (∃ p ∈ Subgroup.closure {dD.uv, dD.t, dD.u}, p⁻¹ * y * p = (dD.c : G) ^ 2 ^ (m - 1)) ∨
        ∃ g ∈ dD.L, g⁻¹ * y * g = (dD.a : G) ^ 2 ^ (m + 1) := by
  intro y hy h2 h1
  obtain ⟨ε, hε, rfl⟩ := dD.t200_eq_om_of_mul_self hm hy h2
  rw [dD.t200_c_pow, dD.t200_a_pow]
  have hW : ∀ x ∈ ({dD.uv, dD.t, dD.u} : Set G), x ∈ Subgroup.closure {dD.uv, dD.t, dD.u} :=
    fun x hx => Subgroup.subset_closure hx
  have hconj_uv := dD.conj_ofTorus dD.uv_mem dD.uv_conj
  have hconj_t := dD.conj_ofTorus dD.t_mem dD.t_conj
  have hconj_ρ := dD.conj_ofTorus dD.ρ_mem dD.ρ_conj
  have hε0 : ¬ (ε 0 = 0 ∧ ε 1 = 0 ∧ ε 2 = 0) := by
    rintro ⟨h0, h1', h2'⟩
    apply h1
    rw [← dD.ofTorus_zero, ← om200_zero]
    congr 2
    funext i
    fin_cases i <;> simp [h0, h1', h2']
  have hεv : ε = ![ε 0, ε 1, ε 2] := by
    funext i; fin_cases i <;> rfl
  rcases hε 0 with e0 | e0 <;> rcases hε 1 with e1 | e1 <;> rcases hε 2 with e2 | e2 <;>
    rw [hεv, e0, e1, e2]
  · exact absurd ⟨e0, e1, e2⟩ hε0
  · right
    refine ⟨dD.ρ * dD.ρ, mul_mem dD.ρ_mem_L dD.ρ_mem_L, ?_⟩
    rw [mul_inv_rev, show (dD.ρ⁻¹ * dD.ρ⁻¹ * dD.ofTorus (om200 m ![0, 0, 1]) * (dD.ρ * dD.ρ)) =
      dD.ρ⁻¹ * (dD.ρ⁻¹ * dD.ofTorus (om200 m ![0, 0, 1]) * dD.ρ) * dD.ρ by group, hconj_ρ,
      hconj_ρ, t200_φρ_om hm, t200_φρ_om hm]
    exact congrArg dD.ofTorus ((om200_eq_iff hm _ _).mpr (by decide))
  · right
    exact ⟨1, one_mem _, by simp⟩
  · right
    refine ⟨dD.ρ, dD.ρ_mem_L, ?_⟩
    rw [hconj_ρ, t200_φρ_om hm]
    exact congrArg dD.ofTorus ((om200_eq_iff hm _ _).mpr (by decide))
  · left
    exact ⟨1, one_mem _, by simp⟩
  · left
    refine ⟨dD.uv * dD.t, mul_mem (hW _ (by simp)) (hW _ (by simp)), ?_⟩
    rw [mul_inv_rev, show dD.t⁻¹ * dD.uv⁻¹ * dD.ofTorus (om200 m ![1, 0, 1]) * (dD.uv * dD.t) =
      dD.t⁻¹ * (dD.uv⁻¹ * dD.ofTorus (om200 m ![1, 0, 1]) * dD.uv) * dD.t by group, hconj_uv,
      hconj_t, t200_φuv_om hm, t200_φt_om hm]
    exact congrArg dD.ofTorus ((om200_eq_iff hm _ _).mpr (by decide))
  · left
    refine ⟨dD.t, hW _ (by simp), ?_⟩
    rw [hconj_t, t200_φt_om hm]
    exact congrArg dD.ofTorus ((om200_eq_iff hm _ _).mpr (by decide))
  · left
    refine ⟨dD.uv, hW _ (by simp), ?_⟩
    rw [hconj_uv, t200_φuv_om hm]
    exact congrArg dD.ofTorus ((om200_eq_iff hm _ _).mpr (by decide))

theorem t200_comm_z (hm : 1 ≤ m) {v : Torus (StrothTypeIndex.t200 m).k} {i j l : Bool}
    (h : dD.ofTorus v * dD.d8 i j l * (dD.c : G) ^ 2 ^ (m - 1) =
      (dD.c : G) ^ 2 ^ (m - 1) * (dD.ofTorus v * dD.d8 i j l)) : i = false ∧ j = false := by
  rw [dD.t200_c_pow, nf_commute_iff] at h
  cases i <;> cases j <;> cases l <;>
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, t200_φuv_om hm, t200_φt_om hm, t200_φu_om, om200_eq_iff hm] at h <;>
    first
    | exact ⟨rfl, rfl⟩
    | exact absurd h (by decide)

theorem t200_om_comm {v : Torus (StrothTypeIndex.t200 m).k} {i j l : Bool} {ε : Fin 3 → ℤ}
    (h : (StrothTypeIndex.t200 m).action.d8Act i j l (om200 m ε) = om200 m ε) :
    dD.ofTorus (om200 m ε) * (dD.ofTorus v * dD.d8 i j l) =
      dD.ofTorus v * dD.d8 i j l * dD.ofTorus (om200 m ε) :=
  ((dD.nf_commute_iff v (om200 m ε) i j l).mpr h).symm

theorem t200_h6 (hm : 1 ≤ m) :
    ∀ y : G, y * dD.uv ∈ D → y * y = 1 → ∃ E : Subgroup G,
      E ≤ Subgroup.centralizer {y} ∧ (∀ e ∈ E, e * e = 1) ∧ Nat.card E = 16 := by
  intro y hy hyy
  have hF := t200_faithful (m := m) hm
  obtain ⟨v, hv⟩ := dD.exists_ofTorus hy
  have hyv : y = dD.ofTorus v * dD.d8 true false false := by
    rw [d8_tff, ← hv, mul_assoc, dD.uv_sq, mul_one]
  subst hyv
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
  have hsq := hyy
  rw [nf_mul_self, Bool.and_false, d8_fff, mul_one, ofTorus_eq_one_iff] at hsq
  simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
    AddMonoidHom.id_apply, t200_φuv] at hsq
  rw [← Torus.ofInt_add, t200_ofInt_eq_zero_iff] at hsq
  obtain ⟨-, hsq1, -⟩ := hsq
  simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero] at hsq1
  set w : Fin 3 → ℤ := ![0, -x 2, 0] with hw
  have hdecide : ∀ (ε ε' : Fin 3 → ℤ), (∀ i, ε i ≡ ε' i [ZMOD 2]) → om200 m ε = om200 m ε' :=
    fun ε ε' h => (om200_eq_iff hm ε ε').mpr h
  refine Stroth42Core.exists_E16 (H := D) (x₁ := dD.ofTorus (om200 m ![0, 1, 0]))
    (x₂ := dD.ofTorus (om200 m ![0, 0, 1]))
    (y₃ := dD.ofTorus (Torus.ofInt _ x) * dD.d8 true false false)
    (y₄ := dD.ofTorus (Torus.ofInt _ w) * dD.d8 false true false)
    (dD.ofTorus_mem _) (dD.ofTorus_mem _) ?_ ?_ hyy ?_ (dD.ofTorus_comm _ _) ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?_
  · rw [ofTorus_mul_self, om200_add_self hm, ofTorus_zero]
  · rw [ofTorus_mul_self, om200_add_self hm, ofTorus_zero]
  · rw [nf_mul_self, Bool.and_true, d8_fff, mul_one, ofTorus_eq_one_iff]
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, t200_φt, ← Torus.ofInt_add]
    rw [← Torus.ofInt_zero]
    congr 1
    funext i
    fin_cases i <;> simp [hw]
  · refine dD.t200_om_comm ?_
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, t200_φuv_om hm]
    exact hdecide _ _ (by decide)
  · refine dD.t200_om_comm ?_
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, t200_φt_om hm]
    exact hdecide _ _ (by decide)
  · refine dD.t200_om_comm ?_
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, t200_φuv_om hm]
    exact hdecide _ _ (by decide)
  · refine dD.t200_om_comm ?_
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, t200_φt_om hm]
    exact hdecide _ _ (by decide)
  · rw [nf_mul_nf, nf_mul_nf]
    congr 1
    congr 1
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, t200_φuv, t200_φt, ← Torus.ofInt_add]
    rw [t200_ofInt_eq_iff]
    simp only [hw, Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    refine ⟨⟨0, by ring⟩, ?_, ⟨0, by ring⟩⟩
    obtain ⟨c, hc⟩ := hsq1
    exact ⟨-c, by linear_combination -hc⟩
  · rw [Ne, ofTorus_eq_one_iff, ← om200_zero, om200_eq_iff hm]
    decide
  · rw [Ne, ofTorus_eq_one_iff, ← om200_zero, om200_eq_iff hm]
    decide
  · rw [Ne, dD.ofTorus_inj.eq_iff, om200_eq_iff hm]
    decide
  · exact dD.d8_not_mem hF (by decide) _
  · exact dD.d8_not_mem hF (by decide) _
  · rw [nf_mul_nf]
    exact dD.d8_not_mem hF (by decide) _
  · refine dD.t200_om_comm ?_
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, t200_φuv_om hm]
    exact hdecide _ _ (by decide)
  · refine dD.t200_om_comm ?_
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, t200_φuv_om hm]
    exact hdecide _ _ (by decide)
  · rw [nf_mul_nf, nf_mul_nf]
    congr 1
    congr 1
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, t200_φuv, t200_φt, ← Torus.ofInt_add]
    rw [t200_ofInt_eq_iff]
    simp only [hw, Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    refine ⟨⟨0, by ring⟩, ?_, ⟨0, by ring⟩⟩
    obtain ⟨c, hc⟩ := hsq1
    exact ⟨c, by linear_combination hc⟩

theorem t200_h4 (hm : 1 ≤ m) :
    ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u},
      y * (dD.c : G) ^ 2 ^ (m - 1) = (dD.c : G) ^ 2 ^ (m - 1) * y →
        y ^ 2 ^ m ≠ (dD.c : G) ^ 2 ^ (m - 1) := by
  intro y hy hcomm hpow
  obtain ⟨v, i, j, l, rfl⟩ := dD.mem_sup_iff.mp hy
  obtain ⟨rfl, rfl⟩ := dD.t200_comm_z hm hcomm
  obtain ⟨x0, x1, x2, rfl⟩ := t200_exists_vec v
  rw [Stroth42Core.pow_two_pow_eq_mul_self _ hm, nf_mul_self, Bool.and_false, d8_fff, mul_one,
    ← ofTorus_nsmul, dD.t200_c_pow] at hpow
  have h := dD.ofTorus_inj hpow
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel, om200_succ] at h
  have hc0 : ∀ w : Torus (StrothTypeIndex.t200 (m' + 1)).k, w = Torus.ofInt _ ![x0, x1, x2] +
      (StrothTypeIndex.t200 (m' + 1)).action.d8Act false false l (Torus.ofInt _ ![x0, x1, x2]) →
      ∃ y1 y2 : ℤ, w = Torus.ofInt _ ![2 * x0, y1, y2] := by
    intro w hw
    cases l <;> simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte,
      AddMonoidHom.comp_apply, AddMonoidHom.id_apply, t200_φu, t200_add_vec] at hw <;>
      (try simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons] at hw)
    · exact ⟨_, _, by rw [hw]; congr 2; ring⟩
    · exact ⟨_, _, by rw [hw]; congr 2; ring⟩
  obtain ⟨y1, y2, hw⟩ := hc0 _ rfl
  rw [hw, ← natCast_zsmul, t200_zsmul_vec, t200_ofInt_eq_iff] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at h
  obtain ⟨⟨k, hk⟩, -, -⟩ := h
  push_cast at hk
  have h2 : (2 : ℤ) ^ m' * 1 = 2 ^ m' * (2 * (x0 + k)) := by linear_combination hk
  have h3 := mul_left_cancel₀ (pow_ne_zero m' (two_ne_zero : (2 : ℤ) ≠ 0)) h2
  omega

end StrothWeakTypeData

end CFSG.CGT.Stroth77
