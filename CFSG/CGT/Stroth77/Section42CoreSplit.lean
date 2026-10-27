module

public import CFSG.CGT.Stroth77.Section42Core

public section

namespace CFSG.CGT.Stroth77

open Matrix

namespace Type100

theorem uvM_mulVec (x : Fin 3 → ℤ) :
    uvM *ᵥ x = ![-3 * x 0 + 2 * x 1 + 2 * x 2, -2 * x 0 + x 1 + 2 * x 2, -2 * x 0 + 2 * x 1 + x 2] := by
  funext i
  fin_cases i <;> simp [uvM, uvA, tM, ρM] <;> ring

theorem tM_mulVec (x : Fin 3 → ℤ) :
    tM *ᵥ x = ![x 0 - 2 * x 2, 2 * x 0 - x 1 - 2 * x 2, -x 2] := by
  funext i
  fin_cases i <;> simp [uvA, tM, ρM] <;> ring

theorem uM_mulVec (x : Fin 3 → ℤ) : uM *ᵥ x = ![x 0, x 2, x 1] := by
  funext i
  fin_cases i <;> simp [uM, uMat]

theorem ρM_mulVec (x : Fin 3 → ℤ) : ρM *ᵥ x = ![x 0 - 2 * x 2, -x 2, x 1 - x 2] := by
  funext i
  fin_cases i <;> simp [ρM] <;> ring

end Type100

namespace Stroth42Core

variable {m : ℕ}

theorem t100_φuv (x : Fin 3 → ℤ) :
    (StrothTypeIndex.t100 m).action.φuv (Torus.ofInt _ x) = Torus.ofInt _
      ![-3 * x 0 + 2 * x 1 + 2 * x 2, -2 * x 0 + x 1 + 2 * x 2, -2 * x 0 + 2 * x 1 + x 2] := by
  have h := matAct_ofInt (k := (StrothTypeIndex.t100 m).k) Type100.uvM
    (StrothTypeIndex.t100 m).action.compat_uv x
  rw [Type100.uvM_mulVec] at h
  exact h

theorem t100_φt (x : Fin 3 → ℤ) :
    (StrothTypeIndex.t100 m).action.φt (Torus.ofInt _ x) =
      Torus.ofInt _ ![x 0 - 2 * x 2, 2 * x 0 - x 1 - 2 * x 2, -x 2] := by
  have h := matAct_ofInt (k := (StrothTypeIndex.t100 m).k) Type100.tM
    (StrothTypeIndex.t100 m).action.compat_t x
  rw [Type100.tM_mulVec] at h
  exact h

theorem t100_φu (x : Fin 3 → ℤ) :
    (StrothTypeIndex.t100 m).action.φu (Torus.ofInt _ x) = Torus.ofInt _ ![x 0, x 2, x 1] := by
  have h := matAct_ofInt (k := (StrothTypeIndex.t100 m).k) Type100.uM
    (StrothTypeIndex.t100 m).action.compat_u x
  rw [Type100.uM_mulVec] at h
  exact h

theorem t100_φρ (x : Fin 3 → ℤ) :
    (StrothTypeIndex.t100 m).action.φρ (Torus.ofInt _ x) =
      Torus.ofInt _ ![x 0 - 2 * x 2, -x 2, x 1 - x 2] := by
  have h := matAct_ofInt (k := (StrothTypeIndex.t100 m).k) Type100.ρM
    (StrothTypeIndex.t100 m).action.compat_ρ x
  rw [Type100.ρM_mulVec] at h
  exact h

theorem t100_ofInt_eq_iff (x y : Fin 3 → ℤ) :
    Torus.ofInt (StrothTypeIndex.t100 m).k x = Torus.ofInt _ y ↔
      (2 : ℤ) ^ m ∣ y 0 - x 0 ∧ (2 : ℤ) ^ (m + 1) ∣ y 1 - x 1 ∧
        (2 : ℤ) ^ (m + 1) ∣ y 2 - x 2 := by
  rw [Torus.ofInt_eq_ofInt_iff]
  constructor
  · intro h
    exact ⟨Int.modEq_iff_dvd.mp (h 0), Int.modEq_iff_dvd.mp (h 1), Int.modEq_iff_dvd.mp (h 2)⟩
  · rintro ⟨h0, h1, h2⟩ i
    fin_cases i
    · exact Int.modEq_iff_dvd.mpr h0
    · exact Int.modEq_iff_dvd.mpr h1
    · exact Int.modEq_iff_dvd.mpr h2

theorem t100_ofInt_eq_zero_iff (x : Fin 3 → ℤ) :
    Torus.ofInt (StrothTypeIndex.t100 m).k x = 0 ↔
      (2 : ℤ) ^ m ∣ x 0 ∧ (2 : ℤ) ^ (m + 1) ∣ x 1 ∧ (2 : ℤ) ^ (m + 1) ∣ x 2 := by
  rw [← Torus.ofInt_zero, t100_ofInt_eq_iff]
  simp

@[expose] def om100 (m : ℕ) (ε : Fin 3 → ℤ) : Torus (StrothTypeIndex.t100 m).k :=
  Torus.ofInt _ (fun i => ε i * 2 ^ ((StrothTypeIndex.t100 m).k i - 1))

theorem t100_one_le_k (hm : 1 ≤ m) (i : Fin 3) : 1 ≤ (StrothTypeIndex.t100 m).k i := by
  fin_cases i
  · exact hm
  · show 1 ≤ m + 1; omega
  · show 1 ≤ m + 1; omega

theorem om100_eq_iff (hm : 1 ≤ m) (ε ε' : Fin 3 → ℤ) :
    om100 m ε = om100 m ε' ↔ ∀ i, ε i ≡ ε' i [ZMOD 2] :=
  ofInt_mul_two_pow_pred_eq_iff (t100_one_le_k hm) ε ε'

theorem om100_zero : om100 m 0 = 0 := by
  rw [om100, ← Torus.ofInt_zero]
  congr 1
  funext i
  simp

theorem om100_add_self (hm : 1 ≤ m) (ε : Fin 3 → ℤ) : om100 m ε + om100 m ε = 0 := by
  rw [om100, ← Torus.ofInt_add, ← om100_zero, om100]
  rw [show (fun i => ε i * 2 ^ ((StrothTypeIndex.t100 m).k i - 1)) +
      (fun i => ε i * 2 ^ ((StrothTypeIndex.t100 m).k i - 1)) =
      fun i => (2 * ε i) * 2 ^ ((StrothTypeIndex.t100 m).k i - 1) by funext i; simp; ring]
  exact (om100_eq_iff hm _ _).mpr fun i => by
    simp only [Pi.zero_apply]
    exact (Int.emod_emod_of_dvd _ (dvd_refl 2)).symm.trans (by simp)

theorem om100_succ (m' : ℕ) (ε : Fin 3 → ℤ) :
    om100 (m' + 1) ε = Torus.ofInt _ ![ε 0 * 2 ^ m', ε 1 * 2 ^ (m' + 1), ε 2 * 2 ^ (m' + 1)] := by
  rw [om100]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem t100_φuv_om (hm : 1 ≤ m) (ε : Fin 3 → ℤ) :
    (StrothTypeIndex.t100 m).action.φuv (om100 m ε) =
      om100 m ![-3 * ε 0 + 4 * ε 1 + 4 * ε 2, -ε 0 + ε 1 + 2 * ε 2, -ε 0 + 2 * ε 1 + ε 2] := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [om100_succ, t100_φuv, om100_succ]
  congr 1
  funext i
  fin_cases i <;> simp <;> ring

theorem t100_φt_om (hm : 1 ≤ m) (ε : Fin 3 → ℤ) :
    (StrothTypeIndex.t100 m).action.φt (om100 m ε) =
      om100 m ![ε 0 - 4 * ε 2, ε 0 - ε 1 - 2 * ε 2, -ε 2] := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [om100_succ, t100_φt, om100_succ]
  congr 1
  funext i
  fin_cases i <;> simp <;> ring

theorem t100_φu_om (ε : Fin 3 → ℤ) :
    (StrothTypeIndex.t100 m).action.φu (om100 m ε) = om100 m ![ε 0, ε 2, ε 1] := by
  rw [om100, t100_φu, om100]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem t100_φρ_om (hm : 1 ≤ m) (ε : Fin 3 → ℤ) :
    (StrothTypeIndex.t100 m).action.φρ (om100 m ε) =
      om100 m ![ε 0 - 4 * ε 2, -ε 2, ε 1 - ε 2] := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [om100_succ, t100_φρ, om100_succ]
  congr 1
  funext i
  fin_cases i <;> simp <;> ring

theorem t100_faithful (hm : 1 ≤ m) (i j l : Bool)
    (h : ∀ v, (StrothTypeIndex.t100 m).action.d8Act i j l v = v) :
    i = false ∧ j = false ∧ l = false := by
  have hc := h (om100 m ![1, 0, 0])
  have ha := h (om100 m ![0, 1, 0])
  cases i <;> cases j <;> cases l <;>
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte,
      AddMonoidHom.comp_apply, AddMonoidHom.id_apply, t100_φuv_om hm, t100_φt_om hm,
      t100_φu_om, om100_eq_iff hm] at hc ha <;>
    first
    | exact ⟨rfl, rfl, rfl⟩
    | exact absurd hc (by decide)
    | exact absurd ha (by decide)

theorem t100_parity (hm : 1 ≤ m) (i j l : Bool) (v : Torus (StrothTypeIndex.t100 m).k) :
    Even (((StrothTypeIndex.t100 m).action.d8Act i j l v) 0) ↔ Even (v 0) := by
  have hk : 1 ≤ (StrothTypeIndex.t100 m).k 0 := hm
  refine SigmaFourAction.even_d8Act_zero_iff _ ?_ ?_ ?_ i j l v
  · exact even_matAct_zero_iff hk Type100.uvM (Type100.compat_uv m) (by decide) (by decide)
      (by decide)
  · exact even_matAct_zero_iff hk Type100.tM (Type100.compat_t m) (by decide) (by decide)
      (by decide)
  · exact even_matAct_zero_iff hk Type100.uM (Type100.compat_u m) (by decide) (by decide)
      (by decide)

end Stroth42Core

open Stroth42Core

namespace Stroth42Core

variable {G : Type*} [Group G]

theorem exists_E16_of_conj {y y' g : G} (h : y = g⁻¹ * y' * g)
    (hE : ∃ E : Subgroup G, E ≤ Subgroup.centralizer {y'} ∧ (∀ e ∈ E, e * e = 1) ∧
      Nat.card E = 16) :
    ∃ E : Subgroup G, E ≤ Subgroup.centralizer {y} ∧ (∀ e ∈ E, e * e = 1) ∧
      Nat.card E = 16 := by
  obtain ⟨E, hEc, hEi, hEn⟩ := hE
  refine ⟨E.map (MulAut.conj g⁻¹).toMonoidHom, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hx' := Subgroup.mem_centralizer_iff.mp (hEc hx) y' (Set.mem_singleton _)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, h]
    calc g⁻¹ * y' * g * (g⁻¹ * x * g) = g⁻¹ * (y' * x) * g := by group
      _ = g⁻¹ * (x * y') * g := by rw [hx']
      _ = g⁻¹ * x * g * (g⁻¹ * y' * g) := by group
  · rintro _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc g⁻¹ * x * g * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g := by group
      _ = 1 := by rw [hEi x hx]; group
  · rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hEn]

theorem not_dvd_pow_pred_sub {m : ℕ} (hm : 1 ≤ m) {A : ℤ} (h1 : (2 : ℤ) ^ m ∣ 2 ^ (m - 1) - A)
    (h2 : (2 : ℤ) ^ (m + 1) ∣ 0 - A) : False := by
  have hA : (2 : ℤ) ^ m ∣ A := by
    have : (2 : ℤ) ^ m ∣ 2 ^ (m + 1) := pow_dvd_pow 2 (by omega)
    have h3 := this.trans h2
    simpa using h3.neg_right
  have h' : (2 : ℤ) ^ m ∣ 2 ^ (m - 1) := by
    have := dvd_add h1 hA
    simpa using this
  have hlt : (2 : ℤ) ^ (m - 1) < 2 ^ m := pow_lt_pow_right₀ (by norm_num) (by omega)
  have hpos : (0 : ℤ) < 2 ^ (m - 1) := by positivity
  exact absurd (Int.le_of_dvd hpos h') (not_le.mpr hlt)

theorem not_dvd_pow_pred_sub_of_odd {m n : ℕ} (hm : 1 ≤ m) {w₀ w₁ : ℤ} (hw₁ : w₁ % 2 = 1)
    (h1 : (2 : ℤ) ^ m ∣ 2 ^ (m - 1) - 2 ^ n * w₀) (h2 : (2 : ℤ) ^ (m + 1) ∣ 0 - 2 ^ n * w₁) :
    False := by
  have hcop : IsCoprime ((2 : ℤ) ^ (m + 1)) w₁ := by
    have h2c : IsCoprime (2 : ℤ) w₁ := by
      obtain ⟨k, hk⟩ : ∃ k, w₁ = 2 * k + 1 := ⟨w₁ / 2, by omega⟩
      exact ⟨-k, 1, by rw [hk]; ring⟩
    exact h2c.pow_left
  have h3 : (2 : ℤ) ^ (m + 1) ∣ 2 ^ n := hcop.dvd_of_dvd_mul_right (by simpa using h2.neg_right)
  refine not_dvd_pow_pred_sub hm h1 ?_
  simpa using (h3.mul_right w₀).neg_right

theorem two_pow_dvd_eight {n : ℕ} (hn : 3 ≤ n) {A : ℤ} (h : (2 : ℤ) ^ n ∣ A) : 8 ∣ A := by
  have h8 : (8 : ℤ) ∣ 2 ^ n := by
    rw [show (8 : ℤ) = 2 ^ 3 by norm_num]
    exact pow_dvd_pow 2 hn
  exact h8.trans h

end Stroth42Core

namespace StrothWeakTypeData

section Rho

variable {G : Type*} [Group G] {D : Subgroup G} {τ : StrothTypeIndex}
  (dD : StrothWeakTypeData D τ)

theorem conj_rho_uv : dD.ρ⁻¹ * dD.uv * dD.ρ = dD.t := by
  rw [mul_assoc, dD.uv_rho]; group

theorem conj_rho_t : dD.ρ⁻¹ * dD.t * dD.ρ = dD.uv * dD.t := by
  rw [mul_assoc, dD.t_rho]; group

theorem rho_mul_ofTorus_mul_rho_inv (v : Torus τ.k) :
    dD.ρ * dD.ofTorus v * dD.ρ⁻¹ = dD.ofTorus (τ.action.φρ (τ.action.φρ v)) := by
  have h := dD.conj_ofTorus dD.ρ_mem dD.ρ_conj (τ.action.φρ (τ.action.φρ v))
  rw [SigmaFourAction.φρ_φρ_φρ] at h
  rw [← h]
  group

theorem exists_E16_of_mem_t_coset
    (h6 : ∀ y : G, y * dD.uv ∈ D → y * y = 1 → ∃ E : Subgroup G,
      E ≤ Subgroup.centralizer {y} ∧ (∀ e ∈ E, e * e = 1) ∧ Nat.card E = 16)
    {y : G} (hy : y * dD.t ∈ D) (hyy : y * y = 1) :
    ∃ E : Subgroup G, E ≤ Subgroup.centralizer {y} ∧ (∀ e ∈ E, e * e = 1) ∧
      Nat.card E = 16 := by
  obtain ⟨v, hv⟩ := dD.exists_ofTorus hy
  have hyv : y = dD.ofTorus v * dD.t := by
    rw [← hv, mul_assoc, dD.t_sq, mul_one]
  have hy' : dD.ρ * y * dD.ρ⁻¹ =
      dD.ofTorus (τ.action.φρ (τ.action.φρ v)) * dD.uv := by
    have ht : dD.ρ * dD.t * dD.ρ⁻¹ = dD.uv := by
      rw [← dD.conj_rho_uv]; group
    rw [hyv, ← dD.rho_mul_ofTorus_mul_rho_inv, ← ht]
    group
  refine Stroth42Core.exists_E16_of_conj (y' := dD.ρ * y * dD.ρ⁻¹) (g := dD.ρ) (by group)
    (h6 _ ?_ ?_)
  · rw [hy', mul_assoc, dD.uv_sq, mul_one]
    exact dD.ofTorus_mem _
  · calc dD.ρ * y * dD.ρ⁻¹ * (dD.ρ * y * dD.ρ⁻¹) = dD.ρ * (y * y) * dD.ρ⁻¹ := by group
      _ = 1 := by rw [hyy]; group

theorem exists_E16_of_mem_uvt_coset
    (h6 : ∀ y : G, y * dD.uv ∈ D → y * y = 1 → ∃ E : Subgroup G,
      E ≤ Subgroup.centralizer {y} ∧ (∀ e ∈ E, e * e = 1) ∧ Nat.card E = 16)
    {y : G} (hy : y * (dD.uv * dD.t) ∈ D) (hyy : y * y = 1) :
    ∃ E : Subgroup G, E ≤ Subgroup.centralizer {y} ∧ (∀ e ∈ E, e * e = 1) ∧
      Nat.card E = 16 := by
  obtain ⟨v, hv⟩ := dD.exists_ofTorus hy
  have huvt : dD.uv * dD.t * (dD.uv * dD.t) = 1 := by
    rw [mul_assoc, ← mul_assoc dD.t, ← dD.uv_comm_t, mul_assoc, dD.t_sq, mul_one, dD.uv_sq]
  have hyv : y = dD.ofTorus v * (dD.uv * dD.t) := by
    rw [← hv, mul_assoc, huvt, mul_one]
  have hy' : dD.ρ⁻¹ * y * dD.ρ = dD.ofTorus (τ.action.φρ v) * dD.uv := by
    have h1 : dD.ρ⁻¹ * (dD.uv * dD.t) * dD.ρ = dD.uv := by
      calc dD.ρ⁻¹ * (dD.uv * dD.t) * dD.ρ =
          (dD.ρ⁻¹ * dD.uv * dD.ρ) * (dD.ρ⁻¹ * dD.t * dD.ρ) := by group
        _ = dD.t * (dD.uv * dD.t) := by rw [dD.conj_rho_uv, dD.conj_rho_t]
        _ = dD.uv := by rw [← mul_assoc, ← dD.uv_comm_t, mul_assoc, dD.t_sq, mul_one]
    calc dD.ρ⁻¹ * y * dD.ρ =
        (dD.ρ⁻¹ * dD.ofTorus v * dD.ρ) * (dD.ρ⁻¹ * (dD.uv * dD.t) * dD.ρ) := by
          rw [hyv]; group
      _ = dD.ofTorus (τ.action.φρ v) * dD.uv := by
          rw [dD.conj_ofTorus dD.ρ_mem dD.ρ_conj, h1]
  refine Stroth42Core.exists_E16_of_conj (y' := dD.ρ⁻¹ * y * dD.ρ) (g := dD.ρ⁻¹) (by group)
    (h6 _ ?_ ?_)
  · rw [hy', mul_assoc, dD.uv_sq, mul_one]
    exact dD.ofTorus_mem _
  · calc dD.ρ⁻¹ * y * dD.ρ * (dD.ρ⁻¹ * y * dD.ρ) = dD.ρ⁻¹ * (y * y) * dD.ρ := by group
      _ = 1 := by rw [hyy]; group

theorem nf_mul_self_of_false (v : Torus τ.k) {i j l : Bool} (hlj : (l && j) = false) :
    dD.ofTorus v * dD.d8 i j l * (dD.ofTorus v * dD.d8 i j l) =
      dD.ofTorus (v + τ.action.d8Act i j l v) := by
  rw [nf_mul_self, hlj, d8_fff, mul_one]

theorem nf_mul_self_of_true (v : Torus τ.k) {i j l : Bool} (hlj : (l && j) = true) :
    dD.ofTorus v * dD.d8 i j l * (dD.ofTorus v * dD.d8 i j l) =
      dD.ofTorus (v + τ.action.d8Act i j l v) * dD.d8 true false false := by
  rw [nf_mul_self, hlj]

theorem pow_two_pow_of_mul_self {y : G} {W : Torus τ.k} (h : y * y = dD.ofTorus W) {n : ℕ}
    (hn : 1 ≤ n) : y ^ 2 ^ n = dD.ofTorus ((2 ^ (n - 1) : ℕ) • W) := by
  rw [Stroth42Core.pow_two_pow_eq_mul_self y hn, h, ofTorus_nsmul]

end Rho

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ}
  (dD : StrothWeakTypeData D (.t100 m))

theorem t100_c_pow : (dD.c : G) ^ 2 ^ (m - 1) = dD.ofTorus (om100 m ![1, 0, 0]) := by
  rw [c_eq, ← ofTorus_nsmul]
  congr 1
  funext i
  fin_cases i <;> simp [om100, gen, Pi.single_apply] <;> rfl

theorem t100_a_pow : (dD.a : G) ^ 2 ^ m = dD.ofTorus (om100 m ![0, 1, 0]) := by
  rw [a_eq, ← ofTorus_nsmul]
  congr 1
  funext i
  fin_cases i <;> simp [om100, gen, Pi.single_apply] <;> rfl

theorem t100_b_pow : (dD.b : G) ^ 2 ^ m = dD.ofTorus (om100 m ![0, 0, 1]) := by
  rw [b_eq, ← ofTorus_nsmul]
  congr 1
  funext i
  fin_cases i <;> simp [om100, gen, Pi.single_apply] <;> rfl

theorem t100_eq_om_of_mul_self (hm : 1 ≤ m) {y : G} (hy : y ∈ D) (h2 : y * y = 1) :
    ∃ ε : Fin 3 → ℤ, (∀ i, ε i = 0 ∨ ε i = 1) ∧ y = dD.ofTorus (om100 m ε) := by
  obtain ⟨v, rfl⟩ := dD.exists_ofTorus hy
  rw [ofTorus_mul_self, ofTorus_eq_one_iff] at h2
  have h2' : (2 : ℤ) • v = 0 := by rw [two_zsmul]; exact h2
  obtain ⟨ε, hε, rfl⟩ := (Torus.two_zsmul_eq_zero_iff (t100_one_le_k hm) v).mp h2'
  exact ⟨ε, hε, rfl⟩

theorem om100_c (m : ℕ) :
    om100 m ![1, 0, 0] = Torus.ofInt (StrothTypeIndex.t100 m).k ![2 ^ (m - 1), 0, 0] := by
  rw [om100]
  congr 1
  funext i
  fin_cases i <;> simp <;> rfl

theorem t100_h1 (hm : 2 ≤ m) :
    (Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u}).relIndex
      (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}) = 2 :=
  dD.relIndex_S₁ (by show 1 ≤ m; omega) (t100_faithful (by omega)) (t100_parity (by omega))

theorem t100_h2 (hm : 2 ≤ m) :
    (dD.c : G) ∉
      Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u} :=
  dD.c_not_mem_S₁ (by show 1 ≤ m; omega) (t100_faithful (by omega)) (t100_parity (by omega))

theorem t100_h5 :
    ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}, y * y ∈ D ∨ y * y * dD.uv ∈ D :=
  dD.mul_self_mem_or

theorem t100_h3 (hm : 2 ≤ m) :
    ∀ y ∈ D, y * y = 1 → y ≠ 1 →
      (∃ p ∈ Subgroup.closure {dD.uv, dD.t, dD.u}, p⁻¹ * y * p = (dD.c : G) ^ 2 ^ (m - 1)) ∨
        ∃ g ∈ dD.L, g⁻¹ * y * g = (dD.a : G) ^ 2 ^ m := by
  intro y hy h2 h1
  have hm1 : 1 ≤ m := by omega
  obtain ⟨ε, hε, rfl⟩ := dD.t100_eq_om_of_mul_self hm1 hy h2
  rw [dD.t100_c_pow, dD.t100_a_pow]
  have hW : ∀ x ∈ ({dD.uv, dD.t, dD.u} : Set G), x ∈ Subgroup.closure {dD.uv, dD.t, dD.u} :=
    fun x hx => Subgroup.subset_closure hx
  have hconj_uv := dD.conj_ofTorus dD.uv_mem dD.uv_conj
  have hconj_t := dD.conj_ofTorus dD.t_mem dD.t_conj
  have hconj_ρ := dD.conj_ofTorus dD.ρ_mem dD.ρ_conj
  have hε0 : ¬ (ε 0 = 0 ∧ ε 1 = 0 ∧ ε 2 = 0) := by
    rintro ⟨h0, h1', h2'⟩
    apply h1
    rw [← dD.ofTorus_zero, ← om100_zero]
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
    rw [mul_inv_rev, show (dD.ρ⁻¹ * dD.ρ⁻¹ * dD.ofTorus (om100 m ![0, 0, 1]) * (dD.ρ * dD.ρ)) =
      dD.ρ⁻¹ * (dD.ρ⁻¹ * dD.ofTorus (om100 m ![0, 0, 1]) * dD.ρ) * dD.ρ by group, hconj_ρ,
      hconj_ρ, t100_φρ_om hm1, t100_φρ_om hm1]
    exact congrArg dD.ofTorus ((om100_eq_iff hm1 _ _).mpr (by decide))
  · right
    exact ⟨1, one_mem _, by simp⟩
  · right
    refine ⟨dD.ρ, dD.ρ_mem_L, ?_⟩
    rw [hconj_ρ, t100_φρ_om hm1]
    exact congrArg dD.ofTorus ((om100_eq_iff hm1 _ _).mpr (by decide))
  · left
    exact ⟨1, one_mem _, by simp⟩
  · left
    refine ⟨dD.uv * dD.t, mul_mem (hW _ (by simp)) (hW _ (by simp)), ?_⟩
    rw [mul_inv_rev, show dD.t⁻¹ * dD.uv⁻¹ * dD.ofTorus (om100 m ![1, 0, 1]) * (dD.uv * dD.t) =
      dD.t⁻¹ * (dD.uv⁻¹ * dD.ofTorus (om100 m ![1, 0, 1]) * dD.uv) * dD.t by group, hconj_uv,
      hconj_t, t100_φuv_om hm1, t100_φt_om hm1]
    exact congrArg dD.ofTorus ((om100_eq_iff hm1 _ _).mpr (by decide))
  · left
    refine ⟨dD.t, hW _ (by simp), ?_⟩
    rw [hconj_t, t100_φt_om hm1]
    exact congrArg dD.ofTorus ((om100_eq_iff hm1 _ _).mpr (by decide))
  · left
    refine ⟨dD.uv, hW _ (by simp), ?_⟩
    rw [hconj_uv, t100_φuv_om hm1]
    exact congrArg dD.ofTorus ((om100_eq_iff hm1 _ _).mpr (by decide))

theorem t100_comm_z (hm : 1 ≤ m) {v : Torus (StrothTypeIndex.t100 m).k} {i j l : Bool}
    (h : dD.ofTorus v * dD.d8 i j l * (dD.c : G) ^ 2 ^ (m - 1) =
      (dD.c : G) ^ 2 ^ (m - 1) * (dD.ofTorus v * dD.d8 i j l)) : i = false ∧ j = false := by
  rw [dD.t100_c_pow, nf_commute_iff] at h
  cases i <;> cases j <;> cases l <;>
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, t100_φuv_om hm, t100_φt_om hm, t100_φu_om, om100_eq_iff hm] at h <;>
    first
    | exact ⟨rfl, rfl⟩
    | exact absurd h (by decide)

theorem t100_h4 (hm : 2 ≤ m) :
    ∀ y ∈ Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u},
      y * (dD.c : G) ^ 2 ^ (m - 1) = (dD.c : G) ^ 2 ^ (m - 1) * y →
        y ^ 2 ^ (m - 1) ≠ (dD.c : G) ^ 2 ^ (m - 1) := by
  intro y hy hcomm hpow
  have hm1 : 1 ≤ m := by omega
  have hk : 1 ≤ (StrothTypeIndex.t100 m).k 0 := hm1
  obtain ⟨v, i, j, l, hv, rfl⟩ := (dD.mem_S₁_iff hk (t100_parity hm1)).mp hy
  obtain ⟨rfl, rfl⟩ := dD.t100_comm_z hm1 hcomm
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
  rw [Torus.ofInt_apply, even_intCast_iff hk] at hv
  obtain ⟨r, hr⟩ := hv
  have hd8 : dD.d8 (l && false) false false = 1 := by rw [Bool.and_false, d8_fff]
  rw [pow_two_pow_eq_mul_self _ (by omega : 1 ≤ m - 1), nf_mul_self, hd8, mul_one,
    ← ofTorus_nsmul, dD.t100_c_pow] at hpow
  have hpow' := dD.ofTorus_inj hpow
  have hu : (StrothTypeIndex.t100 m).action.d8Act false false l (Torus.ofInt _ x) =
      Torus.ofInt _ ![x 0, if l then x 2 else x 1, if l then x 1 else x 2] := by
    cases l <;> simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte,
      AddMonoidHom.comp_apply, AddMonoidHom.id_apply, t100_φu]
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [hu, ← Torus.ofInt_add, ← natCast_zsmul, ← Torus.ofInt_zsmul, om100_c,
    t100_ofInt_eq_iff] at hpow'
  obtain ⟨h0, -, -⟩ := hpow'
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero] at h0
  rw [hr] at h0
  push_cast at h0
  exact not_two_pow_dvd_aux (n := m) hm r (by rw [one_mul]; exact h0)

theorem t100_odd_of_not_mem (hm1 : 1 ≤ m) {x : Fin 3 → ℤ} {i j l : Bool}
    (hy1 : dD.ofTorus (Torus.ofInt _ x) * dD.d8 i j l ∉
      Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u}) :
    x 0 % 2 = 1 := by
  have hk : 1 ≤ (StrothTypeIndex.t100 m).k 0 := hm1
  have hv : ¬ Even ((Torus.ofInt (StrothTypeIndex.t100 m).k x) 0) := fun h =>
    hy1 ((dD.mem_S₁_iff hk (t100_parity hm1)).mpr ⟨_, i, j, l, h, rfl⟩)
  rw [Torus.ofInt_apply, even_intCast_iff hk, Int.not_even_iff] at hv
  exact hv

theorem t100_om_comm {v : Torus (StrothTypeIndex.t100 m).k} {i j l : Bool} {ε : Fin 3 → ℤ}
    (h : (StrothTypeIndex.t100 m).action.d8Act i j l (om100 m ε) = om100 m ε) :
    dD.ofTorus (om100 m ε) * (dD.ofTorus v * dD.d8 i j l) =
      dD.ofTorus v * dD.d8 i j l * dD.ofTorus (om100 m ε) :=
  ((dD.nf_commute_iff v (om100 m ε) i j l).mpr h).symm

theorem t100_h6 (hm : 2 ≤ m) :
    ∀ y : G, y * dD.uv ∈ D → y * y = 1 → ∃ E : Subgroup G,
      E ≤ Subgroup.centralizer {y} ∧ (∀ e ∈ E, e * e = 1) ∧ Nat.card E = 16 := by
  intro y hy hyy
  have hm1 : 1 ≤ m := by omega
  have hF := t100_faithful (m := m) hm1
  obtain ⟨v, hv⟩ := dD.exists_ofTorus hy
  have hyv : y = dD.ofTorus v * dD.d8 true false false := by
    rw [d8_tff, ← hv, mul_assoc, dD.uv_sq, mul_one]
  subst hyv
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
  have hsq := hyy
  rw [nf_mul_self, Bool.and_false, d8_fff, mul_one, ofTorus_eq_one_iff] at hsq
  simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
    AddMonoidHom.id_apply, t100_φuv] at hsq
  rw [← Torus.ofInt_add, t100_ofInt_eq_zero_iff] at hsq
  obtain ⟨-, hsq1, -⟩ := hsq
  simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero] at hsq1
  set w : Fin 3 → ℤ := ![0, -x 2, 0] with hw
  have hdecide : ∀ (ε ε' : Fin 3 → ℤ), (∀ i, ε i ≡ ε' i [ZMOD 2]) → om100 m ε = om100 m ε' :=
    fun ε ε' h => (om100_eq_iff hm1 ε ε').mpr h
  refine Stroth42Core.exists_E16 (H := D) (x₁ := dD.ofTorus (om100 m ![0, 1, 0]))
    (x₂ := dD.ofTorus (om100 m ![0, 0, 1]))
    (y₃ := dD.ofTorus (Torus.ofInt _ x) * dD.d8 true false false)
    (y₄ := dD.ofTorus (Torus.ofInt _ w) * dD.d8 false true false)
    (dD.ofTorus_mem _) (dD.ofTorus_mem _) ?_ ?_ hyy ?_ (dD.ofTorus_comm _ _) ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?_
  · rw [ofTorus_mul_self, om100_add_self hm1, ofTorus_zero]
  · rw [ofTorus_mul_self, om100_add_self hm1, ofTorus_zero]
  · rw [nf_mul_self, Bool.and_true, d8_fff, mul_one, ofTorus_eq_one_iff]
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, t100_φt, ← Torus.ofInt_add]
    rw [← Torus.ofInt_zero]
    congr 1
    funext i
    fin_cases i <;> simp [hw]
  · refine dD.t100_om_comm ?_
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, t100_φuv_om hm1]
    exact hdecide _ _ (by decide)
  · refine dD.t100_om_comm ?_
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, t100_φt_om hm1]
    exact hdecide _ _ (by decide)
  · refine dD.t100_om_comm ?_
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, t100_φuv_om hm1]
    exact hdecide _ _ (by decide)
  · refine dD.t100_om_comm ?_
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, t100_φt_om hm1]
    exact hdecide _ _ (by decide)
  · rw [nf_mul_nf, nf_mul_nf]
    congr 1
    congr 1
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, t100_φuv, t100_φt, ← Torus.ofInt_add]
    rw [t100_ofInt_eq_iff]
    simp only [hw, Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    refine ⟨⟨0, by ring⟩, ?_, ⟨0, by ring⟩⟩
    obtain ⟨c, hc⟩ := hsq1
    exact ⟨-c, by linear_combination -hc⟩
  · rw [Ne, ofTorus_eq_one_iff, ← om100_zero, om100_eq_iff hm1]
    decide
  · rw [Ne, ofTorus_eq_one_iff, ← om100_zero, om100_eq_iff hm1]
    decide
  · rw [Ne, dD.ofTorus_inj.eq_iff, om100_eq_iff hm1]
    decide
  · exact dD.d8_not_mem hF (by decide) _
  · exact dD.d8_not_mem hF (by decide) _
  · rw [nf_mul_nf]
    exact dD.d8_not_mem hF (by decide) _
  · refine dD.t100_om_comm ?_
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, t100_φuv_om hm1]
    exact hdecide _ _ (by decide)
  · refine dD.t100_om_comm ?_
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, t100_φuv_om hm1]
    exact hdecide _ _ (by decide)
  · rw [nf_mul_nf, nf_mul_nf]
    congr 1
    congr 1
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, t100_φuv, t100_φt, ← Torus.ofInt_add]
    rw [t100_ofInt_eq_iff]
    simp only [hw, Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    refine ⟨⟨0, by ring⟩, ?_, ⟨0, by ring⟩⟩
    obtain ⟨c, hc⟩ := hsq1
    exact ⟨c, by linear_combination hc⟩

theorem uvt_mul_uvt : dD.uv * dD.t * (dD.uv * dD.t) = 1 := by
  rw [mul_assoc, ← mul_assoc dD.t, ← dD.uv_comm_t, mul_assoc, dD.t_sq, mul_one, dD.uv_sq]

theorem t100_h6' (hm : 2 ≤ m) :
    ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u},
      y ∉ Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u} →
      y * y = 1 → ∃ E : Subgroup G,
        E ≤ Subgroup.centralizer {y} ∧ (∀ e ∈ E, e * e = 1) ∧ Nat.card E = 16 := by
  intro y hy hy1 hyy
  have hm1 : 1 ≤ m := by omega
  obtain ⟨v, i, j, l, rfl⟩ := dD.mem_sup_iff.mp hy
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
  have hodd := dD.t100_odd_of_not_mem hm1 hy1
  have h6 := dD.t100_h6 hm
  have hsq := hyy
  rw [nf_mul_self] at hsq
  cases i <;> cases j <;> cases l
  ·
    exfalso
    rw [Bool.and_self, d8_fff, mul_one, ofTorus_eq_one_iff] at hsq
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, ← Torus.ofInt_add, t100_ofInt_eq_zero_iff] at hsq
    have h4 := two_pow_dvd_four hm hsq.1
    simp only [Pi.add_apply] at h4
    omega
  ·
    exfalso
    rw [Bool.true_and, d8_fff, mul_one, ofTorus_eq_one_iff] at hsq
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, t100_φu, ← Torus.ofInt_add, t100_ofInt_eq_zero_iff] at hsq
    have h4 := two_pow_dvd_four hm hsq.1
    simp only [Pi.add_apply, Matrix.cons_val_zero] at h4
    omega
  ·
    exact dD.exists_E16_of_mem_t_coset h6
      (by rw [d8_ftf, mul_assoc, dD.t_sq, mul_one]; exact dD.ofTorus_mem _) hyy
  ·
    exfalso
    rw [Bool.and_self, d8_tff] at hsq
    have hnot := dD.d8_not_mem (t100_faithful hm1) (i := true) (j := false) (l := false)
      (by decide) (Torus.ofInt (StrothTypeIndex.t100 m).k x +
        (StrothTypeIndex.t100 m).action.d8Act false true true (Torus.ofInt _ x))
    rw [d8_tff, hsq] at hnot
    exact hnot (one_mem _)
  ·
    exact h6 _ (by rw [d8_tff, mul_assoc, dD.uv_sq, mul_one]; exact dD.ofTorus_mem _) hyy
  ·
    exfalso
    rw [Bool.true_and, d8_fff, mul_one, ofTorus_eq_one_iff] at hsq
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, t100_φu, t100_φuv, ← Torus.ofInt_add,
      t100_ofInt_eq_zero_iff] at hsq
    obtain ⟨-, h1, h2⟩ := hsq
    have h1' := two_pow_dvd_eight (by omega : 3 ≤ m + 1) h1
    have h2' := two_pow_dvd_eight (by omega : 3 ≤ m + 1) h2
    simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at h1' h2'
    omega
  ·
    exact dD.exists_E16_of_mem_uvt_coset h6
      (by rw [d8_ttf, mul_assoc, dD.uvt_mul_uvt, mul_one]; exact dD.ofTorus_mem _) hyy
  ·
    exfalso
    rw [Bool.and_self, d8_tff] at hsq
    have hnot := dD.d8_not_mem (t100_faithful hm1) (i := true) (j := false) (l := false)
      (by decide) (Torus.ofInt (StrothTypeIndex.t100 m).k x +
        (StrothTypeIndex.t100 m).action.d8Act true true true (Torus.ofInt _ x))
    rw [d8_tff, hsq] at hnot
    exact hnot (one_mem _)

theorem t100_four_dvd_of_pow (hm : 2 ≤ m) {y : G} {w : Fin 3 → ℤ}
    (hsq : y * y = dD.ofTorus (Torus.ofInt _ w)) (h1 : y ^ 2 ^ (m - 1) = 1) : 4 ∣ w 0 := by
  rw [dD.pow_two_pow_of_mul_self hsq (by omega), ofTorus_eq_one_iff, ← natCast_zsmul,
    ← Torus.ofInt_zsmul, t100_ofInt_eq_zero_iff] at h1
  obtain ⟨h0, -, -⟩ := h1
  simp only [Pi.smul_apply, smul_eq_mul] at h0
  push_cast at h0
  exact four_dvd_of_two_pow_dvd_mul (by omega : m - 1 - 1 + 2 = m) h0

theorem t100_pow_ne_c₁ (hm : 1 ≤ m) {y : G} {w : Fin 3 → ℤ}
    (hsq : y * y = dD.ofTorus (Torus.ofInt _ w)) (hw : w 1 = w 0 ∨ w 2 = w 0) {n : ℕ}
    (hn : 1 ≤ n) : y ^ 2 ^ n ≠ (dD.c : G) ^ 2 ^ (m - 1) := by
  intro h
  rw [dD.pow_two_pow_of_mul_self hsq hn, dD.t100_c_pow, om100_c, ← natCast_zsmul,
    ← Torus.ofInt_zsmul] at h
  obtain ⟨h0, h1, h2⟩ := (t100_ofInt_eq_iff _ _).mp (dD.ofTorus_inj h)
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
  rcases hw with hw | hw
  · rw [hw] at h1
    exact not_dvd_pow_pred_sub hm h0 h1
  · rw [hw] at h2
    exact not_dvd_pow_pred_sub hm h0 h2

theorem t100_pow_ne_c₁_of_odd (hm : 1 ≤ m) {y : G} {w : Fin 3 → ℤ}
    (hsq : y * y = dD.ofTorus (Torus.ofInt _ w)) (hw : w 1 % 2 = 1) {n : ℕ} (hn : 1 ≤ n) :
    y ^ 2 ^ n ≠ (dD.c : G) ^ 2 ^ (m - 1) := by
  intro h
  rw [dD.pow_two_pow_of_mul_self hsq hn, dD.t100_c_pow, om100_c, ← natCast_zsmul,
    ← Torus.ofInt_zsmul] at h
  obtain ⟨h0, h1, -⟩ := (t100_ofInt_eq_iff _ _).mp (dD.ofTorus_inj h)
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h0 h1
  push_cast at h0 h1
  exact not_dvd_pow_pred_sub_of_odd hm hw h0 h1

theorem t100_h8 (hm : 2 ≤ m) :
    ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u},
      y ∉ Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u} →
      ∀ l : ℕ, 1 ≤ l → y ^ 2 ^ l = (dD.c : G) ^ 2 ^ (m - 1) → y ^ 2 ^ (m - 1) ≠ 1 := by
  intro y hy hy1 n hn hz
  have hm1 : 1 ≤ m := by omega
  obtain ⟨v, i, j, l, rfl⟩ := dD.mem_sup_iff.mp hy
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
  have hodd := dD.t100_odd_of_not_mem hm1 hy1
  have hz1 : (dD.c : G) ^ 2 ^ (m - 1) ≠ 1 := by
    rw [dD.t100_c_pow, Ne, ofTorus_eq_one_iff, ← om100_zero, om100_eq_iff hm1]
    decide
  have hlt : ∀ i : Bool, dD.ofTorus (Torus.ofInt _ x) * dD.d8 i true true *
      (dD.ofTorus (Torus.ofInt _ x) * dD.d8 i true true) *
      (dD.ofTorus (Torus.ofInt _ x) * dD.d8 i true true *
        (dD.ofTorus (Torus.ofInt _ x) * dD.d8 i true true)) = 1 := by
    intro i
    rw [dD.nf_mul_self_of_true _ (by rfl), nf_mul_self, Bool.and_false, d8_fff, mul_one,
      ofTorus_eq_one_iff]
    cases i <;>
      simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte,
        AddMonoidHom.comp_apply, AddMonoidHom.id_apply, t100_φuv, t100_φt, t100_φu,
        ← Torus.ofInt_add] <;>
      rw [← Torus.ofInt_zero] <;> congr 1 <;> funext i <;> fin_cases i <;>
      simp [Matrix.vecHead, Matrix.vecTail] <;> ring
  have hlt' : ∀ i : Bool, n ≥ 1 →
      (dD.ofTorus (Torus.ofInt _ x) * dD.d8 i true true) ^ 2 ^ n ≠
        (dD.c : G) ^ 2 ^ (m - 1) := by
    intro i hn' hz'
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · have hn1 : n = 1 := by omega
      subst hn1
      rw [pow_one, sq, dD.nf_mul_self_of_true _ (by rfl)] at hz'
      have hnot := dD.d8_not_mem (t100_faithful hm1) (i := true) (j := false) (l := false)
        (by decide) (Torus.ofInt (StrothTypeIndex.t100 m).k x +
          (StrothTypeIndex.t100 m).action.d8Act i true true (Torus.ofInt _ x))
      rw [hz'] at hnot
      exact hnot (pow_mem dD.c.2 _)
    · rw [pow_two_pow_eq_mul_self _ hn', pow_two_pow_eq_mul_self _ (by omega : 1 ≤ n - 1),
        hlt i, one_pow] at hz'
      exact hz1 hz'.symm
  cases i <;> cases j <;> cases l
  ·
    have hsq0 := dD.nf_mul_self_of_false (Torus.ofInt _ x) (i := false) (j := false)
      (l := false) rfl
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, ← Torus.ofInt_add] at hsq0
    intro h1
    have h4 := dD.t100_four_dvd_of_pow hm hsq0 h1
    simp only [Pi.add_apply] at h4
    omega
  ·
    have hsq0 := dD.nf_mul_self_of_false (Torus.ofInt _ x) (i := false) (j := false)
      (l := true) rfl
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, t100_φu, ← Torus.ofInt_add] at hsq0
    intro h1
    have h4 := dD.t100_four_dvd_of_pow hm hsq0 h1
    simp only [Pi.add_apply, Matrix.cons_val_zero] at h4
    omega
  ·
    exfalso
    have hsq0 := dD.nf_mul_self_of_false (Torus.ofInt _ x) (i := false) (j := true)
      (l := false) rfl
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, t100_φt, ← Torus.ofInt_add] at hsq0
    refine dD.t100_pow_ne_c₁ hm1 hsq0 (Or.inl ?_) hn hz
    simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    ring
  · exact absurd hz (hlt' false hn)
  ·
    exfalso
    have hsq0 := dD.nf_mul_self_of_false (Torus.ofInt _ x) (i := true) (j := false)
      (l := false) rfl
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, t100_φuv, ← Torus.ofInt_add] at hsq0
    refine dD.t100_pow_ne_c₁ hm1 hsq0 (Or.inl ?_) hn hz
    simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    ring
  ·
    have hsq0 := dD.nf_mul_self_of_false (Torus.ofInt _ x) (i := true) (j := false)
      (l := true) rfl
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, t100_φu, t100_φuv, ← Torus.ofInt_add] at hsq0
    by_cases hpar : (x 1 + x 2) % 2 = 0
    · intro h1
      have h4 := dD.t100_four_dvd_of_pow hm hsq0 h1
      simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons] at h4
      omega
    · exfalso
      refine dD.t100_pow_ne_c₁_of_odd hm1 hsq0 ?_ hn hz
      simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      omega
  ·
    exfalso
    have hsq0 := dD.nf_mul_self_of_false (Torus.ofInt _ x) (i := true) (j := true)
      (l := false) rfl
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, t100_φuv, t100_φt, ← Torus.ofInt_add] at hsq0
    refine dD.t100_pow_ne_c₁ hm1 hsq0 (Or.inr ?_) hn hz
    simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    ring
  · exact absurd hz (hlt' true hn)

theorem t100_mem_CSz (hm1 : 1 ≤ m) {y : G}
    (hy : y ∈ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}) ⊓
      Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)}) :
    ∃ (v : Torus (StrothTypeIndex.t100 m).k) (l : Bool), y = dD.ofTorus v * dD.d8 false false l := by
  obtain ⟨hyS, hyC⟩ := Subgroup.mem_inf.mp hy
  obtain ⟨v, i, j, l, rfl⟩ := dD.mem_sup_iff.mp hyS
  rw [Subgroup.mem_centralizer_iff] at hyC
  have hc := hyC _ (Set.mem_singleton _)
  obtain ⟨rfl, rfl⟩ := dD.t100_comm_z hm1 hc.symm
  exact ⟨v, l, rfl⟩

theorem t100_mem_CSz_of_not_mem (hm1 : 1 ≤ m) {y : G}
    (hy : y ∈ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}) ⊓
      Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)}) (hyD : y ∉ D) :
    ∃ v : Torus (StrothTypeIndex.t100 m).k, y = dD.ofTorus v * dD.d8 false false true := by
  obtain ⟨v, l, rfl⟩ := dD.t100_mem_CSz hm1 hy
  cases l
  · exact absurd (by rw [d8_fff, mul_one]; exact dD.ofTorus_mem v) hyD
  · exact ⟨v, rfl⟩

theorem t100_h7 (hm : 2 ≤ m) :
    ∀ E : Subgroup G, E ≤ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}) ⊓
      Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)} → (∀ e ∈ E, e * e = 1) →
        Nat.card E ≠ 16 := by
  intro E hE hinv hcard
  have hm1 : 1 ≤ m := by omega
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    have h1 := inv_eq_of_mul_eq_one_right (hinv a ha)
    have h2 := inv_eq_of_mul_eq_one_right (hinv b hb)
    have h3 := inv_eq_of_mul_eq_one_right (hinv _ (mul_mem ha hb))
    calc a * b = (a * b)⁻¹ := h3.symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [h1, h2]
  have hD1 : ∀ e ∈ E, e ∈ D → ∃ a b c : Bool,
      e = dD.ofTorus (om100 m ![(a.toNat : ℤ), b.toNat, c.toNat]) := by
    intro e he heD
    obtain ⟨ε, hε, rfl⟩ := dD.t100_eq_om_of_mul_self hm1 heD (hinv e he)
    refine ⟨decide (ε 0 = 1), decide (ε 1 = 1), decide (ε 2 = 1), ?_⟩
    congr 2
    funext i
    fin_cases i <;> simp [bool_toNat_cast_eq (hε _)]
  have h8 : Nat.card (Bool × Bool × Bool) = 8 := by simp [Nat.card_eq_fintype_card]
  by_cases hD : ∃ e₀ ∈ E, e₀ ∉ D
  · obtain ⟨e₀, he₀, he₀D⟩ := hD
    obtain ⟨v₀, hv₀⟩ := dD.t100_mem_CSz_of_not_mem hm1 (hE he₀) he₀D
    have hfix : ∀ d ∈ E, d ∈ D → ∃ a b : Bool,
        d = dD.ofTorus (om100 m ![(a.toNat : ℤ), b.toNat, b.toNat]) := by
      intro d hd hdD
      obtain ⟨a, b, c, rfl⟩ := hD1 d hd hdD
      have hc := hcomm _ hd _ he₀
      rw [hv₀] at hc
      have hω := (dD.nf_commute_iff v₀ _ false false true).mp hc.symm
      simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
        AddMonoidHom.id_apply, t100_φu_om, om100_eq_iff hm1] at hω
      have h1 := hω 1
      have hbc : c = b := by
        revert h1
        cases a <;> cases b <;> cases c <;> decide
      exact ⟨a, b, by rw [hbc]⟩
    let f : Bool × Bool × Bool → G := fun w =>
      dD.ofTorus (om100 m ![(w.2.1.toNat : ℤ), w.2.2.toNat, w.2.2.toNat]) *
        (if w.1 then e₀ else 1)
    have hcov : ∀ e ∈ E, ∃ w, f w = e := by
      intro e he
      by_cases heD : e ∈ D
      · obtain ⟨a, b, hd⟩ := hfix e he heD
        exact ⟨(false, a, b), by simp [f, hd]⟩
      · obtain ⟨v, hv⟩ := dD.t100_mem_CSz_of_not_mem hm1 (hE he) heD
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
      dD.ofTorus (om100 m ![(w.1.toNat : ℤ), w.2.1.toNat, w.2.2.toNat])
    have hcov : ∀ e ∈ E, ∃ w, f w = e := by
      intro e he
      obtain ⟨a, b, c, hd⟩ := hD1 e he (hD e he)
      exact ⟨(a, b, c), hd.symm⟩
    have hle := Stroth42Core.natCard_le_of_subset_range f hcov
    rw [hcard, h8] at hle
    omega

theorem t100_h9 (hm : 2 ≤ m) :
    ∀ X : Subgroup G, X ≤ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}) ⊓
      Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)} → IsMulCommutative X →
        Nat.card X = Nat.card D → X = D := by
  intro X hX hab hcard
  have hm1 : 1 ≤ m := by omega
  have hDcard : Nat.card D = 2 ^ (m + (m + 1) + (m + 1)) := dD.card
  by_cases hD : ∃ x₀ ∈ X, x₀ ∉ D
  · exfalso
    obtain ⟨x₀, hx₀, hx₀D⟩ := hD
    obtain ⟨v₀, hv₀⟩ := dD.t100_mem_CSz_of_not_mem hm1 (hX hx₀) hx₀D
    have hcomm : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := fun a ha b hb =>
      congrArg Subtype.val (hab.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    haveI : NeZero (2 ^ m) := ⟨by positivity⟩
    haveI : NeZero (2 ^ (m + 1)) := ⟨by positivity⟩
    have hfix : ∀ d ∈ X, d ∈ D → ∃ (p : ZMod (2 ^ m)) (q : ZMod (2 ^ (m + 1))),
        d = dD.ofTorus (Torus.ofInt _ ![(p.val : ℤ), (q.val : ℤ), (q.val : ℤ)]) := by
      intro d hd hdD
      obtain ⟨v, rfl⟩ := dD.exists_ofTorus hdD
      have hc := hcomm _ hd _ hx₀
      rw [hv₀] at hc
      have hfv := (dD.nf_commute_iff v₀ v false false true).mp hc.symm
      simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
        AddMonoidHom.id_apply] at hfv
      obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
      rw [t100_φu, t100_ofInt_eq_iff] at hfv
      obtain ⟨-, h1, -⟩ := hfv
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at h1
      refine ⟨((x 0 : ℤ) : ZMod (2 ^ m)), ((x 1 : ℤ) : ZMod (2 ^ (m + 1))), ?_⟩
      congr 1
      rw [t100_ofInt_eq_iff]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, ZMod.val_intCast]
      have hm' : ((2 ^ m : ℕ) : ℤ) = 2 ^ m := by push_cast; rfl
      have hm'' : ((2 ^ (m + 1) : ℕ) : ℤ) = 2 ^ (m + 1) := by push_cast; rfl
      rw [hm', hm'']
      refine ⟨⟨-(x 0 / 2 ^ m), by rw [Int.emod_def]; ring⟩, ⟨-(x 1 / 2 ^ (m + 1)), by
        rw [Int.emod_def]; ring⟩, ?_⟩
      obtain ⟨c, hc⟩ := h1
      exact ⟨c - x 1 / 2 ^ (m + 1), by rw [Int.emod_def]; linear_combination hc⟩
    let f : Bool × ZMod (2 ^ m) × ZMod (2 ^ (m + 1)) → G := fun w =>
      dD.ofTorus (Torus.ofInt _ ![(w.2.1.val : ℤ), (w.2.2.val : ℤ), (w.2.2.val : ℤ)]) *
        (if w.1 then x₀ else 1)
    have hcov : ∀ e ∈ X, ∃ w, f w = e := by
      intro e he
      by_cases heD : e ∈ D
      · obtain ⟨p, q, hd⟩ := hfix e he heD
        exact ⟨(false, p, q), by simp [f, hd]⟩
      · obtain ⟨v, hv⟩ := dD.t100_mem_CSz_of_not_mem hm1 (hX he) heD
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
    rw [h2, show 2 * (2 ^ m * 2 ^ (m + 1)) = 2 ^ (m + m + 2) by ring] at hle
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
    omega
  · simp only [not_exists, not_and, not_not] at hD
    haveI : Finite D := Nat.finite_of_card_ne_zero (by rw [hDcard]; positivity)
    exact Subgroup.eq_of_le_of_card_ge (fun x hx => hD x hx) hcard.ge

end StrothWeakTypeData

end CFSG.CGT.Stroth77
