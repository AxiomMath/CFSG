module

public import CFSG.CGT.Stroth77.Stroth34Defs
public import CFSG.CGT.Stroth77.Section44Core

public section

namespace CFSG.CGT.Stroth77

open Matrix

namespace Stroth34T201Natural

@[expose] def theta₁₁ (m : ℕ) : IntMat :=
  ofCols ![1, 2 ^ (m + 1), 2 ^ (m + 1)] ![2 ^ (m - 1), 1 + 2 ^ (m + 1), 2 ^ (m + 1)]
    ![2 ^ (m - 1), 2 ^ (m + 1), 1 + 2 ^ (m + 1)]

@[expose] def theta₁₂ (m : ℕ) : IntMat :=
  ofCols ![1, 2 ^ (m + 1), 0] ![0, 1, 0] ![2 ^ (m - 1), 2 ^ (m + 1), 1 + 2 ^ (m + 1)]

@[expose] def theta₂₁ (m : ℕ) : IntMat :=
  ofCols ![1, 2 ^ (m + 1), 2 ^ (m + 1)] ![2 ^ (m - 1), 1, 0] ![2 ^ (m - 1), 0, 1]

@[expose] def theta₂₂ (m : ℕ) : IntMat :=
  ofCols ![1, 2 ^ (m + 1), 0] ![0, 1, 0] ![2 ^ (m - 1), 0, 1 + 2 ^ (m + 1)]

theorem theta₁₁_mulVec (m : ℕ) (x : Fin 3 → ℤ) :
    theta₁₁ m *ᵥ x = ![x 0 + 2 ^ (m - 1) * x 1 + 2 ^ (m - 1) * x 2,
      2 ^ (m + 1) * x 0 + (1 + 2 ^ (m + 1)) * x 1 + 2 ^ (m + 1) * x 2,
      2 ^ (m + 1) * x 0 + 2 ^ (m + 1) * x 1 + (1 + 2 ^ (m + 1)) * x 2] := by
  rw [theta₁₁, ofCols_mulVec]
  funext i
  fin_cases i <;> simp <;> ring

theorem theta₁₂_mulVec (m : ℕ) (x : Fin 3 → ℤ) :
    theta₁₂ m *ᵥ x = ![x 0 + 2 ^ (m - 1) * x 2, 2 ^ (m + 1) * x 0 + x 1 + 2 ^ (m + 1) * x 2,
      (1 + 2 ^ (m + 1)) * x 2] := by
  rw [theta₁₂, ofCols_mulVec]
  funext i
  fin_cases i <;> simp <;> ring

theorem theta₂₁_mulVec (m : ℕ) (x : Fin 3 → ℤ) :
    theta₂₁ m *ᵥ x = ![x 0 + 2 ^ (m - 1) * x 1 + 2 ^ (m - 1) * x 2, 2 ^ (m + 1) * x 0 + x 1,
      2 ^ (m + 1) * x 0 + x 2] := by
  rw [theta₂₁, ofCols_mulVec]
  funext i
  fin_cases i <;> simp <;> ring

theorem theta₂₂_mulVec (m : ℕ) (x : Fin 3 → ℤ) :
    theta₂₂ m *ᵥ x = ![x 0 + 2 ^ (m - 1) * x 2, 2 ^ (m + 1) * x 0 + x 1,
      (1 + 2 ^ (m + 1)) * x 2] := by
  rw [theta₂₂, ofCols_mulVec]
  funext i
  fin_cases i <;> simp <;> ring

theorem compat_theta₁₁ {m : ℕ} (hm : 2 ≤ m) : Compat (StrothTypeIndex.t201 m).k (theta₁₁ m) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
  refine Compat.of_witness (C := !![1, 2 ^ (j + 3), 2 ^ (j + 3); 2 ^ (j + 1), 1 + 2 ^ (j + 3),
    2 ^ (j + 3); 2 ^ (j + 1), 2 ^ (j + 3), 1 + 2 ^ (j + 3)]) fun i l => ?_
  fin_cases i <;> fin_cases l <;>
    simp [StrothTypeIndex.k, Type201.k, theta₁₁, ofCols_apply, show j + 2 - 1 = j + 1 from rfl,
      -mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring

theorem compat_theta₁₂ {m : ℕ} (hm : 2 ≤ m) : Compat (StrothTypeIndex.t201 m).k (theta₁₂ m) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
  refine Compat.of_witness (C := !![1, 0, 2 ^ (j + 3); 2 ^ (j + 1), 1, 2 ^ (j + 3);
    0, 0, 1 + 2 ^ (j + 3)]) fun i l => ?_
  fin_cases i <;> fin_cases l <;>
    simp [StrothTypeIndex.k, Type201.k, theta₁₂, ofCols_apply, show j + 2 - 1 = j + 1 from rfl,
      -mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring

theorem compat_theta₂₁ {m : ℕ} (hm : 2 ≤ m) : Compat (StrothTypeIndex.t201 m).k (theta₂₁ m) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
  refine Compat.of_witness (C := !![1, 2 ^ (j + 3), 2 ^ (j + 3); 2 ^ (j + 1), 1, 0;
    2 ^ (j + 1), 0, 1]) fun i l => ?_
  fin_cases i <;> fin_cases l <;>
    simp [StrothTypeIndex.k, Type201.k, theta₂₁, ofCols_apply, show j + 2 - 1 = j + 1 from rfl,
      -mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring

theorem compat_theta₂₂ {m : ℕ} (hm : 2 ≤ m) : Compat (StrothTypeIndex.t201 m).k (theta₂₂ m) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
  refine Compat.of_witness (C := !![1, 0, 2 ^ (j + 3); 2 ^ (j + 1), 1, 0;
    0, 0, 1 + 2 ^ (j + 3)]) fun i l => ?_
  fin_cases i <;> fin_cases l <;>
    simp [StrothTypeIndex.k, Type201.k, theta₂₂, ofCols_apply, show j + 2 - 1 = j + 1 from rfl,
      -mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring

theorem theta₁₁_invol {m : ℕ} (hm : 2 ≤ m) (v : Torus (StrothTypeIndex.t201 m).k) :
    matAct _ (theta₁₁ m) (compat_theta₁₁ hm) (matAct _ (theta₁₁ m) (compat_theta₁₁ hm) v) = v := by
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
  rw [matAct_ofInt, matAct_ofInt, theta₁₁_mulVec, theta₁₁_mulVec, Stroth44Core.t201_ofInt_eq_iff]
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
  simp only [show j + 2 - 1 = j + 1 from rfl, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  refine ⟨⟨-2 ^ (j + 3) * x 0 - 2 ^ (j + 3) * x 1 - 2 ^ (j + 3) * x 2 - x 1 - x 2, by ring⟩,
    ⟨-2 ^ (j + 3) * x 0 - 9 * 2 ^ j * x 1 - 9 * 2 ^ j * x 2 - x 0 - x 1 - x 2, by ring⟩,
    ⟨-2 ^ (j + 3) * x 0 - 9 * 2 ^ j * x 1 - 9 * 2 ^ j * x 2 - x 0 - x 1 - x 2, by ring⟩⟩

theorem theta₁₂_invol {m : ℕ} (hm : 2 ≤ m) (v : Torus (StrothTypeIndex.t201 m).k) :
    matAct _ (theta₁₂ m) (compat_theta₁₂ hm) (matAct _ (theta₁₂ m) (compat_theta₁₂ hm) v) = v := by
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
  rw [matAct_ofInt, matAct_ofInt, theta₁₂_mulVec, theta₁₂_mulVec, Stroth44Core.t201_ofInt_eq_iff]
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
  simp only [show j + 2 - 1 = j + 1 from rfl, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  refine ⟨⟨-4 * 2 ^ j * x 2 - x 2, by ring⟩, ⟨-5 * 2 ^ j * x 2 - x 0 - x 2, by ring⟩,
    ⟨-4 * 2 ^ j * x 2 - x 2, by ring⟩⟩

theorem theta₂₁_invol {m : ℕ} (hm : 2 ≤ m) (v : Torus (StrothTypeIndex.t201 m).k) :
    matAct _ (theta₂₁ m) (compat_theta₂₁ hm) (matAct _ (theta₂₁ m) (compat_theta₂₁ hm) v) = v := by
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
  rw [matAct_ofInt, matAct_ofInt, theta₂₁_mulVec, theta₂₁_mulVec, Stroth44Core.t201_ofInt_eq_iff]
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
  simp only [show j + 2 - 1 = j + 1 from rfl, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  refine ⟨⟨-2 ^ (j + 3) * x 0 - x 1 - x 2, by ring⟩, ⟨-2 ^ j * x 1 - 2 ^ j * x 2 - x 0, by ring⟩,
    ⟨-2 ^ j * x 1 - 2 ^ j * x 2 - x 0, by ring⟩⟩

theorem theta₂₂_invol {m : ℕ} (hm : 2 ≤ m) (v : Torus (StrothTypeIndex.t201 m).k) :
    matAct _ (theta₂₂ m) (compat_theta₂₂ hm) (matAct _ (theta₂₂ m) (compat_theta₂₂ hm) v) = v := by
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
  rw [matAct_ofInt, matAct_ofInt, theta₂₂_mulVec, theta₂₂_mulVec, Stroth44Core.t201_ofInt_eq_iff]
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
  simp only [show j + 2 - 1 = j + 1 from rfl, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  refine ⟨⟨-4 * 2 ^ j * x 2 - x 2, by ring⟩, ⟨-2 ^ j * x 2 - x 0, by ring⟩,
    ⟨-4 * 2 ^ j * x 2 - x 2, by ring⟩⟩

theorem torusDiag_e_invol (m : ℕ) (v : Torus (StrothTypeIndex.t201 m).k) :
    torusDiag _ ![1, 1 + 2 ^ (m + 1), 1 + 2 ^ (m + 1)]
      (torusDiag _ ![1, 1 + 2 ^ (m + 1), 1 + 2 ^ (m + 1)] v) = v := by
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
  rw [torusDiag_ofInt, torusDiag_ofInt, Stroth44Core.t201_ofInt_eq_iff]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  refine ⟨⟨0, by ring⟩, ⟨-(1 + 2 ^ m) * x 1, by ring⟩, ⟨-(1 + 2 ^ m) * x 2, by ring⟩⟩

section Group

variable {G : Type*} [Group G] {D : Subgroup G} {τ : StrothTypeIndex}
  (dD : StrothWeakTypeData D τ)

private theorem mul_ofTorus_of_conj {g : G} {F : Torus τ.k →+ Torus τ.k}
    (hg : ∀ v, g⁻¹ * dD.ofTorus v * g = dD.ofTorus (F v)) (hF : ∀ v, F (F v) = v)
    (v : Torus τ.k) : g * dD.ofTorus v = dD.ofTorus (F v) * g := by
  have h := hg (F v)
  rw [hF] at h
  rw [← h]
  group

private theorem conj_sq_eq {f g : G} {F Φ : Torus τ.k →+ Torus τ.k} {z s : Torus τ.k}
    (hf : ∀ v, f⁻¹ * dD.ofTorus v * f = dD.ofTorus (F v))
    (hg : ∀ v, g * dD.ofTorus v = dD.ofTorus (Φ v) * g)
    (hs : g * g = dD.ofTorus s) (hz : f⁻¹ * g * f = dD.ofTorus z * g) :
    F s = z + Φ z + s := by
  apply dD.ofTorus_inj
  calc dD.ofTorus (F s) = f⁻¹ * (g * g) * f := by rw [hs, hf]
    _ = (f⁻¹ * g * f) * (f⁻¹ * g * f) := by group
    _ = dD.ofTorus z * (g * dD.ofTorus z) * g := by rw [hz]; group
    _ = dD.ofTorus z * dD.ofTorus (Φ z) * (g * g) := by rw [hg]; group
    _ = dD.ofTorus (z + Φ z + s) := by rw [hs, dD.ofTorus_add, dD.ofTorus_add]

private theorem conj_conj_eq {f g : G} {F Φ : Torus τ.k →+ Torus τ.k} {z p : Torus τ.k}
    (hf : ∀ v, f⁻¹ * dD.ofTorus v * f = dD.ofTorus (F v))
    (hg : ∀ v, g * dD.ofTorus v = dD.ofTorus (Φ v) * g)
    (hp : f * f = dD.ofTorus p) (hz : f⁻¹ * g * f = dD.ofTorus z * g) :
    F z + z = -p + Φ p := by
  apply dD.ofTorus_inj
  apply mul_right_cancel (b := g)
  calc dD.ofTorus (F z + z) * g = (f⁻¹ * dD.ofTorus z * f) * (f⁻¹ * g * f) := by
        rw [hf, hz, dD.ofTorus_add, mul_assoc]
    _ = f⁻¹ * (dD.ofTorus z * g) * f := by group
    _ = f⁻¹ * (f⁻¹ * g * f) * f := by rw [hz]
    _ = (f * f)⁻¹ * g * (f * f) := by group
    _ = dD.ofTorus (-p) * (g * dD.ofTorus p) := by rw [hp, dD.ofTorus_neg, mul_assoc]
    _ = dD.ofTorus (-p + Φ p) * g := by rw [hg, dD.ofTorus_add, mul_assoc]

private theorem conj_conj_of_mul_self {u : G} (hu : u * u = 1) (g : G) :
    u⁻¹ * (u⁻¹ * g * u) * u = g := by
  rw [inv_eq_of_mul_eq_one_right hu]
  calc u * (u * g * u) * u = u * u * g * (u * u) := by group
    _ = g := by rw [hu, one_mul, mul_one]

private theorem theta₁_rels {u e f₁ f₂ : G} {U Φ F₁ F₂ : Torus τ.k →+ Torus τ.k}
    {s p x y t₁ t₂ : Torus τ.k}
    (hU : ∀ v, u⁻¹ * dD.ofTorus v * u = dD.ofTorus (U v)) (hu : u * u = 1)
    (heL : ∀ v, e * dD.ofTorus v = dD.ofTorus (Φ v) * e)
    (hf₁ : ∀ v, f₁⁻¹ * dD.ofTorus v * f₁ = dD.ofTorus (F₁ v))
    (hf₁L : ∀ v, f₁ * dD.ofTorus v = dD.ofTorus (F₁ v) * f₁)
    (hf₂L : ∀ v, f₂ * dD.ofTorus v = dD.ofTorus (F₂ v) * f₂)
    (hs : e * e = dD.ofTorus s) (hp : f₁ * f₁ = dD.ofTorus p)
    (hx : f₁⁻¹ * e * f₁ = dD.ofTorus x * e) (hy : f₁⁻¹ * f₂ * f₁ = dD.ofTorus y * f₂)
    (ht₁ : u⁻¹ * f₁ * u = dD.ofTorus t₁ * f₁) (ht₂ : u⁻¹ * f₂ * u = dD.ofTorus t₂ * (f₁ * f₂)) :
    F₁ s = x + Φ x + s ∧ F₁ x + x = -p + Φ p ∧ F₁ y + y = -p + F₂ p ∧
      dD.ofTorus (U t₂ + t₁ + F₁ t₂ + p) = 1 ∧ U y + t₂ = F₁ (-t₁ + t₂) + F₂ t₁ + F₁ y := by
  refine ⟨conj_sq_eq dD hf₁ heL hs hx, conj_conj_eq dD hf₁ heL hp hx,
    conj_conj_eq dD hf₁ hf₂L hp hy, ?_, ?_⟩
  ·
    apply (right_eq_mul (b := f₂)).1
    calc f₂ = u⁻¹ * (u⁻¹ * f₂ * u) * u := (conj_conj_of_mul_self hu f₂).symm
      _ = u⁻¹ * (dD.ofTorus t₂ * (f₁ * f₂)) * u := by rw [ht₂]
      _ = (u⁻¹ * dD.ofTorus t₂ * u) * ((u⁻¹ * f₁ * u) * (u⁻¹ * f₂ * u)) := by group
      _ = dD.ofTorus (U t₂) * ((dD.ofTorus t₁ * f₁) * (dD.ofTorus t₂ * (f₁ * f₂))) := by
          rw [hU, ht₁, ht₂]
      _ = dD.ofTorus (U t₂) * (dD.ofTorus t₁ * ((f₁ * dD.ofTorus t₂) * (f₁ * f₂))) := by
          simp only [mul_assoc]
      _ = dD.ofTorus (U t₂) * (dD.ofTorus t₁ * ((dD.ofTorus (F₁ t₂) * f₁) * (f₁ * f₂))) := by
          rw [hf₁L]
      _ = dD.ofTorus (U t₂) * (dD.ofTorus t₁ * (dD.ofTorus (F₁ t₂) * ((f₁ * f₁) * f₂))) := by
          simp only [mul_assoc]
      _ = dD.ofTorus (U t₂) * (dD.ofTorus t₁ * (dD.ofTorus (F₁ t₂) * (dD.ofTorus p * f₂))) := by
          rw [hp]
      _ = dD.ofTorus (U t₂ + t₁ + F₁ t₂ + p) * f₂ := by simp only [dD.ofTorus_add, mul_assoc]
  ·
    apply dD.ofTorus_inj
    apply mul_right_cancel (b := f₁ * f₂)
    calc dD.ofTorus (U y + t₂) * (f₁ * f₂)
        = (u⁻¹ * dD.ofTorus y * u) * (u⁻¹ * f₂ * u) := by
          rw [hU, ht₂, dD.ofTorus_add, mul_assoc]
      _ = u⁻¹ * (dD.ofTorus y * f₂) * u := by group
      _ = u⁻¹ * (f₁⁻¹ * f₂ * f₁) * u := by rw [hy]
      _ = (u⁻¹ * f₁ * u)⁻¹ * (u⁻¹ * f₂ * u) * (u⁻¹ * f₁ * u) := by group
      _ = (dD.ofTorus t₁ * f₁)⁻¹ * (dD.ofTorus t₂ * (f₁ * f₂)) * (dD.ofTorus t₁ * f₁) := by
          rw [ht₁, ht₂]
      _ = f₁⁻¹ * ((dD.ofTorus t₁)⁻¹ * dD.ofTorus t₂) * f₁ * (f₂ * dD.ofTorus t₁) * f₁ := by
          group
      _ = f₁⁻¹ * dD.ofTorus (-t₁ + t₂) * f₁ * (dD.ofTorus (F₂ t₁) * f₂) * f₁ := by
          rw [hf₂L, dD.ofTorus_add, dD.ofTorus_neg]
      _ = dD.ofTorus (F₁ (-t₁ + t₂)) * dD.ofTorus (F₂ t₁) * (f₂ * f₁) := by
          rw [← hf₁]; group
      _ = dD.ofTorus (F₁ (-t₁ + t₂)) * dD.ofTorus (F₂ t₁) * (f₁ * (f₁⁻¹ * f₂ * f₁)) := by
          group
      _ = dD.ofTorus (F₁ (-t₁ + t₂)) * dD.ofTorus (F₂ t₁) * ((f₁ * dD.ofTorus y) * f₂) := by
          rw [hy]; simp only [mul_assoc]
      _ = dD.ofTorus (F₁ (-t₁ + t₂) + F₂ t₁ + F₁ y) * (f₁ * f₂) := by
          rw [hf₁L]; simp only [dD.ofTorus_add, mul_assoc]

private theorem theta₂_rels {u e f₁ f₂ : G} {U F₁ F₂ : Torus τ.k →+ Torus τ.k}
    {s p t₁ t₂ : Torus τ.k}
    (hU : ∀ v, u⁻¹ * dD.ofTorus v * u = dD.ofTorus (U v)) (hu : u * u = 1)
    (hf₁ : ∀ v, f₁⁻¹ * dD.ofTorus v * f₁ = dD.ofTorus (F₁ v))
    (hf₁L : ∀ v, f₁ * dD.ofTorus v = dD.ofTorus (F₁ v) * f₁)
    (hf₂L : ∀ v, f₂ * dD.ofTorus v = dD.ofTorus (F₂ v) * f₂)
    (hue : u⁻¹ * e * u = e) (hs : e * e = dD.ofTorus s) (hp : f₁ * f₁ = dD.ofTorus p)
    (ht₁ : u⁻¹ * f₁ * u = dD.ofTorus t₁ * f₁)
    (ht₂ : u⁻¹ * f₂ * u = dD.ofTorus t₂ * (f₁ * f₂ * e)) :
    F₁ p = p ∧ dD.ofTorus (U t₁ + t₁) = 1 ∧ dD.ofTorus (U t₂ + t₁ + F₁ t₂ + p + F₂ s) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  ·
    apply dD.ofTorus_inj
    rw [← hf₁, ← hp]
    group
  ·
    apply (mul_eq_right (b := f₁)).1
    calc dD.ofTorus (U t₁ + t₁) * f₁ = (u⁻¹ * dD.ofTorus t₁ * u) * (u⁻¹ * f₁ * u) := by
          rw [hU, ht₁, dD.ofTorus_add, mul_assoc]
      _ = u⁻¹ * (dD.ofTorus t₁ * f₁) * u := by group
      _ = u⁻¹ * (u⁻¹ * f₁ * u) * u := by rw [ht₁]
      _ = f₁ := conj_conj_of_mul_self hu f₁
  ·
    apply (right_eq_mul (b := f₂)).1
    calc f₂ = u⁻¹ * (u⁻¹ * f₂ * u) * u := (conj_conj_of_mul_self hu f₂).symm
      _ = u⁻¹ * (dD.ofTorus t₂ * (f₁ * f₂ * e)) * u := by rw [ht₂]
      _ = (u⁻¹ * dD.ofTorus t₂ * u) * ((u⁻¹ * f₁ * u) * ((u⁻¹ * f₂ * u) * (u⁻¹ * e * u))) := by
          group
      _ = dD.ofTorus (U t₂) * ((dD.ofTorus t₁ * f₁) * ((dD.ofTorus t₂ * (f₁ * f₂ * e)) * e)) := by
          rw [hU, ht₁, ht₂, hue]
      _ = dD.ofTorus (U t₂) * (dD.ofTorus t₁ * ((f₁ * dD.ofTorus t₂) * (f₁ * (f₂ * (e * e))))) := by
          simp only [mul_assoc]
      _ = dD.ofTorus (U t₂) * (dD.ofTorus t₁ * ((dD.ofTorus (F₁ t₂) * f₁) *
            (f₁ * (f₂ * dD.ofTorus s)))) := by
          rw [hf₁L, hs]
      _ = dD.ofTorus (U t₂) * (dD.ofTorus t₁ * (dD.ofTorus (F₁ t₂) * ((f₁ * f₁) *
            (f₂ * dD.ofTorus s)))) := by
          simp only [mul_assoc]
      _ = dD.ofTorus (U t₂) * (dD.ofTorus t₁ * (dD.ofTorus (F₁ t₂) * (dD.ofTorus p *
            (dD.ofTorus (F₂ s) * f₂)))) := by
          rw [hp, hf₂L]
      _ = dD.ofTorus (U t₂ + t₁ + F₁ t₂ + p + F₂ s) * f₂ := by
          simp only [dD.ofTorus_add, mul_assoc]

end Group

private theorem two_dvd_of_two_pow_dvd {a b : ℕ} (hab : b = a + 1) {E S : ℤ}
    (h : (2 : ℤ) ^ b ∣ E) (hE : E = 2 ^ a * S) : 2 ∣ S := by
  subst hab hE
  rw [pow_succ] at h
  exact (mul_dvd_mul_iff_left (pow_ne_zero a two_ne_zero)).1 h

end Stroth34T201Natural

open Stroth34T201Natural

theorem StrothWeakTypeData.t201_false_of_theta₁ {G : Type*} [Group G] {D : Subgroup G} {m : ℕ}
    (dD : StrothWeakTypeData D (.t201 m)) (hm : 2 ≤ m) {e f₁ f₂ : G}
    (he : Rel34i dD e (2 ^ (m + 1)))
    (hf₁ : ∀ v, f₁⁻¹ * dD.ofTorus v * f₁ =
      dD.ofTorus (matAct _ (theta₁₁ m) (compat_theta₁₁ hm) v))
    (hf₂ : ∀ v, f₂⁻¹ * dD.ofTorus v * f₂ =
      dD.ofTorus (matAct _ (theta₁₂ m) (compat_theta₁₂ hm) v))
    (hp₁ : f₁ * f₁ ∈ D) (hd₁ : f₁⁻¹ * e * f₁ * e⁻¹ ∈ D) (hd₁₂ : f₁⁻¹ * f₂ * f₁ * f₂⁻¹ ∈ D)
    (hτ₁ : dD.u⁻¹ * f₁ * dD.u * f₁⁻¹ ∈ D) (hτ₂ : dD.u⁻¹ * f₂ * dD.u * (f₁ * f₂)⁻¹ ∈ D) :
    False := by
  have hE : ∀ v, e⁻¹ * dD.ofTorus v * e =
      dD.ofTorus (torusDiag _ ![1, 1 + 2 ^ (m + 1), 1 + 2 ^ (m + 1)] v) :=
    dD.conj_ofTorus_of_gens
      (by rw [he.c_conj, torusDiag_gen, dD.ofTorus_zsmul, ← dD.c_eq]; simp)
      (by
        rw [he.a_conj, torusDiag_gen, dD.ofTorus_zsmul, ← dD.a_eq,
          show (![1, 1 + 2 ^ (m + 1), 1 + 2 ^ (m + 1)] : Fin 3 → ℤ) 1 = 1 + 2 ^ (m + 1) from rfl,
          zpow_add, zpow_one, show ((2 : ℤ) ^ (m + 1)) = ((2 ^ (m + 1) : ℕ) : ℤ) by push_cast; rfl,
          zpow_natCast])
      (by
        rw [he.b_conj, torusDiag_gen, dD.ofTorus_zsmul, ← dD.b_eq,
          show (![1, 1 + 2 ^ (m + 1), 1 + 2 ^ (m + 1)] : Fin 3 → ℤ) 2 = 1 + 2 ^ (m + 1) from rfl,
          zpow_add, zpow_one, show ((2 : ℤ) ^ (m + 1)) = ((2 ^ (m + 1) : ℕ) : ℤ) by push_cast; rfl,
          zpow_natCast])
  have he2 : e * e = dD.ofTorus (Torus.ofInt _ ![-1, 0, 0]) := by
    rw [he.e_sq, dD.ofTorus_ofInt]
    simp
  obtain ⟨P, hP⟩ := dD.exists_ofTorus hp₁
  obtain ⟨X, hX⟩ := dD.exists_ofTorus hd₁
  obtain ⟨Y, hY⟩ := dD.exists_ofTorus hd₁₂
  obtain ⟨T₁, hT₁⟩ := dD.exists_ofTorus hτ₁
  obtain ⟨T₂, hT₂⟩ := dD.exists_ofTorus hτ₂
  rw [mul_inv_eq_iff_eq_mul] at hX hY hT₁ hT₂
  obtain ⟨hA, hB, hE₁₂, hC, hD⟩ := theta₁_rels dD (dD.conj_ofTorus dD.u_mem dD.u_conj) dD.u_sq
    (mul_ofTorus_of_conj dD hE (torusDiag_e_invol m)) hf₁
    (mul_ofTorus_of_conj dD hf₁ (theta₁₁_invol hm)) (mul_ofTorus_of_conj dD hf₂ (theta₁₂_invol hm))
    he2 hP hX hY hT₁ hT₂
  obtain ⟨p, rfl⟩ := Torus.exists_ofInt P
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt X
  obtain ⟨y, rfl⟩ := Torus.exists_ofInt Y
  obtain ⟨t₁, rfl⟩ := Torus.exists_ofInt T₁
  obtain ⟨t₂, rfl⟩ := Torus.exists_ofInt T₂
  simp only [Stroth44Core.t201_φu] at hC hD
  simp only [matAct_ofInt, torusDiag_ofInt, ← Torus.ofInt_neg, ← Torus.ofInt_add,
    Stroth44Core.t201_ofInt_eq_iff, Stroth44Core.ofTorus_ofInt_eq_one_iff, theta₁₁_mulVec,
    theta₁₂_mulVec, Pi.add_apply, Pi.neg_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hA hB hE₁₂ hC hD
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
  simp only [show j + 2 - 1 = j + 1 from rfl] at hA hB hE₁₂ hC hD
  have hx₀ : (2 : ℤ) ∣ x 0 := by
    have h := dvd_trans (⟨2 ^ j, by ring⟩ : (4 : ℤ) ∣ 2 ^ (j + 2)) hA.1
    ring_nf at h
    omega
  have hx₂ : (2 : ℤ) ∣ x 2 := by
    have h := dvd_trans (⟨2 ^ (j + 2), by ring⟩ : (4 : ℤ) ∣ 2 ^ (j + 2 + 2)) hA.2.2
    ring_nf at h
    omega
  have hp : (2 : ℤ) ∣ 1 + p 1 - x 0 - x 2 :=
    two_dvd_of_two_pow_dvd (a := j + 2 + 1) rfl (dvd_add hA.2.1 hB.2.1) (by ring)
  have hy₁ : (2 : ℤ) ∣ y 1 := by
    have h := dvd_trans (⟨2 ^ (j + 2), by ring⟩ : (4 : ℤ) ∣ 2 ^ (j + 2 + 2)) hE₁₂.2.1
    ring_nf at h
    omega
  have hy₂ : (2 : ℤ) ∣ y 2 := by
    have h := dvd_trans (⟨2 ^ (j + 2), by ring⟩ : (4 : ℤ) ∣ 2 ^ (j + 2 + 2)) hE₁₂.2.2
    ring_nf at h
    omega
  have hc := dvd_trans (⟨2 ^ (j + 2 + 1), by ring⟩ : (2 : ℤ) ∣ 2 ^ (j + 2 + 2)) hC.2.1
  ring_nf at hc
  have hd : (2 : ℤ) ∣ -t₁ 1 + t₂ 1 + t₂ 2 + y 1 + y 2 :=
    two_dvd_of_two_pow_dvd (a := j + 1) rfl hD.1 (by ring)
  omega

theorem StrothWeakTypeData.t201_false_of_theta₂ {G : Type*} [Group G] {D : Subgroup G} {m : ℕ}
    (dD : StrothWeakTypeData D (.t201 m)) (hm : 2 ≤ m) {e f₁ f₂ : G}
    (he : Rel34i dD e (2 ^ (m + 1)))
    (hf₁ : ∀ v, f₁⁻¹ * dD.ofTorus v * f₁ =
      dD.ofTorus (matAct _ (theta₂₁ m) (compat_theta₂₁ hm) v))
    (hf₂ : ∀ v, f₂⁻¹ * dD.ofTorus v * f₂ =
      dD.ofTorus (matAct _ (theta₂₂ m) (compat_theta₂₂ hm) v))
    (hp₁ : f₁ * f₁ ∈ D) (hτ₁ : dD.u⁻¹ * f₁ * dD.u * f₁⁻¹ ∈ D)
    (hτ₂ : dD.u⁻¹ * f₂ * dD.u * (f₁ * f₂ * e)⁻¹ ∈ D) :
    False := by
  have hue : dD.u⁻¹ * e * dD.u = e := by
    rw [dD.u_inv]
    calc dD.u * e * dD.u = e * (e⁻¹ * dD.u * e) * dD.u := by group
      _ = e := by rw [he.u_conj, mul_assoc, dD.u_sq, mul_one]
  have he2 : e * e = dD.ofTorus (Torus.ofInt _ ![-1, 0, 0]) := by
    rw [he.e_sq, dD.ofTorus_ofInt]
    simp
  obtain ⟨P, hP⟩ := dD.exists_ofTorus hp₁
  obtain ⟨T₁, hT₁⟩ := dD.exists_ofTorus hτ₁
  obtain ⟨T₂, hT₂⟩ := dD.exists_ofTorus hτ₂
  rw [mul_inv_eq_iff_eq_mul] at hT₁ hT₂
  obtain ⟨h₁, h₂, h₃⟩ := theta₂_rels dD (dD.conj_ofTorus dD.u_mem dD.u_conj) dD.u_sq hf₁
    (mul_ofTorus_of_conj dD hf₁ (theta₂₁_invol hm)) (mul_ofTorus_of_conj dD hf₂ (theta₂₂_invol hm))
    hue he2 hP hT₁ hT₂
  obtain ⟨p, rfl⟩ := Torus.exists_ofInt P
  obtain ⟨t₁, rfl⟩ := Torus.exists_ofInt T₁
  obtain ⟨t₂, rfl⟩ := Torus.exists_ofInt T₂
  simp only [Stroth44Core.t201_φu] at h₂ h₃
  simp only [matAct_ofInt, ← Torus.ofInt_add, Stroth44Core.t201_ofInt_eq_iff,
    Stroth44Core.ofTorus_ofInt_eq_one_iff, theta₂₁_mulVec, theta₂₂_mulVec, Pi.add_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at h₁ h₂ h₃
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
  simp only [show j + 2 - 1 = j + 1 from rfl] at h₁ h₃
  have hp : (2 : ℤ) ∣ -p 0 := two_dvd_of_two_pow_dvd (a := j + 2 + 1) rfl h₁.2.1 (by ring)
  have ht : (4 : ℤ) ∣ t₁ 0 + t₁ 0 := dvd_trans ⟨2 ^ j, by ring⟩ h₂.1
  have hc := dvd_trans (⟨2 ^ (j + 1), by ring⟩ : (2 : ℤ) ∣ 2 ^ (j + 2)) h₃.1
  ring_nf at hc
  omega

end CFSG.CGT.Stroth77
