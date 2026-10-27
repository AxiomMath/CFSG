module

public import CFSG.ClassicalInvolution.Asc77.AscSCH14
public import CFSG.RankThree.CentralLift.DefiningUnitary

public section

namespace CFSG.ClassicalInvolution.Asc77.SCH

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.Classical CFSG.RankThree.CentralLift

variable {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)

theorem single_mem_skew {x : K} (i : Fin 2) (hx : x + h.bar x = 0) :
    (Matrix.single i i x : Matrix (Fin 2) (Fin 2) K) ∈ skewHermMatrices h 2 := by
  rw [mem_skewHermMatrices_iff]
  intro k l
  by_cases hkl : i = k ∧ i = l
  · obtain ⟨rfl, rfl⟩ := hkl
    simpa using hx
  · have h1 : (Matrix.single i i x : Matrix (Fin 2) (Fin 2) K) k l = 0 := by
      simp [hkl]
    have h2 : (Matrix.single i i x : Matrix (Fin 2) (Fin 2) K) l k = 0 := by
      simp only [Matrix.single_apply]
      rw [ite_eq_right_iff.2 (fun hh => absurd ⟨hh.2, hh.1⟩ hkl)]
    rw [h1, h2, map_zero, add_zero]

@[expose] noncomputable def suE0 : K →+ skewHermMatrices h 2 where
  toFun s := ⟨Matrix.single 0 0 (s - h.bar s), single_mem_skew h 0 (by
    rw [map_sub, h.bar_bar]; ring)⟩
  map_zero' := Subtype.ext (by simp)
  map_add' s t := Subtype.ext (by
    simp only [AddSubgroup.coe_add, map_add, ← Matrix.single_add]
    congr 1
    ring)

@[expose] noncomputable def suE1 : K →+ skewHermMatrices h 2 where
  toFun s := ⟨Matrix.single 1 1 (s - h.bar s), single_mem_skew h 1 (by
    rw [map_sub, h.bar_bar]; ring)⟩
  map_zero' := Subtype.ext (by simp)
  map_add' s t := Subtype.ext (by
    simp only [AddSubgroup.coe_add, map_add, ← Matrix.single_add]
    congr 1
    ring)

@[expose] noncomputable def suE2 : K →+ skewHermMatrices h 2 where
  toFun s := ⟨Matrix.single 0 1 s + Matrix.single 1 0 (-h.bar s), by
    rw [mem_skewHermMatrices_iff]
    intro k l
    fin_cases k <;> fin_cases l <;> simp [h.bar_bar]⟩
  map_zero' := Subtype.ext (by simp)
  map_add' s t := Subtype.ext (by
    simp only [AddSubgroup.coe_add, map_add, neg_add, Matrix.single_add]
    abel)

theorem coe_suE0 (s : K) : ((suE0 h s : skewHermMatrices h 2) : Matrix (Fin 2) (Fin 2) K) =
    Matrix.single 0 0 (s - h.bar s) := rfl

theorem coe_suE1 (s : K) : ((suE1 h s : skewHermMatrices h 2) : Matrix (Fin 2) (Fin 2) K) =
    Matrix.single 1 1 (s - h.bar s) := rfl

theorem coe_suE2 (s : K) : ((suE2 h s : skewHermMatrices h 2) : Matrix (Fin 2) (Fin 2) K) =
    Matrix.single 0 1 s + Matrix.single 1 0 (-h.bar s) := rfl

theorem skewHerm_two_decomp (h2 : (2 : K) ≠ 0) (v : skewHermMatrices h 2) :
    v = suE0 h ((v : Matrix (Fin 2) (Fin 2) K) 0 0 / 2) +
      suE1 h ((v : Matrix (Fin 2) (Fin 2) K) 1 1 / 2) +
      suE2 h ((v : Matrix (Fin 2) (Fin 2) K) 0 1) := by
  have hv := (mem_skewHermMatrices_iff h).1 v.2
  have h00 := hv 0 0
  have h11 := hv 1 1
  have h10 := hv 1 0
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_suE0, coe_suE1, coe_suE2, map_div₀]
  · have hb : h.bar ((v : Matrix (Fin 2) (Fin 2) K) 0 0) = - (v : Matrix (Fin 2) (Fin 2) K) 0 0 :=
      eq_neg_of_add_eq_zero_right h00
    rw [hb, map_ofNat h.bar 2]
    field_simp
    ring
  · exact eq_neg_of_add_eq_zero_left h10
  · have hb : h.bar ((v : Matrix (Fin 2) (Fin 2) K) 1 1) = - (v : Matrix (Fin 2) (Fin 2) K) 1 1 :=
      eq_neg_of_add_eq_zero_right h11
    rw [hb, map_ofNat h.bar 2]
    field_simp
    ring

@[expose] def suTorus (a : Fin 2 → Kˣ) (ha : ∀ i, h.bar (a i) = a i) :
    gramSU h (hypGram2 2 K) := ⟨torusGL a, torusGL_mem_gramSU h ha⟩

theorem torus_conj_siegelSU (a : Fin 2 → Kˣ) (ha : ∀ i, h.bar (a i) = a i)
    (v w : skewHermMatrices h 2)
    (hw : (w : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal (fun i => (a i : K)) * v *
      Matrix.diagonal (fun i => (a i : K))) :
    suTorus h a ha * siegelSUHom h 2 (Multiplicative.ofAdd v) * (suTorus h a ha)⁻¹ =
      siegelSUHom h 2 (Multiplicative.ofAdd w) := by
  apply Subtype.ext
  change torusGL a * siegelGL (v : Matrix (Fin 2) (Fin 2) K) * (torusGL a)⁻¹ =
    siegelGL (w : Matrix (Fin 2) (Fin 2) K)
  rw [torusGL_conj_siegelGL, hw]

theorem levi_conj_siegelSU (A : SpecialLinearGroup (Fin 2) K) (v w : skewHermMatrices h 2)
    (hw : (w : Matrix (Fin 2) (Fin 2) K) = (A : Matrix (Fin 2) (Fin 2) K) * v *
      ((A : Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ) :
    leviU h 2 A * siegelSUHom h 2 (Multiplicative.ofAdd v) * (leviU h 2 A)⁻¹ =
      siegelSUHom h 2 (Multiplicative.ofAdd w) := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_leviU_conj h A (x := siegelSUHom h 2 (Multiplicative.ofAdd v)) (B := v) rfl, ← hw]
  rfl

theorem suTorus_suE0 (a : Fin 2 → Kˣ) (ha : ∀ i, h.bar (a i) = a i) (s : K) :
    suTorus h a ha * siegelSUHom h 2 (Multiplicative.ofAdd (suE0 h s)) * (suTorus h a ha)⁻¹ =
      siegelSUHom h 2 (Multiplicative.ofAdd (suE0 h ((a 0 : K) ^ 2 * s))) :=
  torus_conj_siegelSU h a ha _ _ (by
    rw [coe_suE0, coe_suE0, diagonal_mul_single_mul_diagonal, map_mul, map_pow, ha 0]
    congr 1
    ring)

theorem suTorus_suE1 (a : Fin 2 → Kˣ) (ha : ∀ i, h.bar (a i) = a i) (s : K) :
    suTorus h a ha * siegelSUHom h 2 (Multiplicative.ofAdd (suE1 h s)) * (suTorus h a ha)⁻¹ =
      siegelSUHom h 2 (Multiplicative.ofAdd (suE1 h ((a 1 : K) ^ 2 * s))) :=
  torus_conj_siegelSU h a ha _ _ (by
    rw [coe_suE1, coe_suE1, diagonal_mul_single_mul_diagonal, map_mul, map_pow, ha 1]
    congr 1
    ring)

theorem suTorus_suE2 (a : Fin 2 → Kˣ) (ha : ∀ i, h.bar (a i) = a i) (s : K) :
    suTorus h a ha * siegelSUHom h 2 (Multiplicative.ofAdd (suE2 h s)) * (suTorus h a ha)⁻¹ =
      siegelSUHom h 2 (Multiplicative.ofAdd (suE2 h ((a 0 : K) * (a 1 : K) * s))) :=
  torus_conj_siegelSU h a ha _ _ (by
    rw [coe_suE2, coe_suE2, Matrix.mul_add, Matrix.add_mul, diagonal_mul_single',
      diagonal_mul_single', single_mul_diagonal', single_mul_diagonal']
    simp only [map_mul, ha 0, ha 1]
    congr 2 <;> ring)

@[expose] def slD (w : Kˣ) : SpecialLinearGroup (Fin 2) K :=
  ⟨!![(w : K), 0; 0, ((w⁻¹ : Kˣ) : K)], by simp [Matrix.det_fin_two]⟩

@[expose] def slL (x : K) : SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, 0; x, 1], by simp [Matrix.det_fin_two]⟩

theorem coe_slD (w : Kˣ) :
    ((slD w : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![(w : K), 0; 0, ((w⁻¹ : Kˣ) : K)] := rfl

theorem coe_slL (x : K) :
    ((slL x : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![1, 0; x, 1] := rfl

theorem levi_slD_suE2 (w : Kˣ) (s : K) :
    leviU h 2 (slD w) * siegelSUHom h 2 (Multiplicative.ofAdd (suE2 h s)) *
        (leviU h 2 (slD w))⁻¹ =
      siegelSUHom h 2 (Multiplicative.ofAdd (suE2 h ((w : K) * (h.bar (w : K))⁻¹ * s))) :=
  levi_conj_siegelSU h _ _ _ (by
    rw [coe_suE2, coe_suE2, coe_slD]
    have hw : (w : K) ≠ 0 := w.ne_zero
    have hb : h.bar (w : K) ≠ 0 := by
      intro h0
      exact hw (by simpa [h.bar_bar] using congrArg h.bar h0)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply,
        Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        Fin.isValue] <;>
      simp [map_mul, map_inv₀, h.bar_bar] <;> field_simp)

theorem levi_slU_suE1 (s : K) :
    leviU h 2 (slU (1 : K)) * siegelSUHom h 2 (Multiplicative.ofAdd (suE1 h s)) *
        (leviU h 2 (slU (1 : K)))⁻¹ =
      siegelSUHom h 2 (Multiplicative.ofAdd (suE0 h s + suE1 h s + suE2 h (s - h.bar s))) :=
  levi_conj_siegelSU h _ _ _ (by
    simp only [AddSubgroup.coe_add, coe_suE0, coe_suE1, coe_suE2, coe_slU]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply,
        Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        Fin.isValue] <;>
      simp [map_sub, h.bar_bar])

theorem levi_slL_suE0 (s : K) :
    leviU h 2 (slL (1 : K)) * siegelSUHom h 2 (Multiplicative.ofAdd (suE0 h s)) *
        (leviU h 2 (slL (1 : K)))⁻¹ =
      siegelSUHom h 2 (Multiplicative.ofAdd (suE1 h s + suE0 h s + suE2 h (s - h.bar s))) :=
  levi_conj_siegelSU h _ _ _ (by
    simp only [AddSubgroup.coe_add, coe_suE0, coe_suE1, coe_suE2, coe_slL]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply,
        Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        Fin.isValue] <;>
      simp [map_sub, h.bar_bar])

section Pairing

variable {E : Type*} [Group E] {π : E →* gramSU h (hypGram2 2 K)}
  (hπ : Function.Surjective π) (hZ : π.ker ≤ Subgroup.center E)

@[expose] noncomputable def suE2' : K →+ skewHermMatrices h 2 :=
  (suE2 h).comp (AddMonoidHom.id K - (h.bar : K →+* K).toAddMonoidHom)

theorem suE2'_apply (s : K) : suE2' h s = suE2 h (s - h.bar s) := rfl

include hZ in
theorem siegelSU_liftPair_eq_one [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2)
    (h9 : ℓ ^ (2 * f) ≠ 9) (hc : ∃ c : Kˣ, h.bar (c : K) = c ∧ c ^ 2 ≠ 1)
    (v w : skewHermMatrices h 2) :
    liftPair hπ (siegelSUHom h 2) v w = 1 := by
  have := h.finite
  have : CharP K ℓ := h.charP
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K ℓ]; exact hℓ2)
  obtain ⟨c, hcb, hc2⟩ := hc
  have hc1 : (c : K) ≠ 1 := fun h1 => hc2 (by
    have : c = 1 := Units.ext h1
    rw [this, one_pow])
  have hc2' : (c : K) ^ 2 ≠ 1 := fun h1 => hc2 (Units.ext (by simpa using h1))
  have hb1 : ∀ i, h.bar (((![1, c] : Fin 2 → Kˣ) i : Kˣ) : K) = ((![1, c] : Fin 2 → Kˣ) i : Kˣ) :=
    fun i => by fin_cases i <;> simp [hcb]
  have hb2 : ∀ i, h.bar (((![c, 1] : Fin 2 → Kˣ) i : Kˣ) : K) = ((![c, 1] : Fin 2 → Kˣ) i : Kˣ) :=
    fun i => by fin_cases i <;> simp [hcb]
  have c01 : ∀ s t, liftPair hπ (siegelSUHom h 2) (suE0 h s) (suE1 h t) = 1 := fun s t =>
    liftPair_eq_one_of_scale_right hπ (siegelSUHom h 2) hZ (suE0 h) (suE1 h)
      (suTorus h ![1, c] hb1) ((c : K) ^ 2) hc2'
      (fun s => by rw [suTorus_suE0]; simp)
      (fun t => by rw [suTorus_suE1]; simp) s t
  have c10 : ∀ s t, liftPair hπ (siegelSUHom h 2) (suE1 h s) (suE0 h t) = 1 := fun s t =>
    liftPair_eq_one_of_scale_left hπ (siegelSUHom h 2) hZ (suE1 h) (suE0 h)
      (suTorus h ![1, c] hb1) ((c : K) ^ 2) hc2'
      (fun s => by rw [suTorus_suE1]; simp)
      (fun t => by rw [suTorus_suE0]; simp) s t
  have c02 : ∀ s t, liftPair hπ (siegelSUHom h 2) (suE0 h s) (suE2 h t) = 1 := fun s t =>
    liftPair_eq_one_of_scale_right hπ (siegelSUHom h 2) hZ (suE0 h) (suE2 h)
      (suTorus h ![1, c] hb1) (c : K) hc1
      (fun s => by rw [suTorus_suE0]; simp)
      (fun t => by rw [suTorus_suE2]; simp) s t
  have c20 : ∀ s t, liftPair hπ (siegelSUHom h 2) (suE2 h s) (suE0 h t) = 1 := fun s t =>
    liftPair_eq_one_of_scale_left hπ (siegelSUHom h 2) hZ (suE2 h) (suE0 h)
      (suTorus h ![1, c] hb1) (c : K) hc1
      (fun s => by rw [suTorus_suE2]; simp)
      (fun t => by rw [suTorus_suE0]; simp) s t
  have c12 : ∀ s t, liftPair hπ (siegelSUHom h 2) (suE1 h s) (suE2 h t) = 1 := fun s t =>
    liftPair_eq_one_of_scale_right hπ (siegelSUHom h 2) hZ (suE1 h) (suE2 h)
      (suTorus h ![c, 1] hb2) (c : K) hc1
      (fun s => by rw [suTorus_suE1]; simp)
      (fun t => by rw [suTorus_suE2]; simp) s t
  have c21 : ∀ s t, liftPair hπ (siegelSUHom h 2) (suE2 h s) (suE1 h t) = 1 := fun s t =>
    liftPair_eq_one_of_scale_left hπ (siegelSUHom h 2) hZ (suE2 h) (suE1 h)
      (suTorus h ![c, 1] hb2) (c : K) hc1
      (fun s => by rw [suTorus_suE2]; simp)
      (fun t => by rw [suTorus_suE1]; simp) s t
  have s2 : ∀ s t, liftPair hπ (siegelSUHom h 2) (suE2 h s) (suE2 h t) = 1 :=
    liftPair_self_eq_one_of_sq hπ (siegelSUHom h 2) hZ hℓ2 h.card h9 (suE2 h) (fun c' hc' => by
      have hb' : h.bar c' ≠ 0 := fun h0 => hc' (by simpa [h.bar_bar] using congrArg h.bar h0)
      let nw : Kˣ := Units.mk0 (c' * h.bar c') (mul_ne_zero hc' hb')
      have hnw : ∀ i, h.bar (((![nw, 1] : Fin 2 → Kˣ) i : Kˣ) : K) =
          ((![nw, 1] : Fin 2 → Kˣ) i : Kˣ) := fun i => by
        fin_cases i
        · simp [nw, mul_comm, h.bar_bar]
        · simp
      refine ⟨suTorus h ![nw, 1] hnw * leviU h 2 (slD (Units.mk0 c' hc')), fun s => ?_⟩
      have e1 : ∀ (g₁ g₂ x : gramSU h (hypGram2 2 K)), (g₁ * g₂) * x * (g₁ * g₂)⁻¹ =
          g₁ * (g₂ * x * g₂⁻¹) * g₁⁻¹ := fun g₁ g₂ x => by group
      rw [e1, levi_slD_suE2, suTorus_suE2]
      congr 3
      simp only [nw, Units.val_mk0, Matrix.cons_val_zero, Matrix.cons_val_one, Units.val_one]
      field_simp)
  have s0 : ∀ s t, liftPair hπ (siegelSUHom h 2) (suE0 h s) (suE0 h t) = 1 := fun s t =>
    self_of_conj hπ (siegelSUHom h 2) hZ (suE0 h) (suE1 h) (suE2' h) (leviU h 2 (slU (1 : K)))
      (fun y => levi_slU_suE1 h y) c01 c10 (fun s t => c02 s _) (fun s t => c20 _ t)
      (fun s t => c12 s _) (fun s t => c21 _ t) (fun s t => s2 _ _) s t
  have s1 : ∀ s t, liftPair hπ (siegelSUHom h 2) (suE1 h s) (suE1 h t) = 1 := fun s t =>
    self_of_conj hπ (siegelSUHom h 2) hZ (suE1 h) (suE0 h) (suE2' h) (leviU h 2 (slL (1 : K)))
      (fun y => levi_slL_suE0 h y) c10 c01 (fun s t => c12 s _) (fun s t => c21 _ t)
      (fun s t => c02 s _) (fun s t => c20 _ t) (fun s t => s2 _ _) s t
  rw [skewHerm_two_decomp h h2 v, skewHerm_two_decomp h h2 w,
    liftPair_add3 hπ (siegelSUHom h 2) hZ]
  simp only [c01, c10, c02, c20, c12, c21, s0, s1, s2, one_mul]

end Pairing

end CFSG.ClassicalInvolution.Asc77.SCH
