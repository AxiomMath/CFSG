module

public import CFSG.LocalAnalysis.EvenBN.U4.Model.AutNormalizer

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

section Blocks

@[expose] def miyamotoI2Norm1 : Subgroup (GL (Fin 4) K) :=
  (Units.map h.normHom).ker.map (miyamotoI2Hom h)

theorem mem_miyamotoI2Norm1 {g : GL (Fin 4) K} :
    g ∈ miyamotoI2Norm1 h ↔ ∃ b : Kˣ, h.norm (b : K) = 1 ∧ miyamotoI2Hom h b = g := by
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b, (h.mem_ker_normUnits).mp hb, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b, (h.mem_ker_normUnits).mpr hb, rfl⟩

theorem coe_miyamotoI2Hom_of_norm {b : Kˣ} (hb : h.norm (b : K) = 1) :
    ((miyamotoI2Hom h b : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      diagonal ![(b : K) ^ 2, ((b : K) ^ 2)⁻¹, ((b : K) ^ 2)⁻¹, (b : K) ^ 2] := by
  have hbar : h.bar (b : K) = (b : K)⁻¹ := eq_inv_of_mul_eq_one_right hb
  rw [coe_miyamotoI2Hom, hbar]
  congr 1
  ext i
  fin_cases i <;> simp <;> ring

theorem miyamotoN2_le_gramSU_of_det : miyamotoN2 h ≤ gramSU h (miyamotoJ4 K) := by
  have : CharP K 2 := h.charP
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rintro _ ⟨m, rfl⟩
  have hdet : ((m : Matrix (Fin 2) (Fin 2) h.fixedField) 0 0 : K) *
      ((m : Matrix (Fin 2) (Fin 2) h.fixedField) 1 1 : K) -
      ((m : Matrix (Fin 2) (Fin 2) h.fixedField) 0 1 : K) *
        ((m : Matrix (Fin 2) (Fin 2) h.fixedField) 1 0 : K) = 1 := by
    have e : (m : Matrix (Fin 2) (Fin 2) h.fixedField).det = 1 := m.2
    rw [Matrix.det_fin_two] at e
    have := congrArg (fun x : h.fixedField => (x : K)) e
    simpa using this
  have hbar : ∀ i j, h.bar ((m : Matrix (Fin 2) (Fin 2) h.fixedField) i j : K) =
      ((m : Matrix (Fin 2) (Fin 2) h.fixedField) i j : K) := fun i j =>
    ((m : Matrix (Fin 2) (Fin 2) h.fixedField) i j).2
  refine mem_gramSU.mpr ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [miyamotoJ4, miyamotoN2Mat, Matrix.mul_apply, Fin.sum_univ_four, hbar]
    all_goals first
      | linear_combination hdet + (((m : Matrix (Fin 2) (Fin 2) h.fixedField) 0 1 : K) *
          ((m : Matrix (Fin 2) (Fin 2) h.fixedField) 1 0 : K)) * h2
      | (ring_nf; simp [h2])
  · change (miyamotoN2Mat K _).det = 1
    rw [det_fin_four_expand]
    simp [miyamotoN2Mat]
    linear_combination hdet

theorem mem_A2_of_block {g : GL (Fin 4) K} (hg : g ∈ gramSU h (miyamotoJ4 K)) {a c d e e' : K}
    (hM : (g : Matrix (Fin 4) (Fin 4) K) = !![1, 0, 0, 0; a, 1, 0, 0; c, 0, 1, 0; d, e, e', 1]) :
    g ∈ miyamotoA2 h := by
  have : CharP K 2 := h.charP
  obtain ⟨hU, -⟩ := mem_gramSU.mp hg
  have E00 := miyamotoJ4_unitary_entry h hU 0 0
  have E01 := miyamotoJ4_unitary_entry h hU 0 1
  have E02 := miyamotoJ4_unitary_entry h hU 0 2
  simp [hM, miyamotoJ4] at E00 E01 E02
  have he : e = h.bar c := by linear_combination E01 - h.bar c * CharTwo.two_eq_zero (R := K)
  have he' : e' = h.bar a := by linear_combination E02 - h.bar a * CharTwo.two_eq_zero (R := K)
  have hgx : g = miyamotoXGL h a 0 c d := eq_miyamotoXGL h (by
    rw [hM]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [miyamotoX, he, he'])
  rw [hgx]
  refine (miyamotoXGL_mem_A2 h).mpr ⟨rfl, ?_⟩
  linear_combination E00

end Blocks

section CentralizerZ

theorem conj_Z_entries {s : GL (Fin 4) K} {d d' : K}
    (e : s * miyamotoXGL h 0 0 0 d' = miyamotoXGL h 0 0 0 d * s) :
    (s : Matrix (Fin 4) (Fin 4) K) 0 3 * d' = 0 ∧ (s : Matrix (Fin 4) (Fin 4) K) 1 3 * d' = 0 ∧
    (s : Matrix (Fin 4) (Fin 4) K) 2 3 * d' = 0 ∧ d * (s : Matrix (Fin 4) (Fin 4) K) 0 1 = 0 ∧
    d * (s : Matrix (Fin 4) (Fin 4) K) 0 2 = 0 ∧
    (s : Matrix (Fin 4) (Fin 4) K) 3 3 * d' = d * (s : Matrix (Fin 4) (Fin 4) K) 0 0 := by
  have hM := congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K)) e
  simp only [Units.val_mul, coe_miyamotoXGL] at hM
  have E00 := congrFun (congrFun hM 0) 0
  have E10 := congrFun (congrFun hM 1) 0
  have E20 := congrFun (congrFun hM 2) 0
  have E30 := congrFun (congrFun hM 3) 0
  have E31 := congrFun (congrFun hM 3) 1
  have E32 := congrFun (congrFun hM 3) 2
  simp [Matrix.mul_apply, Fin.sum_univ_four, miyamotoX] at E00 E10 E20 E30 E31 E32
  exact ⟨mul_eq_zero.mpr E00, mul_eq_zero.mpr E10, mul_eq_zero.mpr E20, mul_eq_zero.mpr E31,
    mul_eq_zero.mpr E32, by linear_combination E30⟩

theorem exists_A2_I2_N2_of_block {s : GL (Fin 4) K} (hs : s ∈ gramSU h (miyamotoJ4 K))
    (h01 : (s : Matrix (Fin 4) (Fin 4) K) 0 1 = 0) (h02 : (s : Matrix (Fin 4) (Fin 4) K) 0 2 = 0)
    (h03 : (s : Matrix (Fin 4) (Fin 4) K) 0 3 = 0) (h13 : (s : Matrix (Fin 4) (Fin 4) K) 1 3 = 0)
    (h23 : (s : Matrix (Fin 4) (Fin 4) K) 2 3 = 0)
    (h33 : (s : Matrix (Fin 4) (Fin 4) K) 3 3 = (s : Matrix (Fin 4) (Fin 4) K) 0 0) :
    ∃ a ∈ miyamotoA2 h, ∃ i ∈ miyamotoI2Norm1 h, ∃ n ∈ miyamotoN2 h, s = a * (i * n) := by
  have : CharP K 2 := h.charP
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hbb := h.bar_bar
  obtain ⟨hU, hdet⟩ := mem_gramSU.mp hs
  have E03 := miyamotoJ4_unitary_entry h hU 0 3
  have E11 := miyamotoJ4_unitary_entry h hU 1 1
  have E12 := miyamotoJ4_unitary_entry h hU 1 2
  have E21 := miyamotoJ4_unitary_entry h hU 2 1
  have E22 := miyamotoJ4_unitary_entry h hU 2 2
  simp only [h01, h02, h03, h13, h23, h33, map_zero, mul_zero, zero_mul, add_zero, zero_add,
    miyamotoJ4, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    Matrix.empty_val', Matrix.cons_val_fin_one] at E03 E11 E12 E21 E22
  rw [det_fin_four_expand, h01, h02, h03, h13, h23, h33] at hdet
  set l := (s : Matrix (Fin 4) (Fin 4) K) 0 0 with hl
  set α := (s : Matrix (Fin 4) (Fin 4) K) 1 1 with hα
  set β := (s : Matrix (Fin 4) (Fin 4) K) 1 2 with hβ
  set γ := (s : Matrix (Fin 4) (Fin 4) K) 2 1 with hγ
  set ε := (s : Matrix (Fin 4) (Fin 4) K) 2 2 with hε
  have hN : h.norm l = 1 := by
    rw [UnitaryFieldData.norm, mul_comm]; exact E03
  have hl0 : l ≠ 0 := by
    rintro e
    rw [e, map_zero, zero_mul] at E03
    exact zero_ne_one E03
  have hdet' : l ^ 2 * (α * ε - β * γ) = 1 := by rw [← hdet]; ring
  obtain ⟨b, hb⟩ := exists_sq_eq h l
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hl0 (by rw [← hb]; ring)
  have hNb : h.norm b = 1 := by
    refine eq_of_sq_eq_sq ?_
    rw [one_pow, sq, ← norm_mul_eq h, ← sq, hb, hN]
  have hxα : h.bar α * (α * ε - β * γ) = α := by linear_combination α * E12 - β * E11
  have hxγ : h.bar γ * (α * ε - β * γ) = γ := by
    linear_combination ε * E11 - γ * E12 - γ * h2
  have hxβ : h.bar β * (α * ε - β * γ) = β := by
    linear_combination α * E22 - β * E21 - β * h2
  have hxε : h.bar ε * (α * ε - β * γ) = ε := by linear_combination ε * E21 - γ * E22
  have hlbar : h.bar l = l⁻¹ := eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hN)
  have hF : ∀ x : K, h.bar x * (α * ε - β * γ) = x → h.bar (l * x) = l * x := by
    intro x hx
    rw [map_mul, hlbar]
    have e : α * ε - β * γ = (l ^ 2)⁻¹ := eq_inv_of_mul_eq_one_right hdet'
    rw [e] at hx
    calc l⁻¹ * h.bar x = l⁻¹ * (h.bar x * (l ^ 2)⁻¹) * l ^ 2 := by field_simp
      _ = l * x := by rw [hx]; field_simp
  obtain ⟨n, hn, hnM⟩ := exists_mem_miyamotoN2 h (hF α hxα) (hF β hxβ) (hF γ hxγ) (hF ε hxε)
    (by linear_combination hdet')
  set i := miyamotoI2Hom h (Units.mk0 b hb0) with hi
  have hiN : i ∈ miyamotoI2Norm1 h := (mem_miyamotoI2Norm1 h).mpr ⟨_, hNb, rfl⟩
  have hD : ((i * n : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      !![l, 0, 0, 0; 0, α, β, 0; 0, γ, ε, 0; 0, 0, 0, l] := by
    rw [Units.val_mul, hi, coe_miyamotoI2Hom_of_norm h (b := Units.mk0 b hb0) hNb, hnM]
    ext k m
    fin_cases k <;> fin_cases m <;> simp [Matrix.mul_apply, diagonal, hb] <;> field_simp
  have hin : i * n ∈ gramSU h (miyamotoJ4 K) :=
    mul_mem (miyamotoI2_le_gramSU h ⟨_, rfl⟩) (miyamotoN2_le_gramSU_of_det h hn)
  refine ⟨s * (i * n)⁻¹, ?_, i, hiN, n, hn, by group⟩
  have hS : s * (i * n)⁻¹ ∈ gramSU h (miyamotoJ4 K) := mul_mem hs (inv_mem hin)
  set A := ((s * (i * n)⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hA
  have hAD : A * ((i * n : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (s : Matrix (Fin 4) (Fin 4) K) := by
    rw [hA, ← Units.val_mul, inv_mul_cancel_right]
  rw [hD] at hAD
  have E : ∀ k m : Fin 4, _ := fun k m => congrFun (congrFun hAD k) m
  have F00 := E 0 0
  have F01 := E 0 1
  have F02 := E 0 2
  have F03 := E 0 3
  have F11 := E 1 1
  have F12 := E 1 2
  have F13 := E 1 3
  have F21 := E 2 1
  have F22 := E 2 2
  have F23 := E 2 3
  have F33 := E 3 3
  simp [Matrix.mul_apply, Fin.sum_univ_four] at F00 F01 F02 F03 F11 F12 F13 F21 F22 F23 F33
  have hdM : α * ε - β * γ ≠ 0 := right_ne_zero_of_mul_eq_one hdet'
  obtain ⟨a01, a02⟩ := eq_zero_of_vecMul_two (x := A 0 1) (y := A 0 2) hdM
    (by linear_combination F01 + h01) (by linear_combination F02 + h02)
  obtain ⟨a11, a12⟩ := eq_zero_of_vecMul_two (x := A 1 1 - 1) (y := A 1 2) hdM
    (by linear_combination F11) (by linear_combination F12)
  obtain ⟨a21, a22⟩ := eq_zero_of_vecMul_two (x := A 2 1) (y := A 2 2 - 1) hdM
    (by linear_combination F21) (by linear_combination F22)
  have a00 : A 0 0 = 1 := mul_right_cancel₀ hl0 (by rw [one_mul]; exact F00)
  have a33 : A 3 3 = 1 := mul_right_cancel₀ hl0 (by rw [one_mul]; exact F33.trans h33)
  have a03 : A 0 3 = 0 := (mul_eq_zero.mp (F03.trans h03)).resolve_right hl0
  have a13 : A 1 3 = 0 := (mul_eq_zero.mp (F13.trans h13)).resolve_right hl0
  have a23 : A 2 3 = 0 := (mul_eq_zero.mp (F23.trans h23)).resolve_right hl0
  refine mem_A2_of_block h hS (a := A 1 0) (c := A 2 0) (d := A 3 0) (e := A 3 1)
    (e' := A 3 2) ?_
  rw [← hA]
  ext k m
  fin_cases k <;> fin_cases m <;>
    simp [a00, a01, a02, a03, sub_eq_zero.mp a11, a12, a13, a21, sub_eq_zero.mp a22, a23, a33]

theorem miyamotoA2_commute_Z {a z : GL (Fin 4) K} (ha : a ∈ miyamotoA2 h) (hz : z ∈ miyamotoZ h) :
    a * z = z * a := by
  have : CharP K 2 := h.charP
  obtain ⟨x, c, d, -, rfl⟩ := (mem_A2 h).mp ha
  obtain ⟨e, -, rfl⟩ := (mem_Z h).mp hz
  rw [miyamotoXGL_mul h (map_zero _), miyamotoXGL_mul h (map_zero _), miyamotoXGL_inj]
  refine ⟨by ring, by ring, by ring, by simp only [map_zero]; ring⟩

theorem miyamotoI2Norm1_commute_Z {i z : GL (Fin 4) K} (hi : i ∈ miyamotoI2Norm1 h)
    (hz : z ∈ miyamotoZ h) : i * z = z * i := by
  obtain ⟨b, hb, rfl⟩ := (mem_miyamotoI2Norm1 h).mp hi
  obtain ⟨e, -, rfl⟩ := (mem_Z h).mp hz
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_miyamotoI2Hom_of_norm h hb, coe_miyamotoXGL]
  ext k l
  fin_cases k <;> fin_cases l <;> simp [Matrix.mul_apply, Fin.sum_univ_four, miyamotoX]
  ring

theorem miyamotoN2_mul_comm_Z {n z : GL (Fin 4) K} (hn : n ∈ miyamotoN2 h)
    (hz : z ∈ miyamotoZ h) : n * z = z * n := by
  obtain ⟨m, rfl⟩ := hn
  obtain ⟨e, -, rfl⟩ := (mem_Z h).mp hz
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_miyamotoXGL]
  change miyamotoN2Mat K _ * _ = _ * miyamotoN2Mat K _
  ext k l
  fin_cases k <;> fin_cases l <;> simp [Matrix.mul_apply, Fin.sum_univ_four, miyamotoX,
    miyamotoN2Mat]

theorem fixes_miyamotoZ_iff (α : MulAut (gramSU h (miyamotoJ4 K))) :
    (∀ g : gramSU h (miyamotoJ4 K), (g : GL (Fin 4) K) ∈ miyamotoZ h → α g = g) ↔
      ∃ s : gramSU h (miyamotoJ4 K), (∃ a ∈ miyamotoA2 h, ∃ i ∈ miyamotoI2Norm1 h,
        ∃ n ∈ miyamotoN2 h, (s : GL (Fin 4) K) = a * (i * n)) ∧ ∃ φ : K ≃+* K,
          (φ = RingEquiv.refl K ∨ ∀ c, φ c = h.bar c) ∧
            α = MulAut.conj s * miyamotoFieldAut h φ := by
  have : CharP K 2 := h.charP
  constructor
  · intro hZ
    obtain ⟨s, hs⟩ := exists_eq_conj_mul_fieldAut h α
    set φ := miyamotoFieldFactor h α with hφdef
    have hc : ∀ d : K, h.bar d = d → (s : GL (Fin 4) K) * miyamotoXGL h 0 0 0 (φ d) =
        miyamotoXGL h 0 0 0 d * s := by
      intro d hd
      have hz : miyamotoXGL h 0 0 0 d ∈ miyamotoZ h := (miyamotoXGL_mem_Z h).mpr
        ⟨rfl, rfl, rfl, hd⟩
      have e := congrArg (fun g : gramSU h (miyamotoJ4 K) => (g : GL (Fin 4) K))
        (hZ ⟨_, miyamotoUnipotent_le_SU h true true ((miyamotoZ_le_Z2 h) hz)⟩ hz)
      rw [hs] at e
      simp only [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
        coe_miyamotoFieldAut_apply, glAut_miyamotoXGL, map_zero] at e
      calc (s : GL (Fin 4) K) * miyamotoXGL h 0 0 0 (φ d) =
          (s * miyamotoXGL h 0 0 0 (φ d) * (s : GL (Fin 4) K)⁻¹) * s := by group
        _ = _ := by rw [e]
    obtain ⟨h03, h13, h23, h01, h02, h33⟩ := conj_Z_entries h (hc 1 (map_one _))
    simp only [map_one, mul_one, one_mul] at h03 h13 h23 h01 h02 h33
    have hl0 : ((s : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 0 ≠ 0 := by
      intro e0
      have hdet : ((s : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det ≠ 0 :=
        ((Matrix.isUnit_iff_isUnit_det _).mp (s : GL (Fin 4) K).isUnit).ne_zero
      exact hdet (Matrix.det_eq_zero_of_row_eq_zero 0 fun j => by
        fin_cases j
        exacts [e0, h01, h02, h03])
    have hφF : ∀ a : K, h.bar a = a → φ a = a := by
      intro a ha
      obtain ⟨-, -, -, -, -, e⟩ := conj_Z_entries h (hc a ha)
      rw [h33] at e
      exact mul_left_cancel₀ hl0 (e.trans (mul_comm _ _))
    have hφ : φ = RingEquiv.refl K ∨ ∀ c, φ c = h.bar c :=
      ringEquiv_eq_refl_or_bar_of_fixes h fun a ha => hφF a ((h.mem_fixedField).mp ha)
    exact ⟨s, exists_A2_I2_N2_of_block h s.2 h01 h02 h03 h13 h23 h33, φ, hφ, hs⟩
  · rintro ⟨s, ⟨a, ha, i, hi, n, hn, hs⟩, φ, hφ, rfl⟩ g hg
    have hφF := fixes_of_refl_or_bar h hφ
    obtain ⟨d, hd, hgd⟩ := (mem_Z h).mp hg
    have hφg : glAut φ (g : GL (Fin 4) K) = g := by
      rw [hgd, glAut_miyamotoXGL, map_zero, hφF d hd]
    apply Subtype.ext
    rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      coe_miyamotoFieldAut_apply, hφg, hs]
    have e1 := miyamotoA2_commute_Z h ha hg
    have e2 := miyamotoI2Norm1_commute_Z h hi hg
    have e3 := miyamotoN2_mul_comm_Z h hn hg
    calc a * (i * n) * (g : GL (Fin 4) K) * (a * (i * n))⁻¹ =
        a * (i * (n * g)) * (a * (i * n))⁻¹ := by group
      _ = g := by rw [e3, ← mul_assoc i, e2, mul_assoc (g : GL (Fin 4) K), ← mul_assoc a, e1];
                  group

end CentralizerZ

end CFSG.LocalAnalysis.EvenBN.U4
