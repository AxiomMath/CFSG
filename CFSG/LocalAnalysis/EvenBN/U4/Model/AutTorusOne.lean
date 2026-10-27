module

public import CFSG.LocalAnalysis.EvenBN.U4.Model.AutTorus
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherIsotropicCentralizer
public import CFSG.LocalAnalysis.EvenBN.U4.Model.Weights

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

section TorusOne

omit [Field K] in
theorem coe_miyamotoI1Hom {K : Type} [Field K] (t : Kˣ) :
    ((miyamotoI1Hom t : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      diagonal ![(t : K), t, (t : K)⁻¹, (t : K)⁻¹] := by
  simp [miyamotoI1Hom, miyamotoDiag]

theorem mem_miyamotoI1' {g : GL (Fin 4) K} :
    g ∈ miyamotoI1 h ↔ ∃ t : Kˣ, h.bar t = t ∧ g = miyamotoI1Hom t := by
  rw [mem_miyamotoI1]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, (miyamotoI1Hom_eq h ht).symm⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, miyamotoI1Hom_eq h ht⟩

theorem miyamotoI1_le_gramSU : miyamotoI1 h ≤ gramSU h (miyamotoJ4 K) := by
  intro g hg
  obtain ⟨t, ht, rfl⟩ := (mem_miyamotoI1 h).mp hg
  refine (miyamotoIHom_mem_gramSU_iff h _).mpr (Units.ext ?_)
  have ht' : h.bar (t : K) = t := ht
  simp [miyamotoIParam, ht']

theorem miyamotoI1_mul_comm {g g' : GL (Fin 4) K} (hg : g ∈ miyamotoI1 h)
    (hg' : g' ∈ miyamotoI1 h) : g * g' = g' * g := by
  obtain ⟨a, rfl⟩ := hg
  obtain ⟨b, rfl⟩ := hg'
  rw [← map_mul, ← map_mul, mul_comm]

theorem miyamotoN1_commute_I1 {n g : GL (Fin 4) K} (hn : n ∈ miyamotoN1 h)
    (hg : g ∈ miyamotoI1 h) : n * g = g * n := by
  obtain ⟨m, rfl⟩ := hn
  obtain ⟨t, ht, rfl⟩ := (mem_miyamotoI1' h).mp hg
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_miyamotoI1Hom]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, miyamotoN1Mat, diagonal] <;> ring

theorem commute_miyamotoI1_of_mul {i n g : GL (Fin 4) K} (hi : i ∈ miyamotoI1 h)
    (hn : n ∈ miyamotoN1 h) (hg : g ∈ miyamotoI1 h) : i * n * g = g * (i * n) := by
  rw [mul_assoc, miyamotoN1_commute_I1 h hn hg, ← mul_assoc, miyamotoI1_mul_comm h hi hg,
    mul_assoc]

theorem exists_mem_miyamotoN1 {x y z w : K} (hdet : x * w - y * z = 1) :
    ∃ n ∈ miyamotoN1 h, (n : Matrix (Fin 4) (Fin 4) K) =
      !![x, y, 0, 0; z, w, 0, 0; 0, 0, h.bar x, h.bar y; 0, 0, h.bar z, h.bar w] := by
  let g : SpecialLinearGroup (Fin 2) K :=
    ⟨!![x, y; z, w], by rw [Matrix.det_fin_two_of]; exact hdet⟩
  refine ⟨_, ⟨g, rfl⟩, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

end TorusOne

section CentralizerOne

theorem exists_miyamotoI1_N1_diag_blocks {s : GL (Fin 4) K}
    (hs : s ∈ gramSU h (miyamotoJ4 K))
    (h02 : (s : Matrix (Fin 4) (Fin 4) K) 0 2 = 0) (h03 : (s : Matrix (Fin 4) (Fin 4) K) 0 3 = 0)
    (h12 : (s : Matrix (Fin 4) (Fin 4) K) 1 2 = 0) (h13 : (s : Matrix (Fin 4) (Fin 4) K) 1 3 = 0) :
    ∃ i ∈ miyamotoI1 h, ∃ n ∈ miyamotoN1 h, ((i * n : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      !![(s : Matrix (Fin 4) (Fin 4) K) 0 0, (s : Matrix (Fin 4) (Fin 4) K) 0 1, 0, 0;
        (s : Matrix (Fin 4) (Fin 4) K) 1 0, (s : Matrix (Fin 4) (Fin 4) K) 1 1, 0, 0;
        0, 0, (s : Matrix (Fin 4) (Fin 4) K) 2 2, (s : Matrix (Fin 4) (Fin 4) K) 2 3;
        0, 0, (s : Matrix (Fin 4) (Fin 4) K) 3 2, (s : Matrix (Fin 4) (Fin 4) K) 3 3] := by
  have : CharP K 2 := h.charP
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hbb := h.bar_bar
  obtain ⟨hU, hdet⟩ := mem_gramSU.mp hs
  have E02 := miyamotoJ4_unitary_entry h hU 0 2
  have E03 := miyamotoJ4_unitary_entry h hU 0 3
  have E12 := miyamotoJ4_unitary_entry h hU 1 2
  have E13 := miyamotoJ4_unitary_entry h hU 1 3
  simp only [h02, h03, h12, h13, mul_zero, add_zero, miyamotoJ4, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val',
    Matrix.cons_val_fin_one] at E02 E03 E12 E13
  rw [det_fin_four_expand, h02, h03, h12, h13] at hdet
  set p := (s : Matrix (Fin 4) (Fin 4) K) 0 0 with hp
  set q := (s : Matrix (Fin 4) (Fin 4) K) 0 1 with hq
  set r := (s : Matrix (Fin 4) (Fin 4) K) 1 0 with hr
  set u := (s : Matrix (Fin 4) (Fin 4) K) 1 1 with hu
  set p' := (s : Matrix (Fin 4) (Fin 4) K) 2 2 with hp'
  set q' := (s : Matrix (Fin 4) (Fin 4) K) 2 3 with hq'
  set r' := (s : Matrix (Fin 4) (Fin 4) K) 3 2 with hr'
  set u' := (s : Matrix (Fin 4) (Fin 4) K) 3 3 with hu'
  set l := p * u - q * r with hl
  have hlbar : h.bar l = h.bar p * h.bar u - h.bar q * h.bar r := by
    rw [hl, map_sub, map_mul, map_mul]
  have hp'' : p' * h.bar l = h.bar p := by
    rw [hlbar]; linear_combination h.bar p * E12 - h.bar q * E02
  have hq'' : q' * h.bar l = h.bar q := by
    rw [hlbar]; linear_combination h.bar p * E13 - h.bar q * E03 - h.bar q * h2
  have hr'' : r' * h.bar l = h.bar r := by
    rw [hlbar]; linear_combination h.bar u * E02 - h.bar r * E12 - h.bar r * h2
  have hu'' : u' * h.bar l = h.bar u := by
    rw [hlbar]; linear_combination h.bar u * E03 - h.bar r * E13
  have hdet' : l * (p' * u' - q' * r') = 1 := by rw [← hdet]; ring
  have hl0' : l ≠ 0 := left_ne_zero_of_mul_eq_one hdet'
  have hl0 : h.bar l ≠ 0 := (map_ne_zero _).mpr hl0'
  have hdet2 : (p' * u' - q' * r') * h.bar l = 1 := by
    have e : (p' * u' - q' * r') * h.bar l ^ 2 = h.bar l := by
      rw [show (p' * u' - q' * r') * h.bar l ^ 2 = (p' * h.bar l) * (u' * h.bar l) -
        (q' * h.bar l) * (r' * h.bar l) by ring, hp'', hu'', hq'', hr'', hlbar]
    have e2 : ((p' * u' - q' * r') * h.bar l - 1) * h.bar l = 0 := by linear_combination e
    exact sub_eq_zero.mp ((mul_eq_zero.mp e2).resolve_right hl0)
  have hlF : h.bar l = l := by
    have e : l = (p' * u' - q' * r')⁻¹ := eq_inv_of_mul_eq_one_left hdet'
    have e' : h.bar l = (p' * u' - q' * r')⁻¹ := by
      rw [mul_comm] at hdet2
      exact eq_inv_of_mul_eq_one_left hdet2
    exact e'.trans e.symm
  obtain ⟨a₀, ha₀⟩ := exists_sq_eq h l
  have ha₀0 : a₀ ≠ 0 := by
    rintro rfl
    exact hl0' (by rw [← ha₀]; ring)
  have ha₀F : h.bar a₀ = a₀ := eq_of_sq_eq_sq (by rw [← map_pow, ha₀, hlF])
  have hp3 : p' = h.bar p * (a₀ ^ 2)⁻¹ := by
    rw [ha₀, ← hlF]; exact (eq_mul_inv_iff_mul_eq₀ hl0).mpr hp''
  have hq3 : q' = h.bar q * (a₀ ^ 2)⁻¹ := by
    rw [ha₀, ← hlF]; exact (eq_mul_inv_iff_mul_eq₀ hl0).mpr hq''
  have hr3 : r' = h.bar r * (a₀ ^ 2)⁻¹ := by
    rw [ha₀, ← hlF]; exact (eq_mul_inv_iff_mul_eq₀ hl0).mpr hr''
  have hu3 : u' = h.bar u * (a₀ ^ 2)⁻¹ := by
    rw [ha₀, ← hlF]; exact (eq_mul_inv_iff_mul_eq₀ hl0).mpr hu''
  obtain ⟨n, hn, hnM⟩ := exists_mem_miyamotoN1 h (x := a₀⁻¹ * p) (y := a₀⁻¹ * q) (z := a₀⁻¹ * r)
    (w := a₀⁻¹ * u) (by
      calc a₀⁻¹ * p * (a₀⁻¹ * u) - a₀⁻¹ * q * (a₀⁻¹ * r) = (a₀ ^ 2)⁻¹ * l := by rw [hl]; ring
        _ = 1 := by rw [ha₀, inv_mul_cancel₀ hl0'])
  refine ⟨miyamotoI1Hom (Units.mk0 a₀ ha₀0), (mem_miyamotoI1' h).mpr ⟨_, ha₀F, rfl⟩, n, hn, ?_⟩
  rw [Units.val_mul, coe_miyamotoI1Hom, hnM]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, diagonal, hp3, hq3, hr3, hu3, map_inv₀, ha₀F] <;>
    field_simp

theorem exists_miyamotoI1_N1_of_block {s : GL (Fin 4) K} (hs : s ∈ gramSU h (miyamotoJ4 K))
    (h02 : (s : Matrix (Fin 4) (Fin 4) K) 0 2 = 0) (h03 : (s : Matrix (Fin 4) (Fin 4) K) 0 3 = 0)
    (h12 : (s : Matrix (Fin 4) (Fin 4) K) 1 2 = 0) (h13 : (s : Matrix (Fin 4) (Fin 4) K) 1 3 = 0)
    (h20 : (s : Matrix (Fin 4) (Fin 4) K) 2 0 = 0) (h21 : (s : Matrix (Fin 4) (Fin 4) K) 2 1 = 0)
    (h30 : (s : Matrix (Fin 4) (Fin 4) K) 3 0 = 0) (h31 : (s : Matrix (Fin 4) (Fin 4) K) 3 1 = 0) :
    ∃ i ∈ miyamotoI1 h, ∃ n ∈ miyamotoN1 h, s = i * n := by
  obtain ⟨i, hi, n, hn, e⟩ := exists_miyamotoI1_N1_diag_blocks h hs h02 h03 h12 h13
  refine ⟨i, hi, n, hn, Units.ext ?_⟩
  rw [e]
  ext k l
  fin_cases k <;> fin_cases l <;> simp [h02, h03, h12, h13, h20, h21, h30, h31]

theorem exists_miyamotoI1_N1_of_commute {t : Kˣ} (ht : (t : K) ^ 2 ≠ 1) {s : GL (Fin 4) K}
    (hs : s ∈ gramSU h (miyamotoJ4 K)) (hc : s * miyamotoI1Hom t = miyamotoI1Hom t * s) :
    ∃ i ∈ miyamotoI1 h, ∃ n ∈ miyamotoN1 h, s = i * n := by
  have hne : (t : K) ≠ (t : K)⁻¹ := by
    intro e
    apply ht
    rw [sq]
    nth_rw 2 [e]
    exact mul_inv_cancel₀ t.ne_zero
  have hM := congrArg Units.val hc
  rw [Units.val_mul, Units.val_mul, coe_miyamotoI1Hom] at hM
  have z := fun (i j : Fin 4) (hij : ![(t : K), t, (t : K)⁻¹, (t : K)⁻¹] i ≠
    ![(t : K), t, (t : K)⁻¹, (t : K)⁻¹] j) => eq_zero_of_mul_diagonal_eq hM hij
  exact exists_miyamotoI1_N1_of_block h hs (z 0 2 hne) (z 0 3 hne) (z 1 2 hne) (z 1 3 hne)
    (z 2 0 hne.symm) (z 2 1 hne.symm) (z 3 0 hne.symm) (z 3 1 hne.symm)

end CentralizerOne

section StabA1

theorem mem_A1_of_block {g : GL (Fin 4) K} (hg : g ∈ gramSU h (miyamotoJ4 K)) {b c d e : K}
    (hM : (g : Matrix (Fin 4) (Fin 4) K) = !![1, 0, 0, 0; 0, 1, 0, 0; c, b, 1, 0; d, e, 0, 1]) :
    g ∈ miyamotoA1 h := by
  have : CharP K 2 := h.charP
  obtain ⟨hU, -⟩ := mem_gramSU.mp hg
  have E00 := miyamotoJ4_unitary_entry h hU 0 0
  have E01 := miyamotoJ4_unitary_entry h hU 0 1
  have E11 := miyamotoJ4_unitary_entry h hU 1 1
  simp [hM, miyamotoJ4] at E00 E01 E11
  have hd : h.bar d = d := by linear_combination E00 - d * CharTwo.two_eq_zero (R := K)
  have hb : h.bar b = b := by linear_combination E11 - b * CharTwo.two_eq_zero (R := K)
  have he : e = h.bar c := by linear_combination E01 - h.bar c * CharTwo.two_eq_zero (R := K)
  have hgx : g = miyamotoXGL h 0 b c d := eq_miyamotoXGL h (by
    rw [hM]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [miyamotoX, he])
  rw [hgx]
  exact (miyamotoXGL_mem_A1 h).mpr ⟨rfl, hb, hd⟩

theorem upper_right_eq_zero_of_conj_mem_A1 {s : GL (Fin 4) K}
    (hs : s⁻¹ * miyamotoXGL h 0 0 1 0 * s ∈ miyamotoA1 h) :
    (s : Matrix (Fin 4) (Fin 4) K) 0 2 = 0 ∧ (s : Matrix (Fin 4) (Fin 4) K) 0 3 = 0 ∧
      (s : Matrix (Fin 4) (Fin 4) K) 1 2 = 0 ∧ (s : Matrix (Fin 4) (Fin 4) K) 1 3 = 0 := by
  have : CharP K 2 := h.charP
  obtain ⟨b, c, d, -, -, e⟩ := (mem_A1 h).mp hs
  have e' : miyamotoXGL h 0 0 1 0 * s = s * miyamotoXGL h 0 b c d := by rw [← e]; group
  have hm := congrArg Units.val e'
  rw [Units.val_mul, Units.val_mul, coe_miyamotoXGL, coe_miyamotoXGL] at hm
  have E22 := congrFun (congrFun hm 2) 2
  have E23 := congrFun (congrFun hm 2) 3
  have E32 := congrFun (congrFun hm 3) 2
  have E33 := congrFun (congrFun hm 3) 3
  simp [Matrix.mul_apply, Fin.sum_univ_four, miyamotoX] at E22 E23 E32 E33
  exact ⟨E22, E23, E32, E33⟩

theorem miyamotoN1_le_gramSU_of_det : miyamotoN1 h ≤ gramSU h (miyamotoJ4 K) := by
  have : CharP K 2 := h.charP
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rintro _ ⟨m, rfl⟩
  have hdet : (m : Matrix (Fin 2) (Fin 2) K) 0 0 * (m : Matrix (Fin 2) (Fin 2) K) 1 1 -
      (m : Matrix (Fin 2) (Fin 2) K) 0 1 * (m : Matrix (Fin 2) (Fin 2) K) 1 0 = 1 := by
    rw [← Matrix.det_fin_two]; exact m.2
  have hdetb := congrArg h.bar hdet
  rw [map_sub, map_mul, map_mul, map_one] at hdetb
  have hbb := h.bar_bar
  refine mem_gramSU.mpr ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [miyamotoJ4, miyamotoN1Mat, Matrix.mul_apply, Fin.sum_univ_four, hbb]
    all_goals first
      | linear_combination hdet + ((m : Matrix (Fin 2) (Fin 2) K) 0 1 *
          (m : Matrix (Fin 2) (Fin 2) K) 1 0) * h2
      | linear_combination hdetb + (h.bar ((m : Matrix (Fin 2) (Fin 2) K) 0 1) *
          h.bar ((m : Matrix (Fin 2) (Fin 2) K) 1 0)) * h2
      | (ring_nf; simp [h2])
  · change (miyamotoN1Mat h (m : Matrix (Fin 2) (Fin 2) K)).det = 1
    rw [det_fin_four_expand]
    simp [miyamotoN1Mat]
    linear_combination (h.bar ((m : Matrix (Fin 2) (Fin 2) K) 0 0) *
      h.bar ((m : Matrix (Fin 2) (Fin 2) K) 1 1) - h.bar ((m : Matrix (Fin 2) (Fin 2) K) 0 1) *
        h.bar ((m : Matrix (Fin 2) (Fin 2) K) 1 0)) * hdet + hdetb

theorem coe_miyamotoN1_elem (m : SpecialLinearGroup (Fin 2) K) :
    ((((Units.map (miyamotoN1Mat h)).comp SpecialLinearGroup.toGL) m : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) = miyamotoN1Mat h (m : Matrix (Fin 2) (Fin 2) K) :=
  rfl

theorem coe_miyamotoN1_elem_inv (m : SpecialLinearGroup (Fin 2) K) :
    (((((Units.map (miyamotoN1Mat h)).comp SpecialLinearGroup.toGL) m)⁻¹ : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) = miyamotoN1Mat h !![(m : Matrix (Fin 2) (Fin 2) K) 1 1,
        -(m : Matrix (Fin 2) (Fin 2) K) 0 1; -(m : Matrix (Fin 2) (Fin 2) K) 1 0,
        (m : Matrix (Fin 2) (Fin 2) K) 0 0] := by
  have hinv : ((m⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![(m : Matrix (Fin 2) (Fin 2) K) 1 1, -(m : Matrix (Fin 2) (Fin 2) K) 0 1;
        -(m : Matrix (Fin 2) (Fin 2) K) 1 0, (m : Matrix (Fin 2) (Fin 2) K) 0 0] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two]
  rw [← map_inv, coe_miyamotoN1_elem, hinv]

theorem miyamotoN1_conj_mem_A1 {n g : GL (Fin 4) K} (hn : n ∈ miyamotoN1 h)
    (hg : g ∈ miyamotoA1 h) : n * g * n⁻¹ ∈ miyamotoA1 h := by
  have : CharP K 2 := h.charP
  have hS : n * g * n⁻¹ ∈ gramSU h (miyamotoJ4 K) :=
    mul_mem (mul_mem (miyamotoN1_le_gramSU_of_det h hn) (miyamotoUnipotent_le_SU h true false hg))
      (inv_mem (miyamotoN1_le_gramSU_of_det h hn))
  refine mem_A1_of_block h hS (b := ((n * g * n⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 2 1)
    (c := ((n * g * n⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 2 0)
    (d := ((n * g * n⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 3 0)
    (e := ((n * g * n⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 3 1) ?_
  obtain ⟨m, rfl⟩ := hn
  obtain ⟨b, c, d, -, -, rfl⟩ := (mem_A1 h).mp hg
  have hdet : (m : Matrix (Fin 2) (Fin 2) K) 0 0 * (m : Matrix (Fin 2) (Fin 2) K) 1 1 -
      (m : Matrix (Fin 2) (Fin 2) K) 0 1 * (m : Matrix (Fin 2) (Fin 2) K) 1 0 = 1 := by
    rw [← Matrix.det_fin_two]; exact m.2
  have hdetb := congrArg h.bar hdet
  rw [map_sub, map_mul, map_mul, map_one] at hdetb
  ext i j
  fin_cases i <;> fin_cases j
  all_goals try rfl
  all_goals
    rw [Units.val_mul, Units.val_mul, coe_miyamotoN1_elem, coe_miyamotoN1_elem_inv]
    simp [miyamotoN1Mat, miyamotoX, Matrix.mul_apply, Fin.sum_univ_four]
  all_goals first
    | linear_combination hdet
    | linear_combination hdetb
    | ring

theorem glAut_miyamotoXGL (φ : K ≃+* K) (a b c d : K) :
    glAut φ (miyamotoXGL h a b c d) = miyamotoXGL h (φ a) (φ b) (φ c) (φ d) := by
  apply Units.ext
  rw [coe_glAut, coe_miyamotoXGL, coe_miyamotoXGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [miyamotoX, map_bar_comm]

theorem glAut_mem_A1 (φ : K ≃+* K) {g : GL (Fin 4) K} (hg : g ∈ miyamotoA1 h) :
    glAut φ g ∈ miyamotoA1 h := by
  have : CharP K 2 := h.charP
  obtain ⟨b, c, d, hb, hd, rfl⟩ := (mem_A1 h).mp hg
  rw [glAut_miyamotoXGL, map_zero]
  exact (miyamotoXGL_mem_A1 h).mpr ⟨rfl, by rw [← map_bar_comm, hb], by rw [← map_bar_comm, hd]⟩

theorem glAut_mem_A1_iff (φ : K ≃+* K) {g : GL (Fin 4) K} :
    glAut φ g ∈ miyamotoA1 h ↔ g ∈ miyamotoA1 h := by
  refine ⟨fun hg => ?_, glAut_mem_A1 h φ⟩
  have := glAut_mem_A1 h φ⁻¹ hg
  rwa [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply] at this

theorem miyamotoI1_conj_mem_A1 {i g : GL (Fin 4) K} (hi : i ∈ miyamotoI1 h)
    (hg : g ∈ miyamotoA1 h) : i * g * i⁻¹ ∈ miyamotoA1 h := by
  have : CharP K 2 := h.charP
  obtain ⟨t, ht, rfl⟩ := (mem_miyamotoI1 h).mp hi
  obtain ⟨b, c, d, hb, hd, rfl⟩ := (mem_A1 h).mp hg
  have e : miyamotoIHom h (t, t) * miyamotoXGL h 0 b c d * (miyamotoIHom h (t, t))⁻¹ =
      (miyamotoIHom h (t⁻¹, t⁻¹))⁻¹ * miyamotoXGL h 0 b c d * miyamotoIHom h (t⁻¹, t⁻¹) := by
    rw [← map_inv, ← map_inv (miyamotoIHom h) (t⁻¹, t⁻¹), Prod.inv_mk, Prod.inv_mk, inv_inv]
  rw [e, miyamotoIHom_conj, mul_zero]
  have hbt : h.bar ((t⁻¹ : Kˣ) : K) = ((t⁻¹ : Kˣ) : K) := by
    rw [Units.val_inv_eq_inv_val, map_inv₀]
    exact congrArg _ ht
  refine (miyamotoXGL_mem_A1 h).mpr ⟨rfl, ?_, ?_⟩
  · dsimp only
    rw [map_mul, map_mul, hbt, hb, hbt]
  · dsimp only
    rw [map_mul, map_mul, hbt, hd, hbt]

theorem conj_mem_A1_iff_of_I1_N1 {i n g : GL (Fin 4) K} (hi : i ∈ miyamotoI1 h)
    (hn : n ∈ miyamotoN1 h) : i * n * g * (i * n)⁻¹ ∈ miyamotoA1 h ↔ g ∈ miyamotoA1 h := by
  have key : ∀ g, g ∈ miyamotoA1 h → i * n * g * (i * n)⁻¹ ∈ miyamotoA1 h := fun g hg => by
    have e : i * n * g * (i * n)⁻¹ = i * (n * g * n⁻¹) * i⁻¹ := by group
    rw [e]
    exact miyamotoI1_conj_mem_A1 h hi (miyamotoN1_conj_mem_A1 h hn hg)
  refine ⟨fun hg => ?_, key g⟩
  have e : g = n⁻¹ * (i⁻¹ * (i * n * g * (i * n)⁻¹) * i⁻¹⁻¹) * n⁻¹⁻¹ := by group
  rw [e]
  exact miyamotoN1_conj_mem_A1 h (inv_mem hn) (miyamotoI1_conj_mem_A1 h (inv_mem hi) hg)

end StabA1

section MainOne

theorem glAut_miyamotoI1Hom (φ : K ≃+* K) (t : Kˣ) :
    glAut φ (miyamotoI1Hom t) = miyamotoI1Hom (Units.map (φ : K →* K) t) := by
  apply Units.ext
  rw [coe_glAut, coe_miyamotoI1Hom, coe_miyamotoI1Hom, diagonal_map (map_zero φ)]
  congr 1
  ext i
  fin_cases i <;> simp [map_inv₀]

theorem glAut_eq_of_mem_miyamotoI1 {φ : K ≃+* K} (hφ : ∀ a : K, h.bar a = a → φ a = a)
    {g : GL (Fin 4) K} (hg : g ∈ miyamotoI1 h) : glAut φ g = g := by
  obtain ⟨t, ht, rfl⟩ := (mem_miyamotoI1' h).mp hg
  rw [glAut_miyamotoI1Hom]
  congr 1
  exact Units.ext (hφ _ ht)

theorem glAut_mem_miyamotoN1 (φ : K ≃+* K) {n : GL (Fin 4) K} (hn : n ∈ miyamotoN1 h) :
    glAut φ n ∈ miyamotoN1 h := by
  obtain ⟨m, rfl⟩ := hn
  refine ⟨SpecialLinearGroup.map (φ : K →+* K) m, Units.ext ?_⟩
  rw [coe_miyamotoN1_elem, coe_glAut, coe_miyamotoN1_elem]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [miyamotoN1Mat, map_bar_comm]

theorem fixes_of_refl_or_bar {φ : K ≃+* K} (hφ : φ = RingEquiv.refl K ∨ ∀ c, φ c = h.bar c) :
    ∀ a : K, h.bar a = a → φ a = a := by
  intro a ha
  rcases hφ with rfl | hφ
  · rfl
  · rw [hφ, ha]

theorem fixes_fixedField_of_conj_I1 {s : GL (Fin 4) K} {φ : K ≃+* K}
    (h02 : (s : Matrix (Fin 4) (Fin 4) K) 0 2 = 0) (h12 : (s : Matrix (Fin 4) (Fin 4) K) 1 2 = 0)
    (hc : ∀ t : Kˣ, h.bar t = t → s * glAut φ (miyamotoI1Hom t) * s⁻¹ = miyamotoI1Hom t) :
    ∀ a : K, h.bar a = a → φ a = a := by
  have hdet : (s : Matrix (Fin 4) (Fin 4) K).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp s.isUnit).ne_zero
  have hcol : (s : Matrix (Fin 4) (Fin 4) K) 2 2 ≠ 0 ∨ (s : Matrix (Fin 4) (Fin 4) K) 3 2 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hdet (Matrix.det_eq_zero_of_column_eq_zero 2 fun i => by
      fin_cases i
      exacts [h02, h12, hcon.1, hcon.2])
  intro a ha
  by_cases ha0 : a = 0
  · rw [ha0, map_zero]
  have e := hc (Units.mk0 a ha0) ha
  have e1 : s * glAut φ (miyamotoI1Hom (Units.mk0 a ha0)) =
      miyamotoI1Hom (Units.mk0 a ha0) * s := by
    calc s * glAut φ (miyamotoI1Hom (Units.mk0 a ha0)) =
        (s * glAut φ (miyamotoI1Hom (Units.mk0 a ha0)) * s⁻¹) * s := by group
      _ = _ := by rw [e]
  have e' := congrArg Units.val e1
  rw [Units.val_mul, Units.val_mul, glAut_miyamotoI1Hom, coe_miyamotoI1Hom,
    coe_miyamotoI1Hom] at e'
  have hφa : φ a ≠ 0 := (map_ne_zero φ).mpr ha0
  have key : ∀ k : Fin 4, k = 2 ∨ k = 3 → (s : Matrix (Fin 4) (Fin 4) K) k 2 ≠ 0 → φ a = a := by
    intro k hk hs
    have e2 := congrFun (congrFun e' k) 2
    rw [mul_diagonal, diagonal_mul] at e2
    rcases hk with rfl | rfl <;>
    · simp at e2
      have := mul_left_cancel₀ hs (e2.trans (mul_comm _ _))
      exact inv_injective this
  rcases hcol with hs | hs
  · exact key 2 (Or.inl rfl) hs
  · exact key 3 (Or.inr rfl) hs

theorem fixes_miyamotoI1_and_stabilizes_A1_iff (hf : 2 ≤ f)
    (α : MulAut (gramSU h (miyamotoJ4 K))) :
    ((∀ g : gramSU h (miyamotoJ4 K), (g : GL (Fin 4) K) ∈ miyamotoI1 h → α g = g) ∧
      ∀ g : gramSU h (miyamotoJ4 K),
        ((α g : gramSU h (miyamotoJ4 K)) : GL (Fin 4) K) ∈ miyamotoA1 h ↔
          (g : GL (Fin 4) K) ∈ miyamotoA1 h) ↔
      ∃ s : gramSU h (miyamotoJ4 K), (∃ i ∈ miyamotoI1 h, ∃ n ∈ miyamotoN1 h,
        (s : GL (Fin 4) K) = i * n) ∧ ∃ φ : K ≃+* K, (φ = RingEquiv.refl K ∨
          ∀ c, φ c = h.bar c) ∧ α = MulAut.conj s * miyamotoFieldAut h φ := by
  have : CharP K 2 := h.charP
  constructor
  · rintro ⟨hI, hA⟩
    obtain ⟨s, hs⟩ := exists_eq_conj_mul_fieldAut h α
    set φ := miyamotoFieldFactor h α with hφdef
    set x₀ : gramSU h (miyamotoJ4 K) := ⟨miyamotoXGL h 0 0 1 0,
      miyamotoUnipotent_le_SU h true false ((miyamotoXGL_mem_A1 h).mpr ⟨rfl, map_zero _,
        map_zero _⟩)⟩ with hx₀
    have hx₀A : (x₀ : GL (Fin 4) K) ∈ miyamotoA1 h :=
      (miyamotoXGL_mem_A1 h).mpr ⟨rfl, map_zero _, map_zero _⟩
    set y := α⁻¹ x₀ with hydef
    have hy : (y : GL (Fin 4) K) ∈ miyamotoA1 h :=
      (hA y).mp (by rw [hydef, MulAut.apply_inv_self]; exact hx₀A)
    have hconj : (s : GL (Fin 4) K)⁻¹ * miyamotoXGL h 0 0 1 0 * s ∈ miyamotoA1 h := by
      have e : ((α y : gramSU h (miyamotoJ4 K)) : GL (Fin 4) K) = miyamotoXGL h 0 0 1 0 := by
        rw [hydef, MulAut.apply_inv_self]
      rw [hs] at e
      simp only [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
        coe_miyamotoFieldAut_apply] at e
      have e2 : glAut φ (y : GL (Fin 4) K) =
          (s : GL (Fin 4) K)⁻¹ * miyamotoXGL h 0 0 1 0 * s := by
        rw [← e]
        group
      rw [← e2]
      exact glAut_mem_A1 h φ hy
    obtain ⟨h02, -, h12, -⟩ := upper_right_eq_zero_of_conj_mem_A1 h hconj
    have hc : ∀ t : Kˣ, h.bar t = t →
        (s : GL (Fin 4) K) * glAut φ (miyamotoI1Hom t) * (s : GL (Fin 4) K)⁻¹ =
          miyamotoI1Hom t := by
      intro t ht
      have hi : miyamotoI1Hom t ∈ miyamotoI1 h := (mem_miyamotoI1' h).mpr ⟨t, ht, rfl⟩
      have e := congrArg (fun g : gramSU h (miyamotoJ4 K) => (g : GL (Fin 4) K))
        (hI ⟨_, miyamotoI1_le_gramSU h hi⟩ hi)
      rw [hs] at e
      simpa [MulAut.conj_apply] using e
    have hφF := fixes_fixedField_of_conj_I1 h h02 h12 hc
    have hφ : φ = RingEquiv.refl K ∨ ∀ c, φ c = h.bar c :=
      ringEquiv_eq_refl_or_bar_of_fixes h fun a ha => hφF a ((h.mem_fixedField).mp ha)
    obtain ⟨t, ht, ht2⟩ := exists_fixed_unit_sq_ne_one h hf
    have hcomm : (s : GL (Fin 4) K) * miyamotoI1Hom t = miyamotoI1Hom t * s := by
      have e := hc t ht
      rw [glAut_eq_of_mem_miyamotoI1 h hφF ((mem_miyamotoI1' h).mpr ⟨t, ht, rfl⟩)] at e
      calc (s : GL (Fin 4) K) * miyamotoI1Hom t =
          (s * miyamotoI1Hom t * (s : GL (Fin 4) K)⁻¹) * s := by group
        _ = _ := by rw [e]
    exact ⟨s, exists_miyamotoI1_N1_of_commute h ht2 s.2 hcomm, φ, hφ, hs⟩
  · rintro ⟨s, ⟨i, hi, n, hn, hs⟩, φ, hφ, rfl⟩
    have hφF := fixes_of_refl_or_bar h hφ
    refine ⟨fun g hg => Subtype.ext ?_, fun g => ?_⟩
    · rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
        Subgroup.coe_inv, coe_miyamotoFieldAut_apply, glAut_eq_of_mem_miyamotoI1 h hφF hg, hs,
        commute_miyamotoI1_of_mul h hi hn hg]
      group
    · rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
        Subgroup.coe_inv, coe_miyamotoFieldAut_apply, hs, conj_mem_A1_iff_of_I1_N1 h hi hn,
        glAut_mem_A1_iff]

end MainOne

section AmbientOne

variable {G : Type} [Group G] (L : Subgroup G) (η : L ≃* gramSU h (miyamotoJ4 K))

theorem exists_sq_eq_miyamotoI1_N1_mul (hf : 2 ≤ f) (x : normalizer (L : Set G))
    (hxI : (x : G) ∈ centralizer (miyamotoI1G h L η : Set G))
    (hxA : (x : G) ∈ normalizer (miyamotoA1G h L η : Set G)) :
    ∃ s : gramSU h (miyamotoJ4 K), (∃ i ∈ miyamotoI1 h, ∃ n ∈ miyamotoN1 h,
      (s : GL (Fin 4) K) = i * n) ∧
        ∃ c ∈ centralizer (L : Set G), (x : G) ^ 2 = (η.symm s : G) * c := by
  obtain ⟨s, ⟨i, hi, n, hn, hs⟩, φ, hφ, hα⟩ :=
    (fixes_miyamotoI1_and_stabilizes_A1_iff h hf (miyamotoAct h L η x)).mp
      ⟨fun g hg => miyamotoAct_apply_of_mem_centralizer h L η x hxI hg,
        fun g => miyamotoAct_mem_iff_of_mem_normalizer h L η x hxA g⟩
  have hφF := fixes_of_refl_or_bar h hφ
  have hφ2 : φ * φ = 1 := by
    rcases hφ with rfl | hφ
    · rfl
    · exact RingEquiv.ext fun c => by
        change φ (φ c) = c
        rw [hφ, hφ, h.bar_bar]
  set s' : gramSU h (miyamotoJ4 K) := s * miyamotoFieldAut h φ s with hs'
  have hα2 : miyamotoAct h L η (x ^ 2) = MulAut.conj s' := by
    have hff : miyamotoFieldAut h φ * miyamotoFieldAut h φ = 1 := by
      rw [← miyamotoFieldHom_apply, ← map_mul, hφ2, map_one]
    rw [map_pow, hα, hs', map_mul, ← miyamotoFieldAut_mul_conj_mul_inv h φ s]
    calc (MulAut.conj s * miyamotoFieldAut h φ) ^ 2 = MulAut.conj s *
        (miyamotoFieldAut h φ * MulAut.conj s * (miyamotoFieldAut h φ)⁻¹) *
          (miyamotoFieldAut h φ * miyamotoFieldAut h φ) := by rw [sq]; group
      _ = _ := by rw [hff, mul_one]
  obtain ⟨c, hc, hxc⟩ := exists_eq_mul_of_miyamotoAct_eq_conj h L η (x ^ 2) s' hα2
  refine ⟨s', ⟨i * i, mul_mem hi hi, n * glAut φ n, mul_mem hn (glAut_mem_miyamotoN1 h φ hn),
    ?_⟩, c, hc, by rw [← hxc]; rfl⟩
  rw [hs', Subgroup.coe_mul, coe_miyamotoFieldAut_apply, hs, map_mul,
    glAut_eq_of_mem_miyamotoI1 h hφF hi]
  have hni : n * i = i * n := miyamotoN1_commute_I1 h hn hi
  calc i * n * (i * glAut φ n) = i * (n * i) * glAut φ n := by group
    _ = i * i * (n * glAut φ n) := by rw [hni]; group

end AmbientOne

end CFSG.LocalAnalysis.EvenBN.U4
