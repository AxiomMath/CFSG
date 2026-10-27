module

public import CFSG.LocalAnalysis.EvenBN.U4.Model.ParabolicG

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

section Action

variable [CharP K 2]

theorem miyamotoN1Hom_conj_A1 (m : SpecialLinearGroup (Fin 2) K) {b c d : K} (hb : h.bar b = b)
    (hd : h.bar d = d) :
    (miyamotoN1Hom h m)⁻¹ * miyamotoXGL h 0 b c d * miyamotoN1Hom h m =
      miyamotoXGL h 0
        (h.bar ((m : Matrix (Fin 2) (Fin 2) K) 1 1) * (c * (m : Matrix (Fin 2) (Fin 2) K) 0 1 +
            b * (m : Matrix (Fin 2) (Fin 2) K) 1 1) -
          h.bar ((m : Matrix (Fin 2) (Fin 2) K) 0 1) * (d * (m : Matrix (Fin 2) (Fin 2) K) 0 1 +
            h.bar c * (m : Matrix (Fin 2) (Fin 2) K) 1 1))
        (h.bar ((m : Matrix (Fin 2) (Fin 2) K) 1 1) * (c * (m : Matrix (Fin 2) (Fin 2) K) 0 0 +
            b * (m : Matrix (Fin 2) (Fin 2) K) 1 0) -
          h.bar ((m : Matrix (Fin 2) (Fin 2) K) 0 1) * (d * (m : Matrix (Fin 2) (Fin 2) K) 0 0 +
            h.bar c * (m : Matrix (Fin 2) (Fin 2) K) 1 0))
        (-h.bar ((m : Matrix (Fin 2) (Fin 2) K) 1 0) * (c * (m : Matrix (Fin 2) (Fin 2) K) 0 0 +
            b * (m : Matrix (Fin 2) (Fin 2) K) 1 0) +
          h.bar ((m : Matrix (Fin 2) (Fin 2) K) 0 0) * (d * (m : Matrix (Fin 2) (Fin 2) K) 0 0 +
            h.bar c * (m : Matrix (Fin 2) (Fin 2) K) 1 0)) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hbb := h.bar_bar
  have hdet := m.2
  rw [Matrix.det_fin_two] at hdet
  have hdet' : h.bar ((m : Matrix (Fin 2) (Fin 2) K) 0 0) *
      h.bar ((m : Matrix (Fin 2) (Fin 2) K) 1 1) - h.bar ((m : Matrix (Fin 2) (Fin 2) K) 0 1) *
      h.bar ((m : Matrix (Fin 2) (Fin 2) K) 1 0) = 1 := by
    rw [← map_mul, ← map_mul, ← map_sub, hdet, map_one]
  apply Units.ext
  rw [← map_inv, Units.val_mul, Units.val_mul, coe_miyamotoN1Hom, coe_miyamotoN1Hom]
  simp only [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, coe_miyamotoXGL]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [miyamotoN1Mat, miyamotoX, Matrix.mul_apply, Fin.sum_univ_four, hbb, hb, hd]
  all_goals first
    | ring1
    | linear_combination hdet
    | linear_combination hdet'
    | linear_combination (h.bar ((m : Matrix (Fin 2) (Fin 2) K) 0 0) * d *
        (m : Matrix (Fin 2) (Fin 2) K) 0 1 - h.bar ((m : Matrix (Fin 2) (Fin 2) K) 1 0) * b *
        (m : Matrix (Fin 2) (Fin 2) K) 1 1) * h2

@[expose] def miyamotoQA1 (x : GL (Fin 4) K) : K :=
  (x : Matrix (Fin 4) (Fin 4) K) 2 0 * h.bar ((x : Matrix (Fin 4) (Fin 4) K) 2 0) +
    (x : Matrix (Fin 4) (Fin 4) K) 2 1 * (x : Matrix (Fin 4) (Fin 4) K) 3 0

omit [CharP K 2] in
@[simp] theorem miyamotoQA1_miyamotoXGL (b c d : K) :
    miyamotoQA1 h (miyamotoXGL h 0 b c d) = c * h.bar c + b * d :=
  rfl

theorem miyamotoQ_identity {p q r s b c d : K} (hdet : p * s - q * r = 1)
    (hdet' : h.bar p * h.bar s - h.bar q * h.bar r = 1) (hb : h.bar b = b) (hd : h.bar d = d) :
    (h.bar s * (c * p + b * r) - h.bar q * (d * p + h.bar c * r)) *
        h.bar (h.bar s * (c * p + b * r) - h.bar q * (d * p + h.bar c * r)) +
      (h.bar s * (c * q + b * s) - h.bar q * (d * q + h.bar c * s)) *
        (-h.bar r * (c * p + b * r) + h.bar p * (d * p + h.bar c * r)) =
      c * h.bar c + b * d := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hbb := h.bar_bar
  simp only [map_sub, map_mul, map_add, hbb, hb, hd]
  linear_combination (c * h.bar c - b * d) * (h.bar p * h.bar s - h.bar q * h.bar r) * hdet +
    (c * h.bar c - b * d) * hdet' +
    ((h.bar s * (c * q + b * s) - h.bar q * (d * q + h.bar c * s)) *
        (-h.bar r * (c * p + b * r) + h.bar p * (d * p + h.bar c * r)) +
      (h.bar s * (c * p + b * r) - h.bar q * (d * p + h.bar c * r)) *
        (h.bar r * b * s - h.bar p * d * q) - b * d) * h2

theorem miyamotoQA1_conj_N1 {n x : GL (Fin 4) K} (hn : n ∈ miyamotoN1 h)
    (hx : x ∈ miyamotoA1 h) : miyamotoQA1 h (n⁻¹ * x * n) = miyamotoQA1 h x := by
  obtain ⟨m, rfl⟩ := hn
  obtain ⟨b, c, d, hb, hd, rfl⟩ := (mem_A1 h).1 hx
  have hdet := m.2
  rw [Matrix.det_fin_two] at hdet
  have hdet' : h.bar ((m : Matrix (Fin 2) (Fin 2) K) 0 0) *
      h.bar ((m : Matrix (Fin 2) (Fin 2) K) 1 1) - h.bar ((m : Matrix (Fin 2) (Fin 2) K) 0 1) *
      h.bar ((m : Matrix (Fin 2) (Fin 2) K) 1 0) = 1 := by
    rw [← map_mul, ← map_mul, ← map_sub, hdet, map_one]
  change miyamotoQA1 h ((miyamotoN1Hom h m)⁻¹ * _ * miyamotoN1Hom h m) = _
  rw [miyamotoN1Hom_conj_A1 h m hb hd, miyamotoQA1_miyamotoXGL, miyamotoQA1_miyamotoXGL]
  exact miyamotoQ_identity h hdet hdet' hb hd

theorem miyamotoQA1_conj_I1 {t : Kˣ} (ht : h.bar t = t) {x : GL (Fin 4) K}
    (hx : x ∈ miyamotoA1 h) :
    miyamotoQA1 h ((miyamotoIHom h (t, t))⁻¹ * x * miyamotoIHom h (t, t)) =
      (t : K) ^ 4 * miyamotoQA1 h x := by
  obtain ⟨b, c, d, -, -, rfl⟩ := (mem_A1 h).1 hx
  rw [miyamotoI1_conj h ht, miyamotoQA1_miyamotoXGL, miyamotoQA1_miyamotoXGL]
  simp only [map_mul, map_pow, ht]
  ring

omit [CharP K 2] in
theorem bar_miyamotoQA1 {x : GL (Fin 4) K} (hx : x ∈ miyamotoA1 h) :
    h.bar (miyamotoQA1 h x) = miyamotoQA1 h x := by
  have : CharP K 2 := h.charP
  obtain ⟨b, c, d, hb, hd, rfl⟩ := (mem_A1 h).1 hx
  rw [miyamotoQA1_miyamotoXGL, map_add, map_mul, map_mul, h.bar_bar, hb, hd, mul_comm]

theorem miyamotoN1Hom_conj_z1 (m : SpecialLinearGroup (Fin 2) K) :
    (miyamotoN1Hom h m)⁻¹ * miyamotoXGL h 0 0 0 1 * miyamotoN1Hom h m =
      miyamotoXGL h 0
        (h.bar ((m : Matrix (Fin 2) (Fin 2) K) 0 1) * (m : Matrix (Fin 2) (Fin 2) K) 0 1)
        (h.bar ((m : Matrix (Fin 2) (Fin 2) K) 0 1) * (m : Matrix (Fin 2) (Fin 2) K) 0 0)
        (h.bar ((m : Matrix (Fin 2) (Fin 2) K) 0 0) * (m : Matrix (Fin 2) (Fin 2) K) 0 0) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [miyamotoN1Hom_conj_A1 h m (map_zero _) (map_one _), miyamotoXGL_inj]
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> simp
  · linear_combination (-(h.bar ((m : Matrix (Fin 2) (Fin 2) K) 0 1) *
      (m : Matrix (Fin 2) (Fin 2) K) 0 1)) * h2
  · linear_combination (-(h.bar ((m : Matrix (Fin 2) (Fin 2) K) 0 1) *
      (m : Matrix (Fin 2) (Fin 2) K) 0 0)) * h2

theorem exists_N1_conj_z1 {x : GL (Fin 4) K} (hx : x ∈ miyamotoA1 h) (hx1 : x ≠ 1)
    (hQ : miyamotoQA1 h x = 0) :
    ∃ n ∈ miyamotoN1 h, n⁻¹ * miyamotoXGL h 0 0 0 1 * n = x := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hbb := h.bar_bar
  obtain ⟨b, c, d, hb, hd, rfl⟩ := (mem_A1 h).1 hx
  rw [miyamotoQA1_miyamotoXGL] at hQ
  by_cases hd0 : d = 0
  · subst hd0
    have hc : c = 0 := by
      have : c * h.bar c = 0 := by simpa using hQ
      rcases mul_eq_zero.1 this with e | e
      · exact e
      · exact (map_eq_zero h.bar).1 e
    subst hc
    have hb0 : b ≠ 0 := fun e => hx1 (by rw [e, miyamotoXGL_zero])
    obtain ⟨q', hq'⟩ := exists_unit_norm_eq h hb hb0
    have hm : (!![0, (q' : K); (q' : K)⁻¹, 0] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
      simp [Matrix.det_fin_two]
      exact CharTwo.neg_eq 1
    obtain ⟨m', hm'⟩ : ∃ m' : SpecialLinearGroup (Fin 2) K,
        (m' : Matrix (Fin 2) (Fin 2) K) = !![0, (q' : K); (q' : K)⁻¹, 0] := ⟨⟨_, hm⟩, rfl⟩
    refine ⟨miyamotoN1Hom h m', ⟨m', rfl⟩, ?_⟩
    rw [miyamotoN1Hom_conj_z1, miyamotoXGL_inj, hm']
    refine ⟨rfl, ?_, by simp, by simp⟩
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    rw [mul_comm]
    exact hq'
  · obtain ⟨p, hp⟩ := exists_unit_norm_eq h hd hd0
    have hp0 : (p : K) ≠ 0 := p.ne_zero
    have hbp : h.bar (p : K) ≠ 0 := by simp
    have hm : (!![(p : K), h.bar c / h.bar p; 0, (p : K)⁻¹] : Matrix (Fin 2) (Fin 2) K).det =
        1 := by
      simp [Matrix.det_fin_two, hp0]
    obtain ⟨m', hm'⟩ : ∃ m' : SpecialLinearGroup (Fin 2) K,
        (m' : Matrix (Fin 2) (Fin 2) K) = !![(p : K), h.bar c / h.bar p; 0, (p : K)⁻¹] :=
      ⟨⟨_, hm⟩, rfl⟩
    refine ⟨miyamotoN1Hom h m', ⟨m', rfl⟩, ?_⟩
    rw [miyamotoN1Hom_conj_z1, miyamotoXGL_inj, hm']
    refine ⟨rfl, ?_, ?_, ?_⟩ <;>
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, map_div₀, hbb]
    · field_simp
      rw [hp]
      linear_combination hQ - (b * d) * h2
    · field_simp
    · rw [mul_comm]
      exact hp

theorem det_omega_add_T {ω s b c d : K} (hs0 : s ≠ 0)
    (hQ : c * h.bar c + b * d = s ^ 2) :
    (ω + h.bar ω * (c / s)) * (ω + h.bar ω * (h.bar c / s)) - h.bar ω * (b / s) *
        (h.bar ω * (d / s)) =
      (ω + h.bar ω) ^ 2 + ω * h.bar ω * (c + h.bar c) / s := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  field_simp
  linear_combination (h.bar ω) ^ 2 * hQ + (- ω * h.bar ω * s ^ 2 - (h.bar ω) ^ 2 * b * d) * h2

theorem exists_N1_conj_scalar {x : GL (Fin 4) K} (hx : x ∈ miyamotoA1 h) {s : K}
    (hs : h.bar s = s) (hs0 : s ≠ 0) (hQ : miyamotoQA1 h x = s ^ 2) :
    ∃ n ∈ miyamotoN1 h, n⁻¹ * miyamotoXGL h 0 0 s 0 * n = x := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hbb := h.bar_bar
  obtain ⟨b, c, d, hb, hd, rfl⟩ := (mem_A1 h).1 hx
  rw [miyamotoQA1_miyamotoXGL] at hQ
  obtain ⟨ω, hω⟩ : ∃ ω : K, (ω + h.bar ω) ^ 2 + ω * h.bar ω * (c + h.bar c) / s ≠ 0 := by
    by_cases htr : c + h.bar c = 0
    · obtain ⟨ω, hω⟩ := h.exists_bar_ne
      refine ⟨ω, ?_⟩
      rw [htr, mul_zero, zero_div, add_zero]
      exact pow_ne_zero 2 (add_bar_ne_zero h hω)
    · refine ⟨1, ?_⟩
      rw [map_one, CharTwo.add_self_eq_zero, sq, zero_mul, zero_add, one_mul, one_mul]
      exact div_ne_zero htr hs0
  set μ := (ω + h.bar ω) ^ 2 + ω * h.bar ω * (c + h.bar c) / s with hμ
  have hμF : h.bar μ = μ := by
    rw [hμ]
    simp only [map_add, map_pow, map_mul, map_div₀, hbb, hs]
    ring
  obtain ⟨lam, hlam, hlamF⟩ := exists_sq_eq_of_charTwo h μ⁻¹
  have hlam' : h.bar lam = lam := hlamF (by rw [map_inv₀, hμF])
  have hlamμ : lam ^ 2 * μ = 1 := by rw [hlam, inv_mul_cancel₀ hω]
  have hlam2 : lam ^ 2 * (s * (ω + h.bar ω) ^ 2 + ω * h.bar ω * (c + h.bar c)) = s := by
    have e : lam ^ 2 * (s * (ω + h.bar ω) ^ 2 + ω * h.bar ω * (c + h.bar c)) =
        s * (lam ^ 2 * μ) := by
      rw [hμ]
      field_simp
    rw [e, hlamμ, mul_one]
  have hdet0 : (ω + h.bar ω * (c / s)) * (ω + h.bar ω * (h.bar c / s)) - h.bar ω * (b / s) *
      (h.bar ω * (d / s)) = μ := det_omega_add_T h (ω := ω) hs0 hQ
  have hm : (!![lam * (ω + h.bar ω * (c / s)), lam * (h.bar ω * (b / s));
      lam * (h.bar ω * (d / s)), lam * (ω + h.bar ω * (h.bar c / s))] :
        Matrix (Fin 2) (Fin 2) K).det = 1 := by
    rw [Matrix.det_fin_two_of, ← hlamμ, ← hdet0]
    ring
  obtain ⟨m', hm'⟩ : ∃ m' : SpecialLinearGroup (Fin 2) K,
      (m' : Matrix (Fin 2) (Fin 2) K) = !![lam * (ω + h.bar ω * (c / s)),
        lam * (h.bar ω * (b / s)); lam * (h.bar ω * (d / s)),
        lam * (ω + h.bar ω * (h.bar c / s))] := ⟨⟨_, hm⟩, rfl⟩
  refine ⟨miyamotoN1Hom h m', ⟨m', rfl⟩, ?_⟩
  rw [miyamotoN1Hom_conj_A1 h m' (map_zero _) (map_zero _), miyamotoXGL_inj, hm']
  refine ⟨rfl, ?_, ?_, ?_⟩ <;>
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, map_mul, map_add, map_div₀, hbb, hb, hd, hs, hlam']
  · field_simp
    linear_combination (s * b) * hlam2 - lam ^ 2 * s * b * (s * ω ^ 2 + s * ω * h.bar ω +
      ω * h.bar ω * h.bar c) * h2
  · field_simp
    linear_combination (c * s) * hlam2 - lam ^ 2 * s * ω * h.bar ω * hQ -
      lam ^ 2 * c * s ^ 2 * ω * h.bar ω * h2
  · field_simp
    linear_combination (d * s) * hlam2 - lam ^ 2 * d * s * (s * ω ^ 2 + s * ω * h.bar ω +
      ω * h.bar ω * c) * h2

end Action

section Orbits

theorem miyamotoZ1_eq : miyamotoZ1 K = miyamotoXGL h 0 0 0 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [miyamotoZ1, miyamotoX]

theorem miyamotoZ2_eq : LocalAnalysis.miyamotoZ2 K = miyamotoXGL h 0 0 1 0 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [LocalAnalysis.miyamotoZ2, miyamotoX]

variable [CharP K 2]

omit [CharP K 2] in
theorem miyamotoI1_le_normalizer_N1 :
    miyamotoI1 h ≤ normalizer (miyamotoN1 h : Set (GL (Fin 4) K)) := fun _ hi =>
  centralizer_le_normalizer _ (mem_centralizer_iff.2 fun _ hn =>
    (miyamotoI1_commute_N1 h hi hn).symm)

omit [CharP K 2] in
theorem exists_mul_of_mem_I1_sup_N1 {g : GL (Fin 4) K} (hg : g ∈ miyamotoI1 h ⊔ miyamotoN1 h) :
    ∃ i ∈ miyamotoI1 h, ∃ n ∈ miyamotoN1 h, g = i * n := by
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _
    (miyamotoI1_le_normalizer_N1 h)] at hg
  obtain ⟨i, hi, n, hn, rfl⟩ := hg
  exact ⟨i, hi, n, hn, rfl⟩

theorem conj_mem_A1_and_Q_of_mem_I1_sup_N1 {g x : GL (Fin 4) K}
    (hg : g ∈ miyamotoI1 h ⊔ miyamotoN1 h) (hx : x ∈ miyamotoA1 h) :
    g⁻¹ * x * g ∈ miyamotoA1 h ∧
      ∃ t : Kˣ, h.bar t = t ∧ miyamotoQA1 h (g⁻¹ * x * g) = (t : K) ^ 4 * miyamotoQA1 h x := by
  obtain ⟨i, hi, n, hn, rfl⟩ := exists_mul_of_mem_I1_sup_N1 h hg
  obtain ⟨t, ht, rfl⟩ := (mem_miyamotoI1 h).1 hi
  have hix : (miyamotoIHom h (t, t))⁻¹ * x * miyamotoIHom h (t, t) ∈ miyamotoA1 h :=
    miyamotoIHom_conj_mem_unipotent h _ hx
  have e : (miyamotoIHom h (t, t) * n)⁻¹ * x * (miyamotoIHom h (t, t) * n) =
      n⁻¹ * ((miyamotoIHom h (t, t))⁻¹ * x * miyamotoIHom h (t, t)) * n := by group
  rw [e]
  refine ⟨conj_mem_A1_of_mem_N1 h hn hix, t, ht, ?_⟩
  rw [miyamotoQA1_conj_N1 h hn hix, miyamotoQA1_conj_I1 h ht hx]

theorem miyamoto_orbit_z1_N1 :
    {y | ∃ n ∈ miyamotoN1 h, n⁻¹ * miyamotoZ1 K * n = y} =
      {x | x ∈ miyamotoA1 h ∧ x ≠ 1 ∧ miyamotoQA1 h x = 0} := by
  rw [miyamotoZ1_eq h]
  have hz : miyamotoXGL h 0 0 0 1 ∈ miyamotoA1 h :=
    (miyamotoXGL_mem_A1 h).2 ⟨rfl, map_zero _, map_one _⟩
  ext y
  constructor
  · rintro ⟨n, hn, rfl⟩
    refine ⟨conj_mem_A1_of_mem_N1 h hn hz, fun e => ?_, ?_⟩
    · have : miyamotoXGL h 0 0 0 1 = 1 := by
        calc miyamotoXGL h 0 0 0 1 = n * (n⁻¹ * miyamotoXGL h 0 0 0 1 * n) * n⁻¹ := by group
          _ = 1 := by rw [e, mul_one, mul_inv_cancel]
      rw [← miyamotoXGL_zero h, miyamotoXGL_inj] at this
      exact one_ne_zero this.2.2.2
    · rw [miyamotoQA1_conj_N1 h hn hz, miyamotoQA1_miyamotoXGL]
      simp
  · rintro ⟨hy, hy1, hQ⟩
    exact exists_N1_conj_z1 h hy hy1 hQ

theorem miyamoto_orbit_z1_I1N1 :
    {y | ∃ g ∈ miyamotoI1 h ⊔ miyamotoN1 h, g⁻¹ * miyamotoZ1 K * g = y} =
      {x | x ∈ miyamotoA1 h ∧ x ≠ 1 ∧ miyamotoQA1 h x = 0} := by
  rw [← miyamoto_orbit_z1_N1 h]
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    have hz : miyamotoZ1 K ∈ miyamotoA1 h := by
      rw [miyamotoZ1_eq h]
      exact (miyamotoXGL_mem_A1 h).2 ⟨rfl, map_zero _, map_one _⟩
    obtain ⟨hA, t, -, hQ⟩ := conj_mem_A1_and_Q_of_mem_I1_sup_N1 h hg hz
    have hQ0 : miyamotoQA1 h (miyamotoZ1 K) = 0 := by
      rw [miyamotoZ1_eq h, miyamotoQA1_miyamotoXGL]
      simp
    rw [hQ0, mul_zero] at hQ
    rw [miyamoto_orbit_z1_N1 h]
    refine ⟨hA, fun e => ?_, hQ⟩
    have : miyamotoZ1 K = 1 := by
      calc miyamotoZ1 K = g * (g⁻¹ * miyamotoZ1 K * g) * g⁻¹ := by group
        _ = 1 := by rw [e, mul_one, mul_inv_cancel]
    rw [miyamotoZ1_eq h, ← miyamotoXGL_zero h, miyamotoXGL_inj] at this
    exact one_ne_zero this.2.2.2
  · rintro _ ⟨n, hn, rfl⟩
    exact ⟨n, mem_sup_right hn, rfl⟩

theorem miyamoto_orbit_z2_N1 :
    {y | ∃ n ∈ miyamotoN1 h, n⁻¹ * LocalAnalysis.miyamotoZ2 K * n = y} =
      {x | x ∈ miyamotoA1 h ∧ miyamotoQA1 h x = 1} := by
  rw [miyamotoZ2_eq h]
  have hz : miyamotoXGL h 0 0 1 0 ∈ miyamotoA1 h :=
    (miyamotoXGL_mem_A1 h).2 ⟨rfl, map_zero _, map_zero _⟩
  ext y
  constructor
  · rintro ⟨n, hn, rfl⟩
    refine ⟨conj_mem_A1_of_mem_N1 h hn hz, ?_⟩
    rw [miyamotoQA1_conj_N1 h hn hz, miyamotoQA1_miyamotoXGL]
    simp
  · rintro ⟨hy, hQ⟩
    exact exists_N1_conj_scalar h hy (map_one _) one_ne_zero (by rw [hQ, one_pow])

theorem miyamoto_orbit_z2_I1N1 :
    {y | ∃ g ∈ miyamotoI1 h ⊔ miyamotoN1 h, g⁻¹ * LocalAnalysis.miyamotoZ2 K * g = y} =
      {x | x ∈ miyamotoA1 h ∧ miyamotoQA1 h x ≠ 0} := by
  rw [miyamotoZ2_eq h]
  have hz : miyamotoXGL h 0 0 1 0 ∈ miyamotoA1 h :=
    (miyamotoXGL_mem_A1 h).2 ⟨rfl, map_zero _, map_zero _⟩
  ext y
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨hA, t, -, hQ⟩ := conj_mem_A1_and_Q_of_mem_I1_sup_N1 h hg hz
    refine ⟨hA, ?_⟩
    rw [hQ, miyamotoQA1_miyamotoXGL]
    simp [t.ne_zero]
  · rintro ⟨hy, hQ⟩
    obtain ⟨s, hs2, hsF⟩ := exists_sq_eq_of_charTwo h (miyamotoQA1 h y)
    have hs : h.bar s = s := hsF (bar_miyamotoQA1 h hy)
    have hs0 : s ≠ 0 := by
      rintro rfl
      exact hQ (by rw [← hs2]; ring)
    obtain ⟨n, hn, e⟩ := exists_N1_conj_scalar h hy hs hs0 hs2.symm
    obtain ⟨t₀, ht2, htF⟩ := exists_sq_eq_of_charTwo h s
    have ht : h.bar t₀ = t₀ := htF hs
    have ht0 : t₀ ≠ 0 := by
      rintro rfl
      exact hs0 (by rw [← ht2]; ring)
    refine ⟨miyamotoIHom h (Units.mk0 t₀ ht0, Units.mk0 t₀ ht0) * n,
      mul_mem (mem_sup_left ((mem_miyamotoI1 h).2 ⟨_, ht, rfl⟩)) (mem_sup_right hn), ?_⟩
    rw [← e, _root_.mul_inv_rev]
    have e' := miyamotoI1_conj h (t := Units.mk0 t₀ ht0) ht 0 0 1 0
    simp only [Units.val_mk0, mul_zero, mul_one, ht2] at e'
    rw [← e']
    group

theorem miyamoto_two_orbits_A1 {x : GL (Fin 4) K} (hx : x ∈ miyamotoA1 h) (hx1 : x ≠ 1) :
    (x ∈ {y | ∃ g ∈ miyamotoI1 h ⊔ miyamotoN1 h, g⁻¹ * miyamotoZ1 K * g = y} ↔
      x ∉ {y | ∃ g ∈ miyamotoI1 h ⊔ miyamotoN1 h, g⁻¹ * LocalAnalysis.miyamotoZ2 K * g = y}) := by
  rw [miyamoto_orbit_z1_I1N1 h, miyamoto_orbit_z2_I1N1 h]
  simp only [Set.mem_ofPred_eq]
  tauto

theorem miyamotoN1_irreducible_A1 {B : Subgroup (GL (Fin 4) K)} (hB : B ≤ miyamotoA1 h)
    (hinv : ∀ n ∈ miyamotoN1 h, ∀ x ∈ B, n⁻¹ * x * n ∈ B) : B = ⊥ ∨ B = miyamotoA1 h := by
  have hbb := h.bar_bar
  by_cases hbot : B = ⊥
  · exact Or.inl hbot
  refine Or.inr (le_antisymm hB ?_)
  obtain ⟨x, hxB, hx1⟩ : ∃ x ∈ B, x ≠ 1 := by
    obtain ⟨⟨x, hx⟩, hne⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hbot
    exact ⟨x, hx, fun e => hne (Subtype.ext e)⟩
  have hinv' : ∀ n ∈ miyamotoN1 h, ∀ y, n⁻¹ * y * n ∈ B → y ∈ B := by
    intro n hn y hy
    have := hinv n⁻¹ (inv_mem hn) _ hy
    rwa [inv_inv, show n * (n⁻¹ * y * n) * n⁻¹ = y by group] at this
  have hz1 : miyamotoXGL h 0 0 0 1 ∈ B := by
    by_cases hQ : miyamotoQA1 h x = 0
    · obtain ⟨n, hn, e⟩ := exists_N1_conj_z1 h (hB hxB) hx1 hQ
      exact hinv' n hn _ (e ▸ hxB)
    · obtain ⟨s, hs2, hsF⟩ := exists_sq_eq_of_charTwo h (miyamotoQA1 h x)
      have hs : h.bar s = s := hsF (bar_miyamotoQA1 h (hB hxB))
      have hs0 : s ≠ 0 := by
        rintro rfl
        exact hQ (by rw [← hs2]; ring)
      obtain ⟨n, hn, e⟩ := exists_N1_conj_scalar h (hB hxB) hs hs0 hs2.symm
      have h1 : miyamotoXGL h 0 0 s 0 ∈ B := hinv' n hn _ (e ▸ hxB)
      have hy : miyamotoXGL h 0 0 s 1 ∈ miyamotoA1 h :=
        (miyamotoXGL_mem_A1 h).2 ⟨rfl, map_zero _, map_one _⟩
      obtain ⟨n', hn', e'⟩ := exists_N1_conj_scalar h hy hs hs0 (by
        rw [miyamotoQA1_miyamotoXGL, hs]
        ring)
      have h2 : miyamotoXGL h 0 0 s 1 ∈ B := e' ▸ hinv n' hn' _ h1
      have : miyamotoXGL h 0 0 0 1 = (miyamotoXGL h 0 0 s 0)⁻¹ * miyamotoXGL h 0 0 s 1 := by
        rw [miyamotoXGL_inv h (map_zero _), miyamotoXGL_mul h (map_zero _), miyamotoXGL_inj]
        refine ⟨by ring, by ring, ?_, ?_⟩
        · simp only [zero_mul, add_zero]
          exact (CharTwo.add_self_eq_zero s).symm
        · simp
      rw [this]
      exact mul_mem (inv_mem h1) h2
  have hrank1 : ∀ y ∈ miyamotoA1 h, miyamotoQA1 h y = 0 → y ∈ B := by
    intro y hy hQ
    by_cases hy1 : y = 1
    · rw [hy1]
      exact one_mem _
    · obtain ⟨n, hn, e⟩ := exists_N1_conj_z1 h hy hy1 hQ
      rw [← e]
      exact hinv n hn _ hz1
  intro y hy
  obtain ⟨b, c, d, hb, hd, rfl⟩ := (mem_A1 h).1 hy
  have hN : h.bar (c * h.bar c) = c * h.bar c := by rw [map_mul, hbb, mul_comm]
  have e1 : miyamotoXGL h 0 0 c 0 = miyamotoXGL h 0 (c * h.bar c) c 1 *
      miyamotoXGL h 0 (c * h.bar c) 0 0 * miyamotoXGL h 0 0 0 1 := by
    rw [miyamotoXGL_mul_eq h hN (a'' := 0) (b'' := 0) (c'' := c) (d'' := 1) (by ring)
      (CharTwo.add_self_eq_zero _).symm (by ring) (by simp),
      miyamotoXGL_mul_eq h (map_zero _) (a'' := 0) (b'' := 0) (c'' := c) (d'' := 0) (by ring)
      (by ring) (by ring) (by simp; exact (CharTwo.add_self_eq_zero 1).symm)]
  have e2 : miyamotoXGL h 0 b c d = miyamotoXGL h 0 b 0 0 * miyamotoXGL h 0 0 0 d *
      miyamotoXGL h 0 0 c 0 := by
    rw [miyamotoXGL_mul_eq h hb (a'' := 0) (b'' := b) (c'' := 0) (d'' := d) (by ring) (by ring)
      (by ring) (by simp),
      miyamotoXGL_mul_eq h hb (a'' := 0) (b'' := b) (c'' := c) (d'' := d) (by ring) (by ring)
      (by ring) (by simp)]
  rw [e2, e1]
  refine mul_mem (mul_mem (hrank1 _ ((miyamotoXGL_mem_A1 h).2 ⟨rfl, hb, map_zero _⟩) (by simp))
    (hrank1 _ ((miyamotoXGL_mem_A1 h).2 ⟨rfl, map_zero _, hd⟩) (by simp)))
    (mul_mem (mul_mem (hrank1 _ ((miyamotoXGL_mem_A1 h).2 ⟨rfl, hN, map_one _⟩) ?_)
      (hrank1 _ ((miyamotoXGL_mem_A1 h).2 ⟨rfl, hN, map_zero _⟩) (by simp))) hz1)
  rw [miyamotoQA1_miyamotoXGL, mul_one, CharTwo.add_self_eq_zero]

end Orbits

section Centralizers

variable [CharP K 2]

@[expose] def miyamotoN1F : Subgroup (GL (Fin 4) K) :=
  ((miyamotoN1Hom h).comp
    (SpecialLinearGroup.map (h.fixedField.subtype : h.fixedField →+* K))).range

omit [CharP K 2] in
theorem miyamotoN1F_hom_injective : Function.Injective ((miyamotoN1Hom h).comp
    (SpecialLinearGroup.map (h.fixedField.subtype : h.fixedField →+* K))) := by
  intro m m' e
  have e' := miyamotoN1Hom_injective h e
  ext i j
  have := congrArg (fun A : SpecialLinearGroup (Fin 2) K => (A : Matrix (Fin 2) (Fin 2) K) i j) e'
  simpa using this

@[expose] def miyamotoN1FEquiv : SpecialLinearGroup (Fin 2) h.fixedField ≃* miyamotoN1F h :=
  MonoidHom.ofInjective (miyamotoN1F_hom_injective h)

theorem miyamotoN1_inf_centralizer_z2 :
    miyamotoN1 h ⊓ centralizer ({LocalAnalysis.miyamotoZ2 K} : Set (GL (Fin 4) K)) =
      miyamotoN1F h := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hbb := h.bar_bar
  rw [miyamotoZ2_eq h]
  apply le_antisymm
  · intro g hg
    obtain ⟨hgN, hc⟩ := mem_inf.1 hg
    obtain ⟨m, hm⟩ := hgN
    have hgm : g = miyamotoN1Hom h m := hm.symm
    subst hgm
    have e : (miyamotoN1Hom h m)⁻¹ * miyamotoXGL h 0 0 1 0 * miyamotoN1Hom h m =
        miyamotoXGL h 0 0 1 0 := (mem_centralizer_singleton_iff_conj).1
      (mem_centralizer_singleton_iff.2 (mem_centralizer_singleton_iff.1 hc).symm)
    rw [miyamotoN1Hom_conj_A1 h m (map_zero _) (map_zero _), miyamotoXGL_inj] at e
    obtain ⟨-, eb, ec, ed⟩ := e
    simp only [zero_mul, add_zero, zero_add, map_one, one_mul] at eb ec ed
    have hdet := m.2
    rw [Matrix.det_fin_two] at hdet
    have hdet' : h.bar ((m : Matrix (Fin 2) (Fin 2) K) 0 0) *
        h.bar ((m : Matrix (Fin 2) (Fin 2) K) 1 1) - h.bar ((m : Matrix (Fin 2) (Fin 2) K) 0 1) *
        h.bar ((m : Matrix (Fin 2) (Fin 2) K) 1 0) = 1 := by
      rw [← map_mul, ← map_mul, ← map_sub, hdet, map_one]
    set m00 := (m : Matrix (Fin 2) (Fin 2) K) 0 0
    set m01 := (m : Matrix (Fin 2) (Fin 2) K) 0 1
    set m10 := (m : Matrix (Fin 2) (Fin 2) K) 1 0
    set m11 := (m : Matrix (Fin 2) (Fin 2) K) 1 1
    have hA11 : -h.bar m10 * m01 + h.bar m00 * m11 = 1 := by
      linear_combination (-(-h.bar m10 * m01 + h.bar m00 * m11)) * ec +
        (-h.bar m10 * m00 + h.bar m00 * m10) * eb +
        (h.bar m00 * h.bar m11 - h.bar m01 * h.bar m10) * hdet + hdet'
    have f00 : h.bar m00 = m00 := by
      linear_combination m00 * hdet' - h.bar m00 * ec - h.bar m01 * ed
    have f01 : h.bar m01 = m01 := by
      linear_combination -h.bar m00 * eb - h.bar m01 * hA11 + m01 * hdet'
    have f10 : h.bar m10 = m10 := by
      linear_combination -h.bar m10 * ec - h.bar m11 * ed + m10 * hdet'
    have f11 : h.bar m11 = m11 := by
      linear_combination -h.bar m10 * eb - h.bar m11 * hA11 + m11 * hdet'
    have hfix : ∀ i j, h.bar ((m : Matrix (Fin 2) (Fin 2) K) i j) =
        (m : Matrix (Fin 2) (Fin 2) K) i j := by
      intro i j
      fin_cases i <;> fin_cases j
      · exact f00
      · exact f01
      · exact f10
      · exact f11
    let mF : Matrix (Fin 2) (Fin 2) h.fixedField := fun i j => ⟨_, hfix i j⟩
    have hmF : mF.map h.fixedField.subtype = (m : Matrix (Fin 2) (Fin 2) K) := by
      ext i j
      rfl
    have hdetF : mF.det = 1 := by
      apply h.fixedField.subtype_injective
      rw [h.fixedField.subtype.map_det, RingHom.mapMatrix_apply, hmF, m.2, map_one]
    exact ⟨⟨mF, hdetF⟩, congrArg (miyamotoN1Hom h) (Subtype.ext hmF)⟩
  · rintro _ ⟨mF, rfl⟩
    refine ⟨⟨_, rfl⟩, mem_centralizer_singleton_iff.2 ?_⟩
    have hfix : ∀ i j, h.bar (((SpecialLinearGroup.map (h.fixedField.subtype : h.fixedField →+* K)
        mF : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j) =
        ((SpecialLinearGroup.map (h.fixedField.subtype : h.fixedField →+* K) mF :
          SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j :=
      fun i j => (mF i j).2
    have hdet := (SpecialLinearGroup.map (h.fixedField.subtype : h.fixedField →+* K) mF).2
    rw [Matrix.det_fin_two] at hdet
    have e : (miyamotoN1Hom h (SpecialLinearGroup.map (h.fixedField.subtype : h.fixedField →+* K)
        mF))⁻¹ * miyamotoXGL h 0 0 1 0 * miyamotoN1Hom h
          (SpecialLinearGroup.map (h.fixedField.subtype : h.fixedField →+* K) mF) =
        miyamotoXGL h 0 0 1 0 := by
      rw [miyamotoN1Hom_conj_A1 h _ (map_zero _) (map_zero _), miyamotoXGL_inj]
      refine ⟨rfl, ?_, ?_, ?_⟩ <;> simp only [zero_mul, add_zero, zero_add, map_one, one_mul, hfix]
      · ring
      · linear_combination hdet
      · ring
    have := (mem_centralizer_singleton_iff_conj).2 e
    exact (mem_centralizer_singleton_iff.1 this).symm

omit [CharP K 2] in
theorem mem_miyamotoN1F_iff {n : GL (Fin 4) K} :
    n ∈ miyamotoN1F h ↔ n ∈ miyamotoN1 h ∧ (n : Matrix (Fin 4) (Fin 4) K).map h.bar = n := by
  have hbb := h.bar_bar
  constructor
  · rintro ⟨mF, rfl⟩
    refine ⟨⟨_, rfl⟩, ?_⟩
    have hfixF : ∀ i j, h.bar (((mF : Matrix (Fin 2) (Fin 2) h.fixedField) i j : h.fixedField) :
        K) = (mF : Matrix (Fin 2) (Fin 2) h.fixedField) i j := fun i j => (mF i j).2
    simp only [MonoidHom.coe_comp, Function.comp_apply, coe_miyamotoN1Hom]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [miyamotoN1Mat, hbb]
    all_goals first | exact hfixF _ _ | exact (hfixF _ _).symm
  · rintro ⟨⟨m, rfl⟩, hu⟩
    have hfix : ∀ i j, h.bar ((m : Matrix (Fin 2) (Fin 2) K) i j) =
        (m : Matrix (Fin 2) (Fin 2) K) i j := by
      intro i j
      have := congrArg (fun M : Matrix (Fin 4) (Fin 4) K =>
        M i.castSucc.castSucc j.castSucc.castSucc) hu
      fin_cases i <;> fin_cases j <;> simpa [miyamotoN1Hom, miyamotoN1Mat] using this
    let mF : Matrix (Fin 2) (Fin 2) h.fixedField := fun i j => ⟨_, hfix i j⟩
    have hmF : mF.map h.fixedField.subtype = (m : Matrix (Fin 2) (Fin 2) K) := by
      ext i j
      rfl
    have hdetF : mF.det = 1 := by
      apply h.fixedField.subtype_injective
      rw [h.fixedField.subtype.map_det, RingHom.mapMatrix_apply, hmF, m.2, map_one]
    exact ⟨⟨mF, hdetF⟩, congrArg (miyamotoN1Hom h) (Subtype.ext hmF)⟩

end Centralizers

section Pull

variable {G : Type} [Group G] (L : Subgroup G) (η : L ≃* gramSU h (miyamotoJ4 K))

theorem exists_invariant_of_miyamotoPull {B : Subgroup G} (hBL : B ≤ L)
    {N : Subgroup (GL (Fin 4) K)} (hN : N ≤ gramSU h (miyamotoJ4 K))
    (hinv : ∀ n ∈ miyamotoPull h L η N, ∀ x ∈ B, n⁻¹ * x * n ∈ B) :
    ∃ M : Subgroup (GL (Fin 4) K), M ≤ gramSU h (miyamotoJ4 K) ∧ miyamotoPull h L η M = B ∧
      ∀ n ∈ N, ∀ x ∈ M, n⁻¹ * x * n ∈ M := by
  obtain ⟨M, hM, rfl⟩ := exists_eq_miyamotoPull h L η hBL
  refine ⟨M, hM, rfl, fun n hn x hx => ?_⟩
  have h1 := hinv _ ((symm_mem_miyamotoPull_iff h L η (g := ⟨n, hN hn⟩)).2 hn) _
    ((symm_mem_miyamotoPull_iff h L η (g := ⟨x, hM hx⟩)).2 hx)
  have e : ((η.symm ⟨n, hN hn⟩ : L) : G)⁻¹ * ((η.symm ⟨x, hM hx⟩ : L) : G) *
      ((η.symm ⟨n, hN hn⟩ : L) : G) = ((η.symm ((⟨n, hN hn⟩ : gramSU h (miyamotoJ4 K))⁻¹ *
        ⟨x, hM hx⟩ * ⟨n, hN hn⟩) : L) : G) := by
    simp only [map_mul, map_inv, coe_mul, coe_inv]
  rw [e, symm_mem_miyamotoPull_iff] at h1
  simpa using h1

theorem miyamotoN1G_irreducible_A1G [CharP K 2] {B : Subgroup G} (hB : B ≤ miyamotoA1G h L η)
    (hinv : ∀ n ∈ miyamotoN1G h L η, ∀ x ∈ B, n⁻¹ * x * n ∈ B) :
    B = ⊥ ∨ B = miyamotoA1G h L η := by
  obtain ⟨M, hM, rfl, hMinv⟩ := exists_invariant_of_miyamotoPull h L η
    (hB.trans (miyamotoPull_le h L η _)) (miyamotoN1_le_gramSU h) hinv
  have hMA : M ≤ miyamotoA1 h := (miyamotoPull_le_miyamotoPull_iff h L η hM).1 hB
  rcases miyamotoN1_irreducible_A1 h hMA hMinv with e | e
  · exact Or.inl (by rw [e, miyamotoPull_bot])
  · exact Or.inr (by rw [e])

end Pull

end CFSG.LocalAnalysis.EvenBN.U4
