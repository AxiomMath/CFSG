module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.Matrix.CharP

public section

namespace CFSG.GH74.GLS.IVK.L2Torus

open Matrix Subgroup

variable {F : Type*} [Field F]

abbrev SL2m (F : Type*) [Field F] := Matrix.SpecialLinearGroup (Fin 2) F

@[expose] def sl2 (a b c d : F) (h : a * d - b * c = 1) : SL2m F :=
  ⟨!![a, b; c, d], by rw [Matrix.det_fin_two_of]; exact h⟩

@[simp] theorem sl2_val (a b c d : F) (h : a * d - b * c = 1) :
    (sl2 a b c d h : Matrix (Fin 2) (Fin 2) F) = !![a, b; c, d] := rfl

theorem sl2_det (x : SL2m F) : x.1 0 0 * x.1 1 1 - x.1 0 1 * x.1 1 0 = 1 := by
  have := x.2
  rw [Matrix.det_fin_two] at this
  exact this

theorem sl2_ext {x y : SL2m F} (h00 : x.1 0 0 = y.1 0 0) (h01 : x.1 0 1 = y.1 0 1)
    (h10 : x.1 1 0 = y.1 1 0) (h11 : x.1 1 1 = y.1 1 1) : x = y := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> assumption

theorem mul_apply' (x y : SL2m F) (i j : Fin 2) :
    (x * y).1 i j = x.1 i 0 * y.1 0 j + x.1 i 1 * y.1 1 j := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem inv_apply_00 (x : SL2m F) : (x⁻¹).1 0 0 = x.1 1 1 := by
  simp [Matrix.SpecialLinearGroup.SL2_inv_expl]

theorem inv_apply_01 (x : SL2m F) : (x⁻¹).1 0 1 = -x.1 0 1 := by
  simp [Matrix.SpecialLinearGroup.SL2_inv_expl]

theorem inv_apply_10 (x : SL2m F) : (x⁻¹).1 1 0 = -x.1 1 0 := by
  simp [Matrix.SpecialLinearGroup.SL2_inv_expl]

theorem inv_apply_11 (x : SL2m F) : (x⁻¹).1 1 1 = x.1 0 0 := by
  simp [Matrix.SpecialLinearGroup.SL2_inv_expl]

@[expose] def diagSub (F : Type*) [Field F] : Subgroup (SL2m F) where
  carrier := {x | x.1 0 1 = 0 ∧ x.1 1 0 = 0}
  mul_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨?_, ?_⟩ <;> simp [mul_apply', hx1, hx2, hy1, hy2]
  one_mem' := by simp
  inv_mem' := by
    rintro x ⟨hx1, hx2⟩
    refine ⟨?_, ?_⟩ <;> simp [inv_apply_01, inv_apply_10, hx1, hx2]

theorem mem_diagSub {x : SL2m F} : x ∈ diagSub F ↔ x.1 0 1 = 0 ∧ x.1 1 0 = 0 := Iff.rfl

@[expose] def w0 (F : Type*) [Field F] : SL2m F := sl2 0 1 (-1) 0 (by ring)

theorem w0_not_mem_diagSub : w0 F ∉ diagSub F := by
  intro h
  have := h.1
  simp [w0] at this

theorem w0_conj_mem_diagSub_iff (n : SL2m F) :
    w0 F * n * (w0 F)⁻¹ ∈ diagSub F ↔ n ∈ diagSub F := by
  simp only [mem_diagSub, mul_apply', inv_apply_00, inv_apply_01, inv_apply_10, inv_apply_11, w0,
    sl2_val]
  simp [and_comm]

theorem w0_mem_normalizer : w0 F ∈ normalizer (diagSub F : Set (SL2m F)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro n
  exact (w0_conj_mem_diagSub_iff n).symm

theorem w0_inv_diag {x : SL2m F} (hx : x ∈ diagSub F) : w0 F * x * (w0 F)⁻¹ = x⁻¹ := by
  obtain ⟨hx1, hx2⟩ := hx
  apply sl2_ext
  all_goals simp [mul_apply', inv_apply_00, inv_apply_01, inv_apply_10, inv_apply_11, w0, hx1, hx2]

theorem w0_sq_mem_center : w0 F ^ 2 ∈ center (SL2m F) := by
  rw [Subgroup.mem_center_iff]
  intro g
  rw [pow_two]
  apply sl2_ext
  all_goals simp [mul_apply', w0]

theorem w0_sq_ne_one (h2 : (2 : F) ≠ 0) : w0 F ^ 2 ≠ 1 := by
  intro h
  have := congrArg (fun x : SL2m F => x.1 0 0) h
  simp [pow_two, mul_apply', w0] at this
  apply h2
  linear_combination -this

theorem mem_diagSub_or_antidiag {h t : SL2m F} (ht : t ∈ diagSub F) (hne : t.1 0 0 ≠ t.1 1 1)
    (hn : h * t * h⁻¹ ∈ diagSub F) : h ∈ diagSub F ∨ (h.1 0 0 = 0 ∧ h.1 1 1 = 0) := by
  obtain ⟨ht01, ht10⟩ := ht
  obtain ⟨hn01, hn10⟩ := hn
  simp only [mul_apply', inv_apply_00, inv_apply_01, inv_apply_10, inv_apply_11, ht01,
    ht10] at hn01 hn10
  have hdet := sl2_det h
  have hsub : t.1 1 1 - t.1 0 0 ≠ 0 := sub_ne_zero.2 hne.symm
  have hxy : h.1 0 0 * h.1 0 1 = 0 := by
    have : h.1 0 0 * h.1 0 1 * (t.1 1 1 - t.1 0 0) = 0 := by linear_combination hn01
    exact (mul_eq_zero.1 this).resolve_right hsub
  have hzw : h.1 1 0 * h.1 1 1 = 0 := by
    have : h.1 1 0 * h.1 1 1 * (t.1 1 1 - t.1 0 0) = 0 := by linear_combination -hn10
    exact (mul_eq_zero.1 this).resolve_right hsub
  by_cases hx : h.1 0 0 = 0
  · right
    refine ⟨hx, ?_⟩
    have hz : h.1 1 0 ≠ 0 := by
      intro hz
      rw [hx, hz] at hdet
      simp at hdet
    exact (mul_eq_zero.1 hzw).resolve_left hz
  · left
    have hy : h.1 0 1 = 0 := (mul_eq_zero.1 hxy).resolve_left hx
    refine ⟨hy, ?_⟩
    have hw : h.1 1 1 ≠ 0 := by
      intro hw
      rw [hy, hw] at hdet
      simp at hdet
    exact (mul_eq_zero.1 hzw).resolve_right hw

theorem exists_mul_w0_of_antidiag {h : SL2m F} (h00 : h.1 0 0 = 0) (h11 : h.1 1 1 = 0) :
    ∃ s ∈ diagSub F, h = s * w0 F := by
  have hdet := sl2_det h
  rw [h00, h11] at hdet
  have hy : h.1 0 1 ≠ 0 := by
    intro hy
    rw [hy] at hdet
    simp at hdet
  have hz : h.1 1 0 = -(h.1 0 1)⁻¹ := by
    field_simp
    linear_combination -hdet
  refine ⟨sl2 (h.1 0 1) 0 0 (h.1 0 1)⁻¹ (by field_simp; simp), ⟨by simp, by simp⟩, ?_⟩
  apply sl2_ext
  all_goals simp [mul_apply', w0, h00, h11, hz]

theorem normalizer_diagSub {t : SL2m F} (ht : t ∈ diagSub F) (hne : t.1 0 0 ≠ t.1 1 1) :
    normalizer (diagSub F : Set (SL2m F)) = diagSub F ⊔ zpowers (w0 F) := by
  apply le_antisymm
  · intro h hh
    rw [Subgroup.mem_normalizer_iff] at hh
    rcases mem_diagSub_or_antidiag ht hne ((hh t).1 ht) with hd | ha
    · exact Subgroup.mem_sup_left hd
    · obtain ⟨s, hs, rfl⟩ := exists_mul_w0_of_antidiag ha.1 ha.2
      exact mul_mem (Subgroup.mem_sup_left hs) (Subgroup.mem_sup_right (mem_zpowers _))
  · exact sup_le (Subgroup.le_normalizer) (zpowers_le.2 w0_mem_normalizer)

theorem card_diagSub_le [Finite F] : Nat.card (diagSub F) ≤ Nat.card F - 1 := by
  rw [← Nat.card_units]
  have hne : ∀ x : diagSub F, (x : SL2m F).1 0 0 ≠ 0 := by
    intro x h
    have hdet := sl2_det (x : SL2m F)
    rw [h, x.2.1] at hdet
    simp at hdet
  refine Nat.card_le_card_of_injective
    (fun x : diagSub F => Units.mk0 ((x : SL2m F).1 0 0) (hne x)) ?_
  intro x y hxy
  have h00 : (x : SL2m F).1 0 0 = (y : SL2m F).1 0 0 := by simpa using congrArg Units.val hxy
  have hx := sl2_det (x : SL2m F)
  have hy := sl2_det (y : SL2m F)
  rw [x.2.1] at hx
  rw [y.2.1] at hy
  apply Subtype.ext
  apply sl2_ext h00 (by rw [x.2.1, y.2.1]) (by rw [x.2.2, y.2.2])
  apply mul_left_cancel₀ (hne x)
  rw [h00] at hx ⊢
  linear_combination hx - hy

open Polynomial in
theorem X_pow_card_sub_X_eq_list (F : Type*) [Field F] [Fintype F] :
    (X ^ Fintype.card F - X : F[X]) = (Finset.univ.toList.map fun a : F => (X - C a)).prod := by
  classical
  have hdeg : (X ^ Fintype.card F - X : F[X]).natDegree = Fintype.card F :=
    FiniteField.X_pow_card_sub_X_natDegree_eq F Fintype.one_lt_card
  have hmonic : (X ^ Fintype.card F - X : F[X]).Monic := by
    apply Polynomial.monic_X_pow_sub
    rw [degree_X]
    exact_mod_cast Fintype.one_lt_card
  have hroots := FiniteField.roots_X_pow_card_sub_X F
  have hcard : Multiset.card (X ^ Fintype.card F - X : F[X]).roots =
      (X ^ Fintype.card F - X : F[X]).natDegree := by
    rw [hroots, hdeg]; simp
  have := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic hcard
  rw [hroots, ← Finset.coe_toList (Finset.univ : Finset F), Multiset.map_coe,
    Multiset.prod_coe] at this
  exact this.symm

open Polynomial in
theorem exists_det_sub_eq_zero (F : Type*) [Field F] [Fintype F] (g : Matrix (Fin 2) (Fin 2) F)
    (hg : g ^ Fintype.card F = g) : ∃ a : F, (g - Matrix.scalar (Fin 2) a).det = 0 := by
  classical
  have hprod : (Finset.univ.toList.map (fun a : F => g - Matrix.scalar (Fin 2) a)).prod = 0 := by
    have h := congrArg (Polynomial.aeval g) (X_pow_card_sub_X_eq_list F)
    rw [map_list_prod, List.map_map] at h
    have hfun : ((Polynomial.aeval g) ∘ fun a : F => (X - C a : F[X])) =
        fun a : F => g - Matrix.scalar (Fin 2) a := by
      funext a
      simp [Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply]
    rw [hfun] at h
    rw [← h]
    simp [hg]
  have hdet : ((Finset.univ.toList.map
      (fun a : F => g - Matrix.scalar (Fin 2) a)).prod).det = 0 := by
    rw [hprod, Matrix.det_zero]
  have h2 := map_list_prod (Matrix.detMonoidHom : Matrix (Fin 2) (Fin 2) F →* F)
    (Finset.univ.toList.map (fun a : F => g - Matrix.scalar (Fin 2) a))
  rw [List.map_map] at h2
  have h3 : (List.map (fun a : F => (g - Matrix.scalar (Fin 2) a).det)
      Finset.univ.toList).prod = 0 := by
    have : (⇑(Matrix.detMonoidHom : Matrix (Fin 2) (Fin 2) F →* F)) ∘
        (fun a : F => g - Matrix.scalar (Fin 2) a) =
        fun a : F => (g - Matrix.scalar (Fin 2) a).det := rfl
    rw [← this, ← h2]
    exact hdet
  have := List.prod_eq_zero_iff.mp h3
  simp only [List.mem_map] at this
  obtain ⟨a, -, ha⟩ := this
  exact ⟨a, ha⟩

theorem trace_eq_of_det_sub_eq_zero {g : SL2m F} {a : F}
    (hdet : (g.1 - Matrix.scalar (Fin 2) a).det = 0) :
    a * (g.1 0 0 + g.1 1 1) = a * a + 1 := by
  have hd := sl2_det g
  rw [Matrix.det_fin_two] at hdet
  simp [Matrix.scalar_apply] at hdet
  linear_combination -hdet + hd

theorem pow_two_mul_eq_one_of_eigenvalue {p : ℕ} [Fact p.Prime] [CharP F p] (hp2 : p ≠ 2)
    (g : SL2m F) (a : F) (ha : a * a = 1) (hdet : (g.1 - Matrix.scalar (Fin 2) a).det = 0) :
    g ^ (2 * p) = 1 := by
  have hd := sl2_det g
  have h1 : a * (g.1 0 0 + g.1 1 1) = 2 := by
    have := trace_eq_of_det_sub_eq_zero hdet
    linear_combination this + ha
  have ht : g.1 0 0 + g.1 1 1 = 2 * a := by
    linear_combination a * h1 - (g.1 0 0 + g.1 1 1) * ha
  have hdet' := hdet
  rw [Matrix.det_fin_two] at hdet'
  simp [Matrix.scalar_apply] at hdet'
  set N : Matrix (Fin 2) (Fin 2) F := g.1 - Matrix.scalar (Fin 2) a with hN
  have hN2 : N * N = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hN, Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply]
    · linear_combination (g.1 0 0 - a) * ht - hdet'
    · linear_combination g.1 0 1 * ht
    · linear_combination g.1 1 0 * ht
    · linear_combination (g.1 1 1 - a) * ht - hdet'
  have hcomm : Commute (Matrix.scalar (Fin 2) a) N := Matrix.scalar_commute _ (fun _ => by
    exact Commute.all _ _) _
  have hg : g.1 = Matrix.scalar (Fin 2) a + N := by simp [hN]
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hap : a ^ p = a := by
    obtain ⟨k, hk⟩ := hodd
    rw [hk, pow_succ, pow_mul, pow_two, ha, one_pow, one_mul]
  have hNp : N ^ p = 0 :=
    pow_eq_zero_of_le (Fact.out : p.Prime).two_le (by rw [pow_two]; exact hN2)
  have hgp : g.1 ^ p = Matrix.scalar (Fin 2) a := by
    rw [hg, add_pow_char_of_commute p hcomm, ← map_pow, hap, hNp, add_zero]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, mul_comm, pow_mul, hgp, ← map_pow, pow_two, ha]
  simp

theorem det_sub_ne_zero_of_sq_eq_one [Finite F] {p n : ℕ} [Fact p.Prime] [CharP F p] (hn : 1 ≤ n)
    (hcard : Nat.card F = p ^ n) (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (g : SL2m F) (hg : orderOf g = Nat.card F - 1) (a : F) (ha : a * a = 1) :
    (g.1 - Matrix.scalar (Fin 2) a).det ≠ 0 := by
  intro hdet
  have hp2 : p ≠ 2 := by
    rintro rfl
    rw [hcard] at hodd
    exact (Nat.not_even_iff_odd.2 hodd) (Nat.even_pow.2 ⟨even_two, by omega⟩)
  have h1 := pow_two_mul_eq_one_of_eigenvalue hp2 g a ha hdet
  have hdvd : Nat.card F - 1 ∣ 2 * p := hg ▸ orderOf_dvd_of_pow_eq_one h1
  have hcop : Nat.Coprime (Nat.card F - 1) p := by
    have hpq : p ∣ Nat.card F := hcard ▸ dvd_pow_self p (by omega)
    have h1 : Nat.Coprime (Nat.card F - 1) (Nat.card F) := by
      obtain ⟨k, hk⟩ : ∃ k, Nat.card F = k + 1 := ⟨Nat.card F - 1, by omega⟩
      rw [hk]
      simp
    exact Nat.Coprime.coprime_dvd_right hpq h1
  have h2 : Nat.card F - 1 ∣ 2 := hcop.dvd_of_dvd_mul_right hdvd
  have := Nat.le_of_dvd (by norm_num) h2
  omega

@[expose] def dg (a b : F) (h : a * b = 1) : SL2m F := sl2 a 0 0 b (by simpa using h)

theorem dg_mem_diagSub (a b : F) (h : a * b = 1) : dg a b h ∈ diagSub F :=
  ⟨by simp [dg], by simp [dg]⟩

theorem dg_apply_00 (a b : F) (h : a * b = 1) : (dg a b h).1 0 0 = a := by simp [dg]

theorem dg_apply_11 (a b : F) (h : a * b = 1) : (dg a b h).1 1 1 = b := by simp [dg]

theorem exists_conj_dg_of_ne_zero_10 {g : SL2m F} {a b : F} (hab : a * b = 1) (hne : a ≠ b)
    (htr : g.1 0 0 + g.1 1 1 = a + b) (hz : g.1 1 0 ≠ 0) :
    ∃ P : SL2m F, P⁻¹ * g * P = dg a b hab := by
  have hδ : g.1 1 0 * (a - b) ≠ 0 := mul_ne_zero hz (sub_ne_zero.2 hne)
  obtain ⟨μ, hμ⟩ : ∃ μ : F, g.1 1 0 * (a - b) * μ = 1 := ⟨(g.1 1 0 * (a - b))⁻¹, mul_inv_cancel₀ hδ⟩
  have hdet := sl2_det g
  refine ⟨sl2 (a - g.1 1 1) ((b - g.1 1 1) * μ) (g.1 1 0) (g.1 1 0 * μ) ?_, ?_⟩
  · linear_combination hμ
  · rw [mul_assoc, inv_mul_eq_iff_eq_mul]
    apply sl2_ext
    · simp only [mul_apply', sl2_val, dg]
      simp
      linear_combination -hdet + a * htr + hab
    · simp only [mul_apply', sl2_val, dg]
      simp
      linear_combination μ * (-hdet + b * htr + hab)
    · simp only [mul_apply', sl2_val, dg]
      simp
      ring
    · simp only [mul_apply', sl2_val, dg]
      simp
      ring

theorem exists_conj_mem_diagSub_of_ne_zero_01 {g : SL2m F} {a b : F} (hab : a * b = 1) (hne : a ≠ b)
    (htr : g.1 0 0 + g.1 1 1 = a + b) (hz : g.1 0 1 ≠ 0) :
    ∃ P : SL2m F, P⁻¹ * g * P = dg a b hab := by
  obtain ⟨P, hP⟩ := exists_conj_dg_of_ne_zero_10 (g := w0 F * g * (w0 F)⁻¹) hab hne
    (by simpa [mul_apply', inv_apply_00, inv_apply_01, inv_apply_10, inv_apply_11, w0, add_comm]
      using htr)
    (by simpa [mul_apply', inv_apply_00, inv_apply_01, inv_apply_10, inv_apply_11, w0] using hz)
  refine ⟨(w0 F)⁻¹ * P, ?_⟩
  rw [← hP]
  group

theorem exists_conj_mem_diagSub_of_eigenvalue {g : SL2m F} {a b : F} (hab : a * b = 1)
    (hne : a ≠ b) (htr : g.1 0 0 + g.1 1 1 = a + b) :
    ∃ P : SL2m F, P⁻¹ * g * P ∈ diagSub F := by
  by_cases h10 : g.1 1 0 = 0
  · by_cases h01 : g.1 0 1 = 0
    · exact ⟨1, by simpa using (show g ∈ diagSub F from ⟨h01, h10⟩)⟩
    · obtain ⟨P, hP⟩ := exists_conj_mem_diagSub_of_ne_zero_01 hab hne htr h01
      exact ⟨P, hP ▸ dg_mem_diagSub a b hab⟩
  · obtain ⟨P, hP⟩ := exists_conj_dg_of_ne_zero_10 hab hne htr h10
    exact ⟨P, hP ▸ dg_mem_diagSub a b hab⟩

theorem exists_conj_mem_diagSub_of_orderOf [Finite F] {p n : ℕ} [Fact p.Prime] [CharP F p]
    (hn : 1 ≤ n) (hcard : Nat.card F = p ^ n) (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (g : SL2m F) (hg : orderOf g = Nat.card F - 1) :
    ∃ P : SL2m F, P⁻¹ * g * P ∈ diagSub F := by
  have := Fintype.ofFinite F
  have hpow : g ^ Fintype.card F = g := by
    have h1 : g ^ (Nat.card F - 1) = 1 := hg ▸ pow_orderOf_eq_one g
    rw [← Nat.card_eq_fintype_card]
    calc g ^ Nat.card F = g ^ (Nat.card F - 1 + 1) := by congr 1; omega
      _ = g := by rw [pow_succ, h1, one_mul]
  have hmat : g.1 ^ Fintype.card F = g.1 := by
    have := congrArg Subtype.val hpow
    simpa [Matrix.SpecialLinearGroup.coe_pow] using this
  obtain ⟨a, ha⟩ := exists_det_sub_eq_zero F g.1 hmat
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at ha
  have hsq : a * a ≠ 1 := fun h => det_sub_ne_zero_of_sq_eq_one hn hcard hodd h3 g hg a h ha
  have hab : a * a⁻¹ = 1 := mul_inv_cancel₀ ha0
  have hne : a ≠ a⁻¹ := by
    intro h
    apply hsq
    nth_rewrite 2 [h]
    exact hab
  have htr : g.1 0 0 + g.1 1 1 = a + a⁻¹ := by
    have := trace_eq_of_det_sub_eq_zero ha
    field_simp
    linear_combination this
  exact exists_conj_mem_diagSub_of_eigenvalue hab hne htr

theorem exists_sq_ne_one [Finite F] (h3 : 3 < Nat.card F) : ∃ a : F, a ≠ 0 ∧ a * a ≠ 1 := by
  by_contra hcon
  push Not at hcon
  classical
  have := Fintype.ofFinite F
  have hle : Nat.card F ≤ 3 := by
    rw [Nat.card_eq_fintype_card]
    calc Fintype.card F = (Finset.univ : Finset F).card := Finset.card_univ.symm
      _ ≤ ({0, 1, -1} : Finset F).card := Finset.card_le_card (fun x _ => by
          by_cases hx : x = 0
          · simp [hx]
          · have h2 := hcon x hx
            have h4 : (x - 1) * (x + 1) = 0 := by linear_combination h2
            rcases mul_eq_zero.1 h4 with h5 | h5
            · simp [sub_eq_zero.1 h5]
            · simp [eq_neg_of_add_eq_zero_left h5])
      _ ≤ 3 := Finset.card_le_three
  omega

theorem exists_map_conj_eq_diagSub [Finite F] (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (D : Subgroup (SL2m F)) (hD : IsCyclic D) (hc : Nat.card D = Nat.card F - 1) :
    ∃ P : SL2m F, D.map (MulAut.conj P⁻¹).toMonoidHom = diagSub F := by
  have := Fintype.ofFinite F
  obtain ⟨p, hpF, n, hp, hq⟩ := FiniteField.card' F
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := hD.exists_generator
  have hord : orderOf (g : SL2m F) = Nat.card F - 1 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hc]
  obtain ⟨P, hP⟩ := exists_conj_mem_diagSub_of_orderOf (n := (n : ℕ)) n.pos
    (by rw [Nat.card_eq_fintype_card]; exact hq) hodd h3 (g : SL2m F) hord
  refine ⟨P, ?_⟩
  have hle : D.map (MulAut.conj P⁻¹).toMonoidHom ≤ diagSub F := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨x, hx⟩)
    have hxk : x = (g : SL2m F) ^ k := by
      rw [← Subgroup.coe_zpow, hk]
    rw [hxk]
    have : (MulAut.conj P⁻¹).toMonoidHom ((g : SL2m F) ^ k) =
        (P⁻¹ * (g : SL2m F) * P) ^ k := by
      rw [map_zpow]
      simp
    rw [this]
    exact zpow_mem hP k
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [Subgroup.card_map_of_injective (MulAut.conj P⁻¹).injective, hc]
  exact card_diagSub_le

theorem exists_inverting_of_equiv {G G' : Type*} [Group G] [Group G'] (c : G ≃* G')
    (D : Subgroup G) (T : Subgroup G') (hD : D.map c.toMonoidHom = T) (w : G')
    (hN : normalizer (T : Set G') = T ⊔ zpowers w) (hw : w ∉ T) (hw2 : w ^ 2 ∈ center G')
    (hw2' : w ^ 2 ≠ 1) (hinv : ∀ x ∈ T, w * x * w⁻¹ = x⁻¹) :
    ∃ w' : G, normalizer (D : Set G) = D ⊔ zpowers w' ∧ w' ∉ D ∧ w' ^ 2 ∈ center G ∧
      w' ^ 2 ≠ 1 ∧ ∀ x ∈ D, w' * x * w'⁻¹ = x⁻¹ := by
  subst hD
  refine ⟨c.symm w, ?_, ?_, ?_, ?_, ?_⟩
  · apply Subgroup.map_injective (f := c.toMonoidHom) c.injective
    rw [Subgroup.map_equiv_normalizer_eq, hN, Subgroup.map_sup, MonoidHom.map_zpowers]
    simp
  · intro h
    exact hw (by simpa using Subgroup.mem_map_of_mem c.toMonoidHom h)
  · rw [Subgroup.mem_center_iff] at hw2 ⊢
    intro g
    apply c.injective
    simp only [map_mul, map_pow, MulEquiv.apply_symm_apply]
    exact hw2 (c g)
  · intro h
    apply hw2'
    have := congrArg c h
    simpa using this
  · intro x hx
    apply c.injective
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hinv _ (Subgroup.mem_map_of_mem c.toMonoidHom hx)

theorem exists_inverting_normalizer {G : Type*} [Group G] [Finite F] (e : G ≃* SL2m F)
    (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F) (D : Subgroup G) (hD : IsCyclic D)
    (hc : Nat.card D = Nat.card F - 1) :
    ∃ w : G, normalizer (D : Set G) = D ⊔ zpowers w ∧ w ∉ D ∧ w ^ 2 ∈ center G ∧
      w ^ 2 ≠ 1 ∧ ∀ x ∈ D, w * x * w⁻¹ = x⁻¹ := by
  have hcyc : IsCyclic (D.map e.toMonoidHom) :=
    (Subgroup.equivMapOfInjective D e.toMonoidHom e.injective).isCyclic.1 hD
  have hcard : Nat.card (D.map e.toMonoidHom) = Nat.card F - 1 := by
    rw [Subgroup.card_map_of_injective e.injective, hc]
  obtain ⟨P, hP⟩ := exists_map_conj_eq_diagSub hodd h3 _ hcyc hcard
  have h2 : (2 : F) ≠ 0 := by
    have := Fintype.ofFinite F
    apply Ring.two_ne_zero
    intro hc2
    have := FiniteField.even_card_of_char_two hc2
    rw [Nat.card_eq_fintype_card, Nat.odd_iff] at hodd
    omega
  obtain ⟨a, ha0, ha⟩ := exists_sq_ne_one h3
  refine exists_inverting_of_equiv (e.trans (MulAut.conj P⁻¹)) D (diagSub F) ?_ (w0 F) ?_
    w0_not_mem_diagSub w0_sq_mem_center (w0_sq_ne_one h2) (fun x hx => w0_inv_diag hx)
  · rw [← hP, Subgroup.map_map]
    rfl
  · refine normalizer_diagSub (t := dg a a⁻¹ (mul_inv_cancel₀ ha0)) (dg_mem_diagSub _ _ _) ?_
    rw [dg_apply_00, dg_apply_11]
    intro h
    apply ha
    nth_rewrite 2 [h]
    exact mul_inv_cancel₀ ha0

end CFSG.GH74.GLS.IVK.L2Torus
