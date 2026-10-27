module

public import CFSG.LocalAnalysis.EvenBN.U4.Model.Weights

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag
open scoped Pointwise

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

section Tori

theorem pow_sub_one_eq_one_of_bar {s : K} (hs : h.bar s = s) (hs0 : s ≠ 0) :
    s ^ (2 ^ f - 1) = 1 := by
  have hq : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  rw [h.bar_apply] at hs
  have : s ^ (2 ^ f - 1) * s = 1 * s := by rw [← pow_succ, Nat.sub_add_cancel hq, hs, one_mul]
  exact mul_right_cancel₀ hs0 this

theorem pow_sub_one_mul_bar {a : K} (ha : a ≠ 0) :
    a ^ (2 ^ f - 1) * h.bar (a ^ (2 ^ f - 1)) = 1 := by
  rw [map_pow, ← mul_pow]
  refine pow_sub_one_eq_one_of_bar h ?_ (mul_ne_zero ha ((map_ne_zero h.bar).2 ha))
  rw [map_mul, h.bar_bar, mul_comm]

theorem bar_pow_sub_one {a : K} (ha : a ≠ 0) :
    h.bar (a ^ (2 ^ f - 1)) = (a ^ (2 ^ f - 1))⁻¹ :=
  eq_inv_of_mul_eq_one_right (pow_sub_one_mul_bar h ha)

theorem miyamotoI2Hom_eq (a : Kˣ) :
    miyamotoI2Hom h a = miyamotoIHom h (a ^ 2, a ^ (2 ^ f - 1)) := by
  have e : a ^ (2 ^ f - 1) = (Units.map h.bar.toMonoidHom (a ^ (2 ^ f - 1)))⁻¹ := by
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.coe_map,
      RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]
    rw [bar_pow_sub_one h a.ne_zero, inv_inv]
  change miyamotoDiag _ _ _ _ = miyamotoDiag _ _ _ _
  rw [← e, map_pow]

theorem mem_miyamotoI2 {g : GL (Fin 4) K} :
    g ∈ miyamotoI2 h ↔ ∃ a : Kˣ, g = miyamotoIHom h (a ^ 2, a ^ (2 ^ f - 1)) := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, miyamotoI2Hom_eq h a⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, miyamotoI2Hom_eq h a⟩

theorem mem_miyamotoI2r1 {g : GL (Fin 4) K} :
    g ∈ miyamotoI2r1 h ↔ ∃ a : Kˣ, g = miyamotoIHom h (a ^ (2 ^ f - 1), a ^ 2) := by
  have key : ∀ a : Kˣ, (MulAut.conj (miyamotoR1 K)⁻¹).toMonoidHom
      (miyamotoIHom h (a ^ 2, a ^ (2 ^ f - 1))) = miyamotoIHom h (a ^ (2 ^ f - 1), a ^ 2) := by
    intro a
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact miyamotoR1_conj_miyamotoIHom h _
  constructor
  · rintro ⟨g', hg', rfl⟩
    obtain ⟨a, rfl⟩ := (mem_miyamotoI2 h).1 hg'
    exact ⟨a, key a⟩
  · rintro ⟨a, rfl⟩
    exact ⟨_, (mem_miyamotoI2 h).2 ⟨a, rfl⟩, key a⟩

theorem miyamotoI1_conj {t : Kˣ} (ht : h.bar t = t) (a b c d : K) :
    (miyamotoIHom h (t, t))⁻¹ * miyamotoXGL h a b c d * miyamotoIHom h (t, t) =
      miyamotoXGL h a ((t : K) ^ 2 * b) ((t : K) ^ 2 * c) ((t : K) ^ 2 * d) := by
  rw [miyamotoIHom_conj, miyamotoXGL_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [ht, sq, t.ne_zero]

theorem miyamotoI2Hom_conj (a : Kˣ) (a' b' c' d' : K) :
    (miyamotoI2Hom h a)⁻¹ * miyamotoXGL h a' b' c' d' * miyamotoI2Hom h a =
      miyamotoXGL h ((a : K) ^ 2 * ((a : K) ^ (2 ^ f - 1))⁻¹ * a') b'
        ((a : K) ^ 2 * ((a : K) ^ (2 ^ f - 1))⁻¹ * c')
        ((a : K) ^ 2 * h.bar ((a : K) ^ 2) * d') := by
  rw [miyamotoI2Hom_eq, miyamotoIHom_conj, miyamotoXGL_inj]
  simp only [Units.val_pow_eq_pow_val]
  rw [pow_sub_one_mul_bar h a.ne_zero, bar_pow_sub_one h a.ne_zero, one_mul]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> trivial

theorem miyamotoI2r1Hom_conj (a : Kˣ) (a' b' c' d' : K) :
    (miyamotoIHom h (a ^ (2 ^ f - 1), a ^ 2))⁻¹ * miyamotoXGL h a' b' c' d' *
        miyamotoIHom h (a ^ (2 ^ f - 1), a ^ 2) =
      miyamotoXGL h ((a : K) ^ (2 ^ f - 1) * ((a : K) ^ 2)⁻¹ * a')
        ((a : K) ^ 2 * h.bar ((a : K) ^ 2) * b')
        ((a : K) ^ (2 ^ f - 1) * h.bar ((a : K) ^ 2) * c') d' := by
  rw [miyamotoIHom_conj, miyamotoXGL_inj]
  simp only [Units.val_pow_eq_pow_val]
  rw [pow_sub_one_mul_bar h a.ne_zero, one_mul]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> trivial

theorem miyamotoIParam_eq_one_iff (p : Kˣ × Kˣ) :
    miyamotoIParam h p = 1 ↔ h.bar ((p.1 : K) * p.2) = (p.1 : K) * p.2 := by
  have h1 : h.bar (p.1 : K) ≠ 0 := by simp
  have h2 : h.bar (p.2 : K) ≠ 0 := by simp
  rw [Units.ext_iff]
  simp only [miyamotoIParam, MonoidHom.mul_apply, MonoidHom.coe_fst, MonoidHom.coe_snd,
    MonoidHom.inv_apply, MonoidHom.coe_comp, Function.comp_apply, Units.val_mul,
    Units.val_inv_eq_inv_val, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
    Units.val_one, map_mul]
  constructor
  · intro e
    field_simp at e
    exact e.symm
  · intro e
    field_simp
    exact e.symm

theorem miyamotoI1_le_I : miyamotoI1 h ≤ miyamotoI h := by
  intro g hg
  obtain ⟨t, ht, rfl⟩ := (mem_miyamotoI1 h).1 hg
  refine (miyamotoIHom_mem_miyamotoI_iff h _).2 ((miyamotoIParam_eq_one_iff h _).2 ?_)
  simp only [map_mul, ht]

theorem miyamotoI2_le_I : miyamotoI2 h ≤ miyamotoI h := by
  intro g hg
  obtain ⟨a, rfl⟩ := (mem_miyamotoI2 h).1 hg
  refine (miyamotoIHom_mem_miyamotoI_iff h _).2 ((miyamotoIParam_eq_one_iff h _).2 ?_)
  simp only [Units.val_pow_eq_pow_val]
  have ha := a.ne_zero
  rw [map_mul, bar_pow_sub_one h ha, map_pow]
  have hq : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have hbar : h.bar (a : K) = (a : K) ^ (2 ^ f - 1) * a := by
    rw [h.bar_apply, ← pow_succ, Nat.sub_add_cancel hq]
  have hp : (a : K) ^ (2 ^ f - 1) ≠ 0 := pow_ne_zero _ ha
  rw [hbar]
  field_simp

theorem miyamotoI2r1_le_I : miyamotoI2r1 h ≤ miyamotoI h := by
  intro g hg
  obtain ⟨a, rfl⟩ := (mem_miyamotoI2r1 h).1 hg
  have := miyamotoI2_le_I h ((mem_miyamotoI2 h).2 ⟨a, rfl⟩)
  rw [miyamotoIHom_mem_miyamotoI_iff, miyamotoIParam_eq_one_iff] at this ⊢
  rwa [mul_comm]

theorem miyamotoI1r2_le_I : miyamotoI1r2 h ≤ miyamotoI h := by
  intro g hg
  obtain ⟨t, ht, rfl⟩ := (mem_miyamotoI1r2 h).1 hg
  refine (miyamotoIHom_mem_miyamotoI_iff h _).2 ((miyamotoIParam_eq_one_iff h _).2 ?_)
  simp

theorem miyamotoIHom_conj_mem_unipotent {za zb : Bool} (p : Kˣ × Kˣ) {x : GL (Fin 4) K}
    (hx : x ∈ miyamotoUnipotent h za zb) :
    (miyamotoIHom h p)⁻¹ * x * miyamotoIHom h p ∈ miyamotoUnipotent h za zb := by
  obtain ⟨a, b, c, d, ha, hb, hb', hd, rfl⟩ := (mem_miyamotoUnipotent h).1 hx
  rw [miyamotoIHom_conj, miyamotoXGL_mem_miyamotoUnipotent]
  have h1 : (p.1 : K) ≠ 0 := p.1.ne_zero
  have h2 : (p.2 : K) ≠ 0 := p.2.ne_zero
  have hb1 : h.bar (p.1 : K) ≠ 0 := by simp
  have hb2 : h.bar (p.2 : K) ≠ 0 := by simp
  refine ⟨fun hz => by rw [ha hz, mul_zero], fun hz => by rw [hb hz, mul_zero], ?_, ?_⟩
  · simp only [map_mul, h.bar_bar, hb']
    ring
  · simp only [map_mul, map_inv₀, h.bar_bar]
    field_simp
    linear_combination (p.1 : K) * h.bar (p.1 : K) * hd

theorem miyamotoI_le_normalizer_unipotent (za zb : Bool) :
    miyamotoI h ≤ normalizer (miyamotoUnipotent h za zb : Set (GL (Fin 4) K)) := by
  rintro _ ⟨p, -, rfl⟩
  refine mem_normalizer_iff''.2 fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · exact miyamotoIHom_conj_mem_unipotent h p hx
  · have := miyamotoIHom_conj_mem_unipotent h p⁻¹ hx
    rwa [map_inv, inv_inv, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul, mul_assoc,
      mul_inv_cancel, mul_one] at this

end Tori

section Weyl

theorem mem_miyamotoN1 {g : GL (Fin 4) K} :
    g ∈ miyamotoN1 h ↔ ∃ m : Matrix (Fin 2) (Fin 2) K, m.det = 1 ∧
      (g : Matrix (Fin 4) (Fin 4) K) = miyamotoN1Mat h m := by
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨m, m.2, rfl⟩
  · rintro ⟨m, hm, hg⟩
    exact ⟨⟨m, hm⟩, Units.ext hg.symm⟩

theorem mem_miyamotoN2 {g : GL (Fin 4) K} :
    g ∈ miyamotoN2 h ↔ ∃ m : Matrix (Fin 2) (Fin 2) K, m.det = 1 ∧
      (∀ i j, h.bar (m i j) = m i j) ∧ (g : Matrix (Fin 4) (Fin 4) K) = miyamotoN2Mat K m := by
  constructor
  · rintro ⟨m, rfl⟩
    refine ⟨((m : Matrix (Fin 2) (Fin 2) h.fixedField).map h.fixedField.subtype), ?_,
      fun i j => (m i j).2, rfl⟩
    have := h.fixedField.subtype.map_det (m : Matrix (Fin 2) (Fin 2) h.fixedField)
    rw [m.2, map_one] at this
    exact this.symm
  · rintro ⟨m, hm, hbar, hg⟩
    let m' : Matrix (Fin 2) (Fin 2) h.fixedField := fun i j => ⟨m i j, hbar i j⟩
    have hm' : m'.map h.fixedField.subtype = m := by
      ext i j
      rfl
    have hdet : m'.det = 1 := by
      apply h.fixedField.subtype_injective
      rw [h.fixedField.subtype.map_det, RingHom.mapMatrix_apply, hm', hm, map_one]
    refine ⟨⟨m', hdet⟩, Units.ext ?_⟩
    rw [hg, ← hm']
    rfl

theorem miyamotoR1_mem_gramSU : miyamotoR1 K ∈ gramSU h (miyamotoJ4 K) := by
  refine mem_gramSU.2 ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [miyamotoR1, miyamotoJ4, Matrix.mul_apply, Fin.sum_univ_four]
  · simp [miyamotoR1, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]

theorem miyamotoR2_mem_gramSU [CharP K 2] : miyamotoR2 K ∈ gramSU h (miyamotoJ4 K) := by
  refine mem_gramSU.2 ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [miyamotoR2, miyamotoJ4, Matrix.mul_apply, Fin.sum_univ_four]
  · simp [miyamotoR2, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
    exact CharTwo.neg_eq 1

theorem miyamotoR1_mem_N1 [CharP K 2] : miyamotoR1 K ∈ miyamotoN1 h := by
  refine (mem_miyamotoN1 h).2 ⟨!![0, 1; 1, 0], ?_, ?_⟩
  · simp [Matrix.det_fin_two]
    exact CharTwo.neg_eq 1
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [miyamotoR1, miyamotoN1Mat]

theorem miyamotoR2_mem_N2 [CharP K 2] : miyamotoR2 K ∈ miyamotoN2 h := by
  refine (mem_miyamotoN2 h).2 ⟨!![0, 1; 1, 0], ?_, fun i j => ?_, ?_⟩
  · simp [Matrix.det_fin_two]
    exact CharTwo.neg_eq 1
  · fin_cases i <;> fin_cases j <;> simp
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [miyamotoR2, miyamotoN2Mat]

theorem miyamotoR1_mul_R2_sq :
    (((miyamotoR1 K * miyamotoR2 K) ^ 2 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      miyamotoJ4 K := by
  have e : ((miyamotoR1 K * miyamotoR2 K : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      !![0, 0, 1, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 1, 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [miyamotoR1, miyamotoR2, Matrix.mul_apply, Fin.sum_univ_four]
  rw [sq, Units.val_mul, e]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [miyamotoJ4, Matrix.mul_apply, Fin.sum_univ_four]

theorem miyamotoR1_mul_R2_pow_four : (miyamotoR1 K * miyamotoR2 K) ^ 4 = 1 := by
  have e : (miyamotoR1 K * miyamotoR2 K) ^ 4 = ((miyamotoR1 K * miyamotoR2 K) ^ 2) ^ 2 := by
    rw [← pow_mul]
  apply Units.ext
  rw [e, sq ((miyamotoR1 K * miyamotoR2 K) ^ 2), Units.val_mul, miyamotoR1_mul_R2_sq,
    miyamotoJ4_mul_self, Units.val_one]

theorem miyamotoR1_conj_mem_I {g : GL (Fin 4) K} (hg : g ∈ miyamotoI h) :
    (miyamotoR1 K)⁻¹ * g * miyamotoR1 K ∈ miyamotoI h := by
  obtain ⟨p, hp, rfl⟩ := hg
  rw [miyamotoR1_conj_miyamotoIHom]
  refine (miyamotoIHom_mem_miyamotoI_iff h _).2 ((miyamotoIParam_eq_one_iff h _).2 ?_)
  have := (miyamotoIParam_eq_one_iff h p).1 hp
  simpa [mul_comm] using this

theorem miyamotoR2_conj_mem_I {g : GL (Fin 4) K} (hg : g ∈ miyamotoI h) :
    (miyamotoR2 K)⁻¹ * g * miyamotoR2 K ∈ miyamotoI h := by
  obtain ⟨p, hp, rfl⟩ := hg
  rw [miyamotoR2_conj_miyamotoIHom]
  refine (miyamotoIHom_mem_miyamotoI_iff h _).2 ((miyamotoIParam_eq_one_iff h _).2 ?_)
  have e := (miyamotoIParam_eq_one_iff h p).1 hp
  have h1 : (p.1 : K) ≠ 0 := p.1.ne_zero
  have h2 : (p.2 : K) ≠ 0 := p.2.ne_zero
  have hb2 : h.bar (p.2 : K) ≠ 0 := by simp
  simp only [Units.val_inv_eq_inv_val, Units.coe_map, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_ofClass, map_mul, map_inv₀, h.bar_bar] at e ⊢
  field_simp
  linear_combination e

end Weyl

section Factorizations

theorem miyamotoIHom_sq_one_mem_I2 {t : Kˣ} (ht : h.bar t = t) :
    miyamotoIHom h (t ^ 2, 1) ∈ miyamotoI2 h := by
  have e : t ^ (2 ^ f - 1) = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact pow_sub_one_eq_one_of_bar h ht t.ne_zero)
  exact (mem_miyamotoI2 h).2 ⟨t, by rw [e]⟩

theorem miyamotoIHom_one_sq_mem_I2r1 {t : Kˣ} (ht : h.bar t = t) :
    miyamotoIHom h (1, t ^ 2) ∈ miyamotoI2r1 h := by
  have e : t ^ (2 ^ f - 1) = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact pow_sub_one_eq_one_of_bar h ht t.ne_zero)
  exact (mem_miyamotoI2r1 h).2 ⟨t, by rw [e]⟩

variable [CharP K 2]

theorem eq_one_of_sq_eq_one {s : K} (hs : s ^ 2 = 1) : s = 1 := by
  have e : (s + 1) ^ 2 = 0 := by
    linear_combination hs + (s + 1) * CharTwo.two_eq_zero (R := K)
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 e
  linear_combination this - CharTwo.two_eq_zero (R := K)

theorem miyamotoP_inf_centralizer_I2 (hf : 2 ≤ f) :
    miyamotoP h ⊓ centralizer (miyamotoI2 h : Set (GL (Fin 4) K)) = miyamotoRootB h := by
  obtain ⟨t, ht, ht2⟩ := exists_fixed_unit_sq_ne_one h hf
  have ht4 : ((t : K) ^ 2) ^ 2 ≠ 1 := fun e => ht2 (eq_one_of_sq_eq_one e)
  apply le_antisymm
  · rintro g ⟨hgP, hgC⟩
    obtain ⟨a, b, c, d, hb, -, rfl⟩ := (mem_P h).1 hgP
    have e := (mem_centralizer_singleton_iff_conj).1 (centralizer_le
      (Set.singleton_subset_iff.2 (miyamotoIHom_sq_one_mem_I2 h ht)) hgC)
    rw [miyamotoIHom_conj, miyamotoXGL_inj] at e
    simp only [Units.val_pow_eq_pow_val, Units.val_one, inv_one, mul_one, map_pow, ht,
      map_one] at e
    have ha : a = 0 := eq_zero_of_mul_eq_self ht2 e.1
    have hc : c = 0 := eq_zero_of_mul_eq_self ht2 e.2.2.1
    have hd : d = 0 := eq_zero_of_mul_eq_self ht4 (by linear_combination e.2.2.2)
    subst ha hc hd
    exact ⟨b, hb, rfl⟩
  · rintro _ ⟨b, hb, rfl⟩
    refine ⟨(miyamotoXGL_mem_P h).2 ⟨hb, by simp⟩, mem_centralizer_iff.2 fun g hg => ?_⟩
    obtain ⟨a, rfl⟩ := hg
    refine (mem_centralizer_singleton_iff.1 ((mem_centralizer_singleton_iff_conj).2 ?_)).symm
    rw [miyamotoI2Hom_conj]
    simp

theorem miyamotoP_inf_centralizer_I2r1 (hf : 2 ≤ f) :
    miyamotoP h ⊓ centralizer (miyamotoI2r1 h : Set (GL (Fin 4) K)) = miyamotoZ h := by
  obtain ⟨t, ht, ht2⟩ := exists_fixed_unit_sq_ne_one h hf
  have ht0 : (t : K) ≠ 0 := t.ne_zero
  have ht4 : ((t : K) ^ 2) ^ 2 ≠ 1 := fun e => ht2 (eq_one_of_sq_eq_one e)
  have ht2' : ((t : K) ^ 2)⁻¹ ≠ 1 := fun e => ht2 (inv_eq_one.1 e)
  apply le_antisymm
  · rintro g ⟨hgP, hgC⟩
    obtain ⟨a, b, c, d, hb, hd, rfl⟩ := (mem_P h).1 hgP
    have e := (mem_centralizer_singleton_iff_conj).1 (centralizer_le
      (Set.singleton_subset_iff.2 (miyamotoIHom_one_sq_mem_I2r1 h ht)) hgC)
    rw [miyamotoIHom_conj, miyamotoXGL_inj] at e
    simp only [Units.val_pow_eq_pow_val, Units.val_one, one_mul, map_pow, ht, map_one,
      mul_one] at e
    have ha : a = 0 := eq_zero_of_mul_eq_self ht2' e.1
    have hb0 : b = 0 := eq_zero_of_mul_eq_self ht4 (by linear_combination e.2.1)
    have hc : c = 0 := eq_zero_of_mul_eq_self ht2 e.2.2.1
    subst ha hb0 hc
    exact (miyamotoXGL_mem_Z h).2 ⟨rfl, rfl, rfl, (add_bar_eq_zero_iff h).1 (by simpa using hd)⟩
  · rintro _ ⟨d, hd, rfl⟩
    refine ⟨miyamotoZ_le_P h ⟨d, hd, rfl⟩, mem_centralizer_iff.2 fun g hg => ?_⟩
    obtain ⟨a, rfl⟩ := (mem_miyamotoI2r1 h).1 hg
    refine (mem_centralizer_singleton_iff.1 ((mem_centralizer_singleton_iff_conj).2 ?_)).symm
    rw [miyamotoI2r1Hom_conj]
    simp

theorem miyamotoZ_mul_rootC :
    (miyamotoZ h : Set (GL (Fin 4) K)) * miyamotoRootC h = miyamotoZ2 h := by
  have key : ∀ c d : K, miyamotoXGL h 0 0 0 d * miyamotoXGL h 0 0 c 0 = miyamotoXGL h 0 0 c d := by
    intro c d
    rw [miyamotoXGL_mul h (map_zero _), miyamotoXGL_inj]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp
  ext g
  rw [Set.mem_mul, SetLike.mem_coe]
  constructor
  · rintro ⟨_, ⟨d, hd, rfl⟩, _, ⟨c, rfl⟩, rfl⟩
    rw [key]
    exact (miyamotoXGL_mem_Z2 h).2 ⟨rfl, rfl, hd⟩
  · intro hg
    obtain ⟨c, d, hd, rfl⟩ := (mem_Z2 h).1 hg
    exact ⟨_, ⟨d, hd, rfl⟩, _, ⟨c, rfl⟩, key c d⟩

theorem miyamotoZ2_mul_rootA :
    (miyamotoZ2 h : Set (GL (Fin 4) K)) * miyamotoRootA h = miyamotoA2 h := by
  have hbb := h.bar_bar
  have key : ∀ a c d : K, miyamotoXGL h 0 0 c d * miyamotoXGL h a 0 0 0 =
      miyamotoXGL h a 0 c (d + h.bar c * a) := by
    intro a c d
    rw [miyamotoXGL_mul h (map_zero _), miyamotoXGL_inj]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp
  ext g
  rw [Set.mem_mul, SetLike.mem_coe]
  constructor
  · rintro ⟨_, hz, _, ⟨a, rfl⟩, rfl⟩
    obtain ⟨c, d, hd, rfl⟩ := (mem_Z2 h).1 hz
    rw [key]
    refine (miyamotoXGL_mem_A2 h).2 ⟨rfl, ?_⟩
    simp only [map_add, map_mul, hbb, hd]
    linear_combination (d + a * h.bar c + h.bar a * c) * CharTwo.two_eq_zero (R := K)
  · intro hg
    obtain ⟨a, c, d, hd, rfl⟩ := (mem_A2 h).1 hg
    refine ⟨miyamotoXGL h 0 0 c (d + h.bar c * a), (miyamotoXGL_mem_Z2 h).2 ⟨rfl, rfl, ?_⟩, _,
      ⟨a, rfl⟩, ?_⟩
    · rw [← add_bar_eq_zero_iff h]
      simp only [map_add, map_mul, hbb]
      linear_combination hd
    · rw [key, miyamotoXGL_inj]
      refine ⟨rfl, rfl, rfl, ?_⟩
      linear_combination (h.bar c * a) * CharTwo.two_eq_zero (R := K)

theorem miyamotoA1_mul_rootA :
    (miyamotoA1 h : Set (GL (Fin 4) K)) * miyamotoRootA h = miyamotoP h := by
  have hbb := h.bar_bar
  ext g
  rw [Set.mem_mul, SetLike.mem_coe]
  constructor
  · rintro ⟨_, hA, _, ⟨a, rfl⟩, rfl⟩
    exact mul_mem (miyamotoA1_le_P h hA) ((miyamotoRootA_le_A2 h).trans (miyamotoA2_le_P h)
      ⟨a, rfl⟩)
  · intro hg
    obtain ⟨a, b, c, d, hb, hd, rfl⟩ := (mem_P h).1 hg
    refine ⟨miyamotoXGL h 0 b (c + b * a) (d + h.bar (c + b * a) * a), ?_, _, ⟨a, rfl⟩, ?_⟩
    · refine (miyamotoXGL_mem_A1 h).2 ⟨rfl, hb, ?_⟩
      rw [← add_bar_eq_zero_iff h]
      simp only [map_add, map_mul, hbb, hb]
      linear_combination hd + (b * a * h.bar a) * CharTwo.two_eq_zero (R := K)
    · rw [miyamotoXGL_mul h hb, miyamotoXGL_inj]
      refine ⟨by ring, by ring, ?_, ?_⟩
      · linear_combination (b * a) * CharTwo.two_eq_zero (R := K)
      · simp only [map_zero, zero_mul, add_zero, mul_zero]
        linear_combination (h.bar (c + b * a) * a) * CharTwo.two_eq_zero (R := K)

theorem miyamotoA2_mul_rootB :
    (miyamotoA2 h : Set (GL (Fin 4) K)) * miyamotoRootB h = miyamotoP h := by
  ext g
  rw [Set.mem_mul, SetLike.mem_coe]
  constructor
  · rintro ⟨_, hA, _, hB, rfl⟩
    exact mul_mem (miyamotoA2_le_P h hA) ((miyamotoRootB_le_A1 h).trans (miyamotoA1_le_P h) hB)
  · intro hg
    obtain ⟨a, b, c, d, hb, hd, rfl⟩ := (mem_P h).1 hg
    refine ⟨_, (miyamotoXGL_mem_A2 h).2 ⟨rfl, hd⟩, _, ⟨b, hb, rfl⟩, ?_⟩
    rw [miyamotoXGL_mul h (map_zero _), miyamotoXGL_inj]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp

omit [CharP K 2] in
theorem miyamotoZ_inf_rootC : miyamotoZ h ⊓ miyamotoRootC h = ⊥ := by
  refine (eq_bot_iff_forall _).2 fun g ⟨hZ, hC⟩ => ?_
  obtain ⟨c, rfl⟩ := hC
  obtain ⟨-, -, rfl, -⟩ := (miyamotoXGL_mem_Z h).1 hZ
  exact miyamotoXGL_zero h

theorem miyamotoZ2_inf_rootB : miyamotoZ2 h ⊓ miyamotoRootB h = ⊥ := by
  refine (eq_bot_iff_forall _).2 fun g ⟨hZ, hB⟩ => ?_
  obtain ⟨b, -, rfl⟩ := hB
  obtain ⟨-, rfl, -⟩ := (miyamotoXGL_mem_Z2 h).1 hZ
  exact miyamotoXGL_zero h

theorem miyamotoA1_inf_rootA : miyamotoA1 h ⊓ miyamotoRootA h = ⊥ := by
  refine (eq_bot_iff_forall _).2 fun g ⟨h1, hA⟩ => ?_
  obtain ⟨a, rfl⟩ := hA
  obtain ⟨rfl, -, -⟩ := (miyamotoXGL_mem_A1 h).1 h1
  exact miyamotoXGL_zero h

omit [CharP K 2] in
theorem miyamotoA2_inf_rootB : miyamotoA2 h ⊓ miyamotoRootB h = ⊥ := by
  refine (eq_bot_iff_forall _).2 fun g ⟨h2, hB⟩ => ?_
  obtain ⟨b, -, rfl⟩ := hB
  obtain ⟨rfl, -⟩ := (miyamotoXGL_mem_A2 h).1 h2
  exact miyamotoXGL_zero h

end Factorizations

section Transitivity

theorem exists_unit_norm_eq {s : K} (hs : h.bar s = s) (hs0 : s ≠ 0) :
    ∃ β : Kˣ, (β : K) * h.bar β = s := by
  obtain ⟨β, hβ⟩ := h.normHom_surjective ⟨s, hs⟩
  have hβ' : β * h.bar β = s := congrArg Subtype.val hβ
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hβ'
    exact hs0 hβ'.symm
  exact ⟨Units.mk0 β hβ0, hβ'⟩

theorem exists_conj_rootA {a a' : K} (ha : a ≠ 0) (ha' : a' ≠ 0) :
    ∃ g ∈ miyamotoI h, g⁻¹ * miyamotoXGL h a 0 0 0 * g = miyamotoXGL h a' 0 0 0 := by
  obtain ⟨p, hp, -, hA⟩ := exists_miyamotoIParam_eq_one_weightB_eq_one h (Units.mk0 (a' / a)
    (div_ne_zero ha' ha))
  refine ⟨miyamotoIHom h p, ⟨p, hp, rfl⟩, ?_⟩
  rw [miyamotoIHom_conj_rootA, hA]
  simp [ha]

theorem exists_conj_rootC {c c' : K} (hc : c ≠ 0) (hc' : c' ≠ 0) :
    ∃ g ∈ miyamotoI h, g⁻¹ * miyamotoXGL h 0 0 c 0 * g = miyamotoXGL h 0 0 c' 0 := by
  obtain ⟨p, hp, hB, hA⟩ := exists_miyamotoIParam_eq_one_weightB_eq_one h (Units.mk0 (c' / c)
    (div_ne_zero hc' hc))
  refine ⟨miyamotoIHom h p, ⟨p, hp, rfl⟩, ?_⟩
  rw [miyamotoIHom_conj_rootC]
  have hB' : ((miyamotoWeightB h p : Kˣ) : K) = 1 := by rw [hB, Units.val_one]
  have hA' : ((miyamotoWeightA p : Kˣ) : K) = c' / c := by rw [hA, Units.val_mk0]
  rw [coe_miyamotoWeightB] at hB'
  rw [coe_miyamotoWeightA] at hA'
  rw [coe_miyamotoWeightC]
  have h2 : (p.2 : K) ≠ 0 := p.2.ne_zero
  have hbar : h.bar (p.2 : K) = (p.2 : K)⁻¹ := eq_inv_of_mul_eq_one_right hB'
  rw [hbar, hA']
  field_simp

theorem exists_conj_rootB {b b' : K} (hb : h.bar b = b) (hb' : h.bar b' = b') (hb0 : b ≠ 0)
    (hb0' : b' ≠ 0) :
    ∃ g ∈ miyamotoI h, g⁻¹ * miyamotoXGL h 0 b 0 0 * g = miyamotoXGL h 0 b' 0 0 := by
  obtain ⟨β, hβ⟩ := exists_unit_norm_eq h (s := b' / b) (by rw [map_div₀, hb, hb'])
    (div_ne_zero hb0' hb0)
  refine ⟨miyamotoIHom h (β⁻¹, β), (miyamotoIHom_mem_miyamotoI_iff h _).2
    ((miyamotoIParam_eq_one_iff h _).2 (by simp)), ?_⟩
  rw [miyamotoIHom_conj_rootB, coe_miyamotoWeightB, hβ]
  field_simp

theorem exists_conj_Z {d d' : K} (hd : h.bar d = d) (hd' : h.bar d' = d') (hd0 : d ≠ 0)
    (hd0' : d' ≠ 0) :
    ∃ g ∈ miyamotoI h, g⁻¹ * miyamotoXGL h 0 0 0 d * g = miyamotoXGL h 0 0 0 d' := by
  obtain ⟨α, hα⟩ := exists_unit_norm_eq h (s := d' / d) (by rw [map_div₀, hd, hd'])
    (div_ne_zero hd0' hd0)
  refine ⟨miyamotoIHom h (α, α⁻¹), (miyamotoIHom_mem_miyamotoI_iff h _).2
    ((miyamotoIParam_eq_one_iff h _).2 (by simp)), ?_⟩
  rw [miyamotoIHom_conj_Z, coe_miyamotoWeightZ, hα]
  field_simp

@[expose] def ConjTransitiveOn {G : Type*} [Group G] (N H : Subgroup G) : Prop :=
  ∀ x ∈ H, ∀ y ∈ H, x ≠ 1 → y ≠ 1 → ∃ g ∈ N, g⁻¹ * x * g = y

theorem miyamoto_two_one_three [CharP K 2] (hf : 2 ≤ f) :
    ConjTransitiveOn (miyamotoI h)
        (miyamotoP h ⊓ centralizer (miyamotoI1 h : Set (GL (Fin 4) K))) ∧
      ConjTransitiveOn (miyamotoI h)
        (miyamotoP h ⊓ centralizer (miyamotoI1r2 h : Set (GL (Fin 4) K))) ∧
      ConjTransitiveOn (miyamotoI h)
        (miyamotoP h ⊓ centralizer (miyamotoI2 h : Set (GL (Fin 4) K))) ∧
      ConjTransitiveOn (miyamotoI h)
        (miyamotoP h ⊓ centralizer (miyamotoI2r1 h : Set (GL (Fin 4) K))) := by
  rw [miyamotoP_inf_centralizer_I1 h hf, miyamotoP_inf_centralizer_I1r2 h hf,
    miyamotoP_inf_centralizer_I2 h hf, miyamotoP_inf_centralizer_I2r1 h hf]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro _ ⟨a, rfl⟩ _ ⟨a', rfl⟩ hx hy
    refine exists_conj_rootA h (fun e => hx ?_) (fun e => hy ?_)
    · rw [e, miyamotoXGL_zero]
    · rw [e, miyamotoXGL_zero]
  · rintro _ ⟨c, rfl⟩ _ ⟨c', rfl⟩ hx hy
    refine exists_conj_rootC h (fun e => hx ?_) (fun e => hy ?_)
    · rw [e, miyamotoXGL_zero]
    · rw [e, miyamotoXGL_zero]
  · rintro _ ⟨b, hb, rfl⟩ _ ⟨b', hb', rfl⟩ hx hy
    refine exists_conj_rootB h hb hb' (fun e => hx ?_) (fun e => hy ?_)
    · rw [e, miyamotoXGL_zero]
    · rw [e, miyamotoXGL_zero]
  · rintro _ ⟨d, hd, rfl⟩ _ ⟨d', hd', rfl⟩ hx hy
    refine exists_conj_Z h hd hd' (fun e => hx ?_) (fun e => hy ?_)
    · rw [e, miyamotoXGL_zero]
    · rw [e, miyamotoXGL_zero]

end Transitivity

end CFSG.LocalAnalysis.EvenBN.U4
