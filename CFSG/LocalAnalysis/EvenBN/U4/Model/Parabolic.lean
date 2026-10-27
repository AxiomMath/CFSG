module

public import CFSG.LocalAnalysis.EvenBN.U4.Model.ParabolicMatrix
public import CFSG.LocalAnalysis.EvenBN.U4.Model.Rank

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

section LeviFactors

@[expose] def miyamotoN1Hom : SpecialLinearGroup (Fin 2) K →* GL (Fin 4) K :=
  (Units.map (miyamotoN1Mat h)).comp SpecialLinearGroup.toGL

theorem coe_miyamotoN1Hom (m : SpecialLinearGroup (Fin 2) K) :
    ((miyamotoN1Hom h m : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      miyamotoN1Mat h (m : Matrix (Fin 2) (Fin 2) K) :=
  rfl

theorem miyamotoN1Hom_injective : Function.Injective (miyamotoN1Hom h) := by
  intro m m' e
  have ent : ∀ i j : Fin 4, miyamotoN1Mat h (m : Matrix (Fin 2) (Fin 2) K) i j =
      miyamotoN1Mat h (m' : Matrix (Fin 2) (Fin 2) K) i j := fun i j => by
    rw [← coe_miyamotoN1Hom, ← coe_miyamotoN1Hom, e]
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [miyamotoN1Mat] using ent 0 0
  · simpa [miyamotoN1Mat] using ent 0 1
  · simpa [miyamotoN1Mat] using ent 1 0
  · simpa [miyamotoN1Mat] using ent 1 1

@[expose] def miyamotoN1Equiv : SpecialLinearGroup (Fin 2) K ≃* miyamotoN1 h :=
  MonoidHom.ofInjective (miyamotoN1Hom_injective h)

theorem coe_miyamotoN1Equiv (m : SpecialLinearGroup (Fin 2) K) :
    ((miyamotoN1Equiv h m : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      miyamotoN1Mat h (m : Matrix (Fin 2) (Fin 2) K) :=
  rfl

@[expose] def miyamotoN2Hom : SpecialLinearGroup (Fin 2) h.fixedField →* GL (Fin 4) K :=
  (Units.map (miyamotoN2Mat K)).comp (SpecialLinearGroup.toGL.comp
    (SpecialLinearGroup.map (h.fixedField.subtype : h.fixedField →+* K)))

theorem coe_miyamotoN2Hom (m : SpecialLinearGroup (Fin 2) h.fixedField) :
    ((miyamotoN2Hom h m : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      miyamotoN2Mat K ((m : Matrix (Fin 2) (Fin 2) h.fixedField).map h.fixedField.subtype) :=
  rfl

theorem miyamotoN2Hom_injective : Function.Injective (miyamotoN2Hom h) := by
  intro m m' e
  have ent : ∀ i j : Fin 4,
      miyamotoN2Mat K ((m : Matrix (Fin 2) (Fin 2) h.fixedField).map h.fixedField.subtype) i j =
      miyamotoN2Mat K ((m' : Matrix (Fin 2) (Fin 2) h.fixedField).map h.fixedField.subtype) i j :=
    fun i j => by rw [← coe_miyamotoN2Hom, ← coe_miyamotoN2Hom, e]
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [miyamotoN2Mat] using ent 1 1
  · simpa [miyamotoN2Mat] using ent 1 2
  · simpa [miyamotoN2Mat] using ent 2 1
  · simpa [miyamotoN2Mat] using ent 2 2

@[expose] def miyamotoN2Equiv : SpecialLinearGroup (Fin 2) h.fixedField ≃* miyamotoN2 h :=
  MonoidHom.ofInjective (miyamotoN2Hom_injective h)

theorem miyamotoI1_commute {x y : GL (Fin 4) K} (hx : x ∈ miyamotoI1 h) (hy : y ∈ miyamotoI1 h) :
    x * y = y * x := by
  obtain ⟨t, -, rfl⟩ := (mem_miyamotoI1 h).1 hx
  obtain ⟨s, -, rfl⟩ := (mem_miyamotoI1 h).1 hy
  rw [← map_mul, ← map_mul, mul_comm]

theorem miyamotoI2_commute' {x y : GL (Fin 4) K} (hx : x ∈ miyamotoI2 h)
    (hy : y ∈ miyamotoI2 h) : x * y = y * x := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  rw [← map_mul, ← map_mul, mul_comm]

theorem miyamotoI1_commute_N1 {x y : GL (Fin 4) K} (hx : x ∈ miyamotoI1 h)
    (hy : y ∈ miyamotoN1 h) : x * y = y * x := by
  obtain ⟨t, ht, rfl⟩ := (mem_miyamotoI1 h).1 hx
  obtain ⟨m, -, hm⟩ := (mem_miyamotoN1 h).1 hy
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hm, coe_miyamotoIHom]
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;> simp [miyamotoN1Mat, ht] <;> ring

theorem miyamotoI2_commute_N2 {x y : GL (Fin 4) K} (hx : x ∈ miyamotoI2 h)
    (hy : y ∈ miyamotoN2 h) : x * y = y * x := by
  obtain ⟨a, rfl⟩ := (mem_miyamotoI2 h).1 hx
  obtain ⟨m, -, -, hm⟩ := (mem_miyamotoN2 h).1 hy
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hm, coe_miyamotoIHom]
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  have ha : h.bar ((a : K) ^ (2 ^ f - 1)) = ((a : K) ^ (2 ^ f - 1))⁻¹ :=
    bar_pow_sub_one h a.ne_zero
  fin_cases i <;> fin_cases j <;> simp [miyamotoN2Mat, ha] <;> ring

variable [CharP K 2]

theorem miyamotoI1_inf_N1 : miyamotoI1 h ⊓ miyamotoN1 h = ⊥ := by
  refine (eq_bot_iff_forall _).2 fun x ⟨hx, hy⟩ => ?_
  obtain ⟨t, ht, rfl⟩ := (mem_miyamotoI1 h).1 hx
  obtain ⟨m, hm, e⟩ := (mem_miyamotoN1 h).1 hy
  rw [coe_miyamotoIHom] at e
  have e00 := congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M 0 0) e
  have e01 := congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M 0 1) e
  have e10 := congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M 1 0) e
  have e11 := congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M 1 1) e
  simp [miyamotoN1Mat] at e00 e01 e10 e11
  rw [Matrix.det_fin_two, ← e00, ← e01, ← e10, ← e11, mul_zero, sub_zero] at hm
  have ht1 : (t : K) = 1 := eq_one_of_sq_eq_one (by rw [sq]; exact hm)
  have : t = 1 := Units.ext ht1
  rw [this]
  exact map_one _

theorem miyamotoI2_inf_N2 : miyamotoI2 h ⊓ miyamotoN2 h = ⊥ := by
  refine (eq_bot_iff_forall _).2 fun x ⟨hx, hy⟩ => ?_
  obtain ⟨a, rfl⟩ := (mem_miyamotoI2 h).1 hx
  obtain ⟨m, -, -, e⟩ := (mem_miyamotoN2 h).1 hy
  rw [coe_miyamotoIHom] at e
  have e00 := congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M 0 0) e
  simp only [miyamotoN2Mat, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.diagonal_apply_eq,
    Units.val_pow_eq_pow_val] at e00
  have ha1 : (a : K) = 1 := eq_one_of_sq_eq_one e00
  have : a = 1 := Units.ext ha1
  rw [this, one_pow, one_pow]
  exact map_one _

end LeviFactors

section LeviNormalizes

variable [CharP K 2]

theorem conj_mem_A1_of_mem_N1 {n x : GL (Fin 4) K} (hn : n ∈ miyamotoN1 h)
    (hx : x ∈ miyamotoA1 h) : n⁻¹ * x * n ∈ miyamotoA1 h := by
  obtain ⟨m, hm, hnm⟩ := (mem_miyamotoN1 h).1 hn
  obtain ⟨b, c, d, hb, hd, rfl⟩ := (mem_A1 h).1 hx
  have hyS : n⁻¹ * miyamotoXGL h 0 b c d * n ∈ gramSU h (miyamotoJ4 K) :=
    mul_mem (mul_mem (inv_mem (miyamotoN1_le_gramSU h hn))
      (miyamotoUnipotent_le_SU h true false hx)) (miyamotoN1_le_gramSU h hn)
  obtain ⟨Y, hY⟩ : ∃ Y, ((n⁻¹ * miyamotoXGL h 0 b c d * n : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) = Y := ⟨_, rfl⟩
  have e : n * (n⁻¹ * miyamotoXGL h 0 b c d * n) = miyamotoXGL h 0 b c d * n := by group
  have ent : ∀ i j, ((n : Matrix (Fin 4) (Fin 4) K) * Y) i j =
      (miyamotoX h 0 b c d * (n : Matrix (Fin 4) (Fin 4) K)) i j := fun i j => by
    rw [← hY, ← coe_miyamotoXGL, ← Units.val_mul, ← Units.val_mul, e]
  rw [Matrix.det_fin_two] at hm
  have hm0 : m 0 0 * m 1 1 - m 1 0 * m 0 1 ≠ 0 := by
    rw [mul_comm (m 1 0), hm]
    exact one_ne_zero
  have hmb : h.bar (m 0 0) * h.bar (m 1 1) - h.bar (m 1 0) * h.bar (m 0 1) ≠ 0 := by
    rw [← map_mul, ← map_mul, ← map_sub, mul_comm (m 1 0), hm, map_one]
    exact one_ne_zero
  have q00 := ent 0 0
  have q10 := ent 1 0
  have q01 := ent 0 1
  have q11 := ent 1 1
  have q02 := ent 0 2
  have q12 := ent 1 2
  have q03 := ent 0 3
  have q13 := ent 1 3
  have q22 := ent 2 2
  have q32 := ent 3 2
  have q23 := ent 2 3
  have q33 := ent 3 3
  simp [Matrix.mul_apply, Fin.sum_univ_four, hnm, miyamotoN1Mat, miyamotoX] at q00 q10 q01 q11
  simp [Matrix.mul_apply, Fin.sum_univ_four, hnm, miyamotoN1Mat, miyamotoX] at q02 q12 q03 q13
  simp [Matrix.mul_apply, Fin.sum_univ_four, hnm, miyamotoN1Mat, miyamotoX] at q22 q32 q23 q33
  obtain ⟨r00, r10⟩ := cancel_two hm0 (u := Y 0 0) (v := Y 1 0)
    (x := 1) (y := 0) (by linear_combination q00) (by linear_combination q10)
  obtain ⟨r01, r11⟩ := cancel_two hm0 (u := Y 0 1) (v := Y 1 1)
    (x := 0) (y := 1) (by linear_combination q01) (by linear_combination q11)
  obtain ⟨r02, r12⟩ := cancel_two hm0 (u := Y 0 2) (v := Y 1 2)
    (x := 0) (y := 0) (by linear_combination q02) (by linear_combination q12)
  obtain ⟨r03, r13⟩ := cancel_two hm0 (u := Y 0 3) (v := Y 1 3)
    (x := 0) (y := 0) (by linear_combination q03) (by linear_combination q13)
  obtain ⟨r22, r32⟩ := cancel_two hmb (u := Y 2 2) (v := Y 3 2)
    (x := 1) (y := 0) (by linear_combination q22) (by linear_combination q32)
  obtain ⟨r23, r33⟩ := cancel_two hmb (u := Y 2 3) (v := Y 3 3)
    (x := 0) (y := 1) (by linear_combination q23) (by linear_combination q33)
  rw [← hY] at r00 r10 r01 r11 r02 r12 r03 r13 r22 r23 r33
  exact (mem_P_of_lowerUnitriangular h hyS r00 r01 r02 r03 r11 r12 r13 r22 r23 r33).2.2 r10

theorem conj_mem_A2_of_mem_N2 {n x : GL (Fin 4) K} (hn : n ∈ miyamotoN2 h)
    (hx : x ∈ miyamotoA2 h) : n⁻¹ * x * n ∈ miyamotoA2 h := by
  obtain ⟨m, hm, -, hnm⟩ := (mem_miyamotoN2 h).1 hn
  obtain ⟨a, c, d, hd, rfl⟩ := (mem_A2 h).1 hx
  have hyS : n⁻¹ * miyamotoXGL h a 0 c d * n ∈ gramSU h (miyamotoJ4 K) :=
    mul_mem (mul_mem (inv_mem (miyamotoN2_le_gramSU h hn))
      (miyamotoUnipotent_le_SU h false true hx)) (miyamotoN2_le_gramSU h hn)
  obtain ⟨Y, hY⟩ : ∃ Y, ((n⁻¹ * miyamotoXGL h a 0 c d * n : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) = Y := ⟨_, rfl⟩
  have e : n * (n⁻¹ * miyamotoXGL h a 0 c d * n) = miyamotoXGL h a 0 c d * n := by group
  have ent : ∀ i j, ((n : Matrix (Fin 4) (Fin 4) K) * Y) i j =
      (miyamotoX h a 0 c d * (n : Matrix (Fin 4) (Fin 4) K)) i j := fun i j => by
    rw [← hY, ← coe_miyamotoXGL, ← Units.val_mul, ← Units.val_mul, e]
  rw [Matrix.det_fin_two] at hm
  have hm0 : m 0 0 * m 1 1 - m 1 0 * m 0 1 ≠ 0 := by
    rw [mul_comm (m 1 0), hm]
    exact one_ne_zero
  have q00 := ent 0 0
  have q01 := ent 0 1
  have q02 := ent 0 2
  have q03 := ent 0 3
  have q11 := ent 1 1
  have q21 := ent 2 1
  have q12 := ent 1 2
  have q22 := ent 2 2
  have q13 := ent 1 3
  have q23 := ent 2 3
  have q33 := ent 3 3
  simp [Matrix.mul_apply, Fin.sum_univ_four, hnm, miyamotoN2Mat, miyamotoX] at q00 q01 q02 q03
  simp [Matrix.mul_apply, Fin.sum_univ_four, hnm, miyamotoN2Mat, miyamotoX] at q11 q21 q12 q22
  simp [Matrix.mul_apply, Fin.sum_univ_four, hnm, miyamotoN2Mat, miyamotoX] at q13 q23 q33
  obtain ⟨r11, r21⟩ := cancel_two hm0 (u := Y 1 1) (v := Y 2 1)
    (x := 1) (y := 0) (by linear_combination q11) (by linear_combination q21)
  obtain ⟨r12, r22⟩ := cancel_two hm0 (u := Y 1 2) (v := Y 2 2)
    (x := 0) (y := 1) (by linear_combination q12) (by linear_combination q22)
  obtain ⟨r13, r23⟩ := cancel_two hm0 (u := Y 1 3) (v := Y 2 3)
    (x := 0) (y := 0) (by linear_combination q13) (by linear_combination q23)
  rw [← hY] at q00 q01 q02 q03 q33 r11 r21 r12 r22 r13 r23
  exact (mem_P_of_lowerUnitriangular h hyS q00 q01 q02 q03 r11 r12 r13 r22 r23 q33).2.1 r21

theorem miyamotoN1_le_normalizer_A1 :
    miyamotoN1 h ≤ normalizer (miyamotoA1 h : Set (GL (Fin 4) K)) := by
  intro n hn
  refine mem_normalizer_iff''.2 fun x => ⟨fun hx => conj_mem_A1_of_mem_N1 h hn hx, fun hx => ?_⟩
  have := conj_mem_A1_of_mem_N1 h (inv_mem hn) hx
  rwa [inv_inv, show n * (n⁻¹ * x * n) * n⁻¹ = x by group] at this

theorem miyamotoN2_le_normalizer_A2 :
    miyamotoN2 h ≤ normalizer (miyamotoA2 h : Set (GL (Fin 4) K)) := by
  intro n hn
  refine mem_normalizer_iff''.2 fun x => ⟨fun hx => conj_mem_A2_of_mem_N2 h hn hx, fun hx => ?_⟩
  have := conj_mem_A2_of_mem_N2 h (inv_mem hn) hx
  rwa [inv_inv, show n * (n⁻¹ * x * n) * n⁻¹ = x by group] at this

end LeviNormalizes

section Normalizers

theorem entry_eq_zero_of_commute_diagonal {g x : GL (Fin 4) K} {v : Fin 4 → K}
    (hx : (x : Matrix (Fin 4) (Fin 4) K) = diagonal v) (hc : g * x = x * g) {i j : Fin 4}
    (hij : v i ≠ v j) : (g : Matrix (Fin 4) (Fin 4) K) i j = 0 := by
  have e := congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M i j) (congrArg Units.val hc)
  simp only [Units.val_mul, hx, Matrix.mul_diagonal, Matrix.diagonal_mul] at e
  have : (g : Matrix (Fin 4) (Fin 4) K) i j * (v j - v i) = 0 := by linear_combination e
  exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 (Ne.symm hij))

variable [CharP K 2]

theorem miyamotoI1_sup_N1_le :
    miyamotoI1 h ⊔ miyamotoN1 h ≤
      gramSU h (miyamotoJ4 K) ⊓ centralizer (miyamotoI1 h : Set (GL (Fin 4) K)) :=
  sup_le (le_inf (miyamotoI1_le_SU h) fun _ hx => mem_centralizer_iff.2 fun _ hy =>
      miyamotoI1_commute h hy hx)
    (le_inf (miyamotoN1_le_gramSU h) fun _ hx => mem_centralizer_iff.2 fun _ hy =>
      miyamotoI1_commute_N1 h hy hx)

theorem miyamotoI2_sup_N2_le :
    miyamotoI2 h ⊔ miyamotoN2 h ≤
      gramSU h (miyamotoJ4 K) ⊓ centralizer (miyamotoI2 h : Set (GL (Fin 4) K)) :=
  sup_le (le_inf (miyamotoI2_le_SU h) fun _ hx => mem_centralizer_iff.2 fun _ hy =>
      miyamotoI2_commute' h hy hx)
    (le_inf (miyamotoN2_le_gramSU h) fun _ hx => mem_centralizer_iff.2 fun _ hy =>
      miyamotoI2_commute_N2 h hy hx)

theorem centralizer_miyamotoI1 (hf : 2 ≤ f) :
    gramSU h (miyamotoJ4 K) ⊓ centralizer (miyamotoI1 h : Set (GL (Fin 4) K)) =
      miyamotoI1 h ⊔ miyamotoN1 h := by
  refine le_antisymm (fun g hg => ?_) (miyamotoI1_sup_N1_le h)
  obtain ⟨hgS, hgC⟩ := mem_inf.1 hg
  obtain ⟨t, ht, ht2⟩ := exists_fixed_unit_sq_ne_one h hf
  have hD : miyamotoIHom h (t, t) ∈ miyamotoI1 h := (mem_miyamotoI1 h).2 ⟨t, ht, rfl⟩
  have hc : g * miyamotoIHom h (t, t) = miyamotoIHom h (t, t) * g :=
    (mem_centralizer_iff.1 hgC _ hD).symm
  have ht0 : (t : K) ≠ 0 := t.ne_zero
  have hne : (t : K) ≠ (h.bar (t : K))⁻¹ := by
    rw [ht]
    intro e
    exact ht2 (by rw [sq]; exact (mul_eq_one_iff_eq_inv₀ ht0).2 e)
  have hcoe := coe_miyamotoIHom h (t, t)
  have z : ∀ {i j : Fin 4}, i.val < 2 → 2 ≤ j.val → (g : Matrix (Fin 4) (Fin 4) K) i j = 0 := by
    intro i j hi hj
    refine entry_eq_zero_of_commute_diagonal hcoe hc ?_
    fin_cases i <;> fin_cases j <;> simp_all
  obtain ⟨a, ha, i, hi, n, hn, rfl⟩ := exists_mul_of_shapeOne h hgS (z (by decide) (by decide))
    (z (by decide) (by decide)) (z (by decide) (by decide)) (z (by decide) (by decide))
  have hin : i * n ∈ centralizer (miyamotoI1 h : Set (GL (Fin 4) K)) :=
    ((miyamotoI1_sup_N1_le h) (mul_mem (mem_sup_left hi) (mem_sup_right hn))).2
  have haC : a ∈ centralizer (miyamotoI1 h : Set (GL (Fin 4) K)) := by
    have := mul_mem hgC (inv_mem hin)
    rwa [show a * i * n * (i * n)⁻¹ = a by group] at this
  have ha1 : a ∈ miyamotoA1 h ⊓ miyamotoRootA h := by
    refine ⟨ha, ?_⟩
    rw [← miyamotoP_inf_centralizer_I1 h hf]
    exact ⟨miyamotoA1_le_P h ha, haC⟩
  rw [miyamotoA1_inf_rootA, mem_bot] at ha1
  rw [ha1, one_mul]
  exact mul_mem (mem_sup_left hi) (mem_sup_right hn)

theorem centralizer_miyamotoI2 (hf : 2 ≤ f) :
    gramSU h (miyamotoJ4 K) ⊓ centralizer (miyamotoI2 h : Set (GL (Fin 4) K)) =
      miyamotoI2 h ⊔ miyamotoN2 h := by
  refine le_antisymm (fun g hg => ?_) (miyamotoI2_sup_N2_le h)
  obtain ⟨hgS, hgC⟩ := mem_inf.1 hg
  obtain ⟨t, ht, ht2⟩ := exists_fixed_unit_sq_ne_one h hf
  have hD := miyamotoIHom_sq_one_mem_I2 h ht
  have hc : g * miyamotoIHom h (t ^ 2, 1) = miyamotoIHom h (t ^ 2, 1) * g :=
    (mem_centralizer_iff.1 hgC _ hD).symm
  have ht0 : (t : K) ≠ 0 := t.ne_zero
  have ht4 : ((t : K) ^ 2) ^ 2 ≠ 1 := fun e => ht2 (eq_one_of_sq_eq_one e)
  have hcoe : ((miyamotoIHom h (t ^ 2, 1) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      diagonal ![(t : K) ^ 2, 1, 1, ((t : K) ^ 2)⁻¹] := by
    rw [coe_miyamotoIHom]
    simp [map_pow, ht]
  have hn0 : (t : K) ^ 2 ≠ ((t : K) ^ 2)⁻¹ := by
    intro e
    apply ht4
    field_simp at e
    linear_combination e
  have hn1 : (1 : K) ≠ ((t : K) ^ 2)⁻¹ := fun e => ht2 (inv_eq_one.1 e.symm)
  have z : ∀ {i : Fin 4}, i.val < 3 → (g : Matrix (Fin 4) (Fin 4) K) i 3 = 0 := by
    intro i hi
    refine entry_eq_zero_of_commute_diagonal hcoe hc ?_
    fin_cases i
    · exact hn0
    · exact hn1
    · exact hn1
    · exact absurd hi (by decide)
  obtain ⟨a, ha, i, hi, n, hn, rfl⟩ := exists_mul_of_shapeTwo h hgS (z (by decide))
    (z (by decide)) (z (by decide))
  have hin : i * n ∈ centralizer (miyamotoI2 h : Set (GL (Fin 4) K)) :=
    ((miyamotoI2_sup_N2_le h) (mul_mem (mem_sup_left hi) (mem_sup_right hn))).2
  have haC : a ∈ centralizer (miyamotoI2 h : Set (GL (Fin 4) K)) := by
    have := mul_mem hgC (inv_mem hin)
    rwa [show a * i * n * (i * n)⁻¹ = a by group] at this
  have ha1 : a ∈ miyamotoA2 h ⊓ miyamotoRootB h := by
    refine ⟨ha, ?_⟩
    rw [← miyamotoP_inf_centralizer_I2 h hf]
    exact ⟨miyamotoA2_le_P h ha, haC⟩
  rw [miyamotoA2_inf_rootB, mem_bot] at ha1
  rw [ha1, one_mul]
  exact mul_mem (mem_sup_left hi) (mem_sup_right hn)

theorem normalizer_miyamotoA1 :
    gramSU h (miyamotoJ4 K) ⊓ normalizer (miyamotoA1 h : Set (GL (Fin 4) K)) =
      miyamotoA1 h ⊔ (miyamotoI1 h ⊔ miyamotoN1 h) := by
  refine le_antisymm (fun g hg => ?_) (sup_le (le_inf (miyamotoUnipotent_le_SU h true false)
    le_normalizer) (sup_le (le_inf (miyamotoI1_le_SU h) ((miyamotoI1_le_I h).trans
      (miyamotoI_le_normalizer_unipotent h true false))) (le_inf (miyamotoN1_le_gramSU h)
        (miyamotoN1_le_normalizer_A1 h))))
  obtain ⟨hgS, hgN⟩ := mem_inf.1 hg
  obtain ⟨h02, h03, h12, h13⟩ := shapeOne_of_mem_normalizer_A1 h hgN
  obtain ⟨a, ha, i, hi, n, hn, rfl⟩ := exists_mul_of_shapeOne h hgS h02 h03 h12 h13
  exact mul_mem (mul_mem (mem_sup_left ha) (mem_sup_right (mem_sup_left hi)))
    (mem_sup_right (mem_sup_right hn))

theorem normalizer_A2_le_normalizer_Z :
    normalizer (miyamotoA2 h : Set (GL (Fin 4) K)) ≤
      normalizer (miyamotoZ h : Set (GL (Fin 4) K)) := by
  rw [← centerIn_miyamotoA2 h]
  exact normalizer_le_normalizer_centerIn _

theorem miyamotoA2_sup_levi_le :
    miyamotoA2 h ⊔ (miyamotoI2 h ⊔ miyamotoN2 h) ≤
      gramSU h (miyamotoJ4 K) ⊓ normalizer (miyamotoA2 h : Set (GL (Fin 4) K)) :=
  sup_le (le_inf (miyamotoUnipotent_le_SU h false true) le_normalizer)
    (sup_le (le_inf (miyamotoI2_le_SU h) ((miyamotoI2_le_I h).trans
      (miyamotoI_le_normalizer_unipotent h false true))) (le_inf (miyamotoN2_le_gramSU h)
        (miyamotoN2_le_normalizer_A2 h)))

theorem mem_levi_of_mem_normalizer_Z {g : GL (Fin 4) K} (hgS : g ∈ gramSU h (miyamotoJ4 K))
    (hgN : g ∈ normalizer (miyamotoZ h : Set (GL (Fin 4) K))) :
    g ∈ miyamotoA2 h ⊔ (miyamotoI2 h ⊔ miyamotoN2 h) := by
  obtain ⟨h03, h13, h23⟩ := shapeTwo_of_mem_normalizer_Z h hgN
  obtain ⟨a, ha, i, hi, n, hn, rfl⟩ := exists_mul_of_shapeTwo h hgS h03 h13 h23
  exact mul_mem (mul_mem (mem_sup_left ha) (mem_sup_right (mem_sup_left hi)))
    (mem_sup_right (mem_sup_right hn))

theorem normalizer_miyamotoA2 :
    gramSU h (miyamotoJ4 K) ⊓ normalizer (miyamotoA2 h : Set (GL (Fin 4) K)) =
      miyamotoA2 h ⊔ (miyamotoI2 h ⊔ miyamotoN2 h) := by
  refine le_antisymm (fun g hg => ?_) (miyamotoA2_sup_levi_le h)
  obtain ⟨hgS, hgN⟩ := mem_inf.1 hg
  exact mem_levi_of_mem_normalizer_Z h hgS (normalizer_A2_le_normalizer_Z h hgN)

theorem normalizer_miyamotoZ :
    gramSU h (miyamotoJ4 K) ⊓ normalizer (miyamotoZ h : Set (GL (Fin 4) K)) =
      gramSU h (miyamotoJ4 K) ⊓ normalizer (miyamotoA2 h : Set (GL (Fin 4) K)) := by
  refine le_antisymm (fun g hg => ?_) (inf_le_inf_left _ (normalizer_A2_le_normalizer_Z h))
  obtain ⟨hgS, hgN⟩ := mem_inf.1 hg
  exact miyamotoA2_sup_levi_le h (mem_levi_of_mem_normalizer_Z h hgS hgN)

theorem miyamotoA1_inf_levi (hf : 2 ≤ f) :
    miyamotoA1 h ⊓ (miyamotoI1 h ⊔ miyamotoN1 h) = ⊥ := by
  refine (eq_bot_iff_forall _).2 fun x ⟨hxA, hxL⟩ => ?_
  have hxC := ((miyamotoI1_sup_N1_le h) hxL).2
  have : x ∈ miyamotoA1 h ⊓ miyamotoRootA h :=
    ⟨hxA, by rw [← miyamotoP_inf_centralizer_I1 h hf]; exact ⟨miyamotoA1_le_P h hxA, hxC⟩⟩
  rwa [miyamotoA1_inf_rootA, mem_bot] at this

theorem miyamotoA2_inf_levi (hf : 2 ≤ f) :
    miyamotoA2 h ⊓ (miyamotoI2 h ⊔ miyamotoN2 h) = ⊥ := by
  refine (eq_bot_iff_forall _).2 fun x ⟨hxA, hxL⟩ => ?_
  have hxC := ((miyamotoI2_sup_N2_le h) hxL).2
  have : x ∈ miyamotoA2 h ⊓ miyamotoRootB h :=
    ⟨hxA, by rw [← miyamotoP_inf_centralizer_I2 h hf]; exact ⟨miyamotoA2_le_P h hxA, hxC⟩⟩
  rwa [miyamotoA2_inf_rootB, mem_bot] at this

end Normalizers

section CentralizerZ

@[expose] def miyamotoI2pow : Subgroup (GL (Fin 4) K) :=
  ((miyamotoI2Hom h).comp (powMonoidHom (2 ^ f - 1))).range

theorem mem_miyamotoI2pow_iff {g : GL (Fin 4) K} :
    g ∈ miyamotoI2pow h ↔ ∃ x ∈ miyamotoI2 h, g = x ^ (2 ^ f - 1) := by
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨_, ⟨b, rfl⟩, by simp [map_pow]⟩
  · rintro ⟨_, ⟨b, rfl⟩, rfl⟩
    exact ⟨b, by simp [map_pow]⟩

theorem miyamotoI2pow_le_I2 : miyamotoI2pow h ≤ miyamotoI2 h := by
  rintro _ ⟨b, rfl⟩
  exact ⟨_, rfl⟩

theorem eq_pow_pow_sub_one_of_norm {u : Kˣ} (hu : (u : K) * h.bar u = 1) :
    (u ^ 2 ^ (f - 1)) ^ (2 ^ f - 1) = u := by
  have hf1 := h.one_le
  obtain ⟨k, hk⟩ : ∃ k, f = k + 1 := ⟨f - 1, by omega⟩
  subst hk
  simp only [Nat.add_sub_cancel]
  have hq : u ^ (2 ^ (k + 1) + 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, pow_succ, ← h.bar_apply, mul_comm]
    exact hu
  obtain ⟨j, hj⟩ : ∃ j, 2 ^ k = j + 1 := ⟨2 ^ k - 1, by have := Nat.one_le_two_pow (n := k); omega⟩
  have e : 2 ^ k * (2 ^ (k + 1) - 1) = (2 ^ (k + 1) + 1) * j + 1 := by
    rw [pow_succ, hj]
    zify [show 1 ≤ (j + 1) * 2 by omega]
    ring
  rw [← pow_mul, e, pow_succ, pow_mul, hq, one_pow, one_mul]

theorem miyamotoI2Hom_mem_I2pow_iff [CharP K 2] (a : Kˣ) :
    miyamotoI2Hom h a ∈ miyamotoI2pow h ↔ (a : K) * h.bar a = 1 := by
  constructor
  · rintro ⟨b, e⟩
    have e00 := congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K) 0 0) e
    simp only [MonoidHom.coe_comp, Function.comp_apply, powMonoidHom_apply, miyamotoI2Hom_eq,
      coe_miyamotoIHom] at e00
    simp only [diagonal_apply_eq, Matrix.cons_val_zero, Units.val_pow_eq_pow_val] at e00
    have hab : ((b : K) ^ (2 ^ f - 1)) = a := by
      have e' : (((b : K) ^ (2 ^ f - 1)) - a) ^ 2 = 0 := by
        linear_combination e00 + ((a : K) ^ 2 - (b : K) ^ (2 ^ f - 1) * a) *
          CharTwo.two_eq_zero (R := K)
      exact sub_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 e')
    rw [← hab]
    exact pow_sub_one_mul_bar h b.ne_zero
  · intro hu
    refine ⟨a ^ 2 ^ (f - 1), ?_⟩
    simp only [MonoidHom.coe_comp, Function.comp_apply, powMonoidHom_apply]
    rw [eq_pow_pow_sub_one_of_norm h hu]

theorem miyamotoN2_commute_Z {n z : GL (Fin 4) K} (hn : n ∈ miyamotoN2 h)
    (hz : z ∈ miyamotoZ h) : n * z = z * n := by
  obtain ⟨m, -, -, hm⟩ := (mem_miyamotoN2 h).1 hn
  obtain ⟨d, -, rfl⟩ := hz
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hm, coe_miyamotoXGL]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [miyamotoN2Mat, miyamotoX, Matrix.mul_apply, Fin.sum_univ_four]

variable [CharP K 2]

theorem miyamotoA2_sup_I2pow_N2_le :
    miyamotoA2 h ⊔ (miyamotoI2pow h ⊔ miyamotoN2 h) ≤
      gramSU h (miyamotoJ4 K) ⊓ centralizer (miyamotoZ h : Set (GL (Fin 4) K)) := by
  refine sup_le (le_inf (miyamotoUnipotent_le_SU h false true) fun x hx => ?_)
    (sup_le (le_inf ((miyamotoI2pow_le_I2 h).trans (miyamotoI2_le_SU h)) ?_)
      (le_inf (miyamotoN2_le_gramSU h) fun n hn => mem_centralizer_iff.2 fun z hz =>
        (miyamotoN2_commute_Z h hn hz).symm))
  · rw [← centerIn_miyamotoA2 h]
    exact mem_centralizer_iff.2 fun z hz => (mem_centralizer_iff.1 hz.2 x hx).symm
  · rintro _ ⟨b, rfl⟩
    refine mem_centralizer_iff.2 fun z hz => ?_
    obtain ⟨d, -, rfl⟩ := hz
    simp only [MonoidHom.coe_comp, Function.comp_apply, powMonoidHom_apply]
    refine mem_centralizer_singleton_iff.1 ((mem_centralizer_singleton_iff_conj).2 ?_)
    rw [miyamotoI2Hom_conj]
    have hN : ((b ^ (2 ^ f - 1) : Kˣ) : K) ^ 2 * h.bar (((b ^ (2 ^ f - 1) : Kˣ) : K) ^ 2) = 1 := by
      rw [map_pow, ← mul_pow, Units.val_pow_eq_pow_val, pow_sub_one_mul_bar h b.ne_zero, one_pow]
    rw [hN, one_mul]
    simp

theorem centralizer_miyamotoZ :
    gramSU h (miyamotoJ4 K) ⊓ centralizer (miyamotoZ h : Set (GL (Fin 4) K)) =
      miyamotoA2 h ⊔ (miyamotoI2pow h ⊔ miyamotoN2 h) := by
  refine le_antisymm (fun g hg => ?_) (miyamotoA2_sup_I2pow_N2_le h)
  obtain ⟨hgS, hgC⟩ := mem_inf.1 hg
  obtain ⟨h03, h13, h23⟩ := shapeTwo_of_mem_normalizer_Z h (centralizer_le_normalizer _ hgC)
  obtain ⟨a, ha, i, hi, n, hn, rfl⟩ := exists_mul_of_shapeTwo h hgS h03 h13 h23
  have hle := miyamotoA2_sup_I2pow_N2_le h
  have haC : a ∈ centralizer (miyamotoZ h : Set (GL (Fin 4) K)) := (hle (mem_sup_left ha)).2
  have hnC : n ∈ centralizer (miyamotoZ h : Set (GL (Fin 4) K)) :=
    (hle (mem_sup_right (mem_sup_right hn))).2
  have hiC : i ∈ centralizer (miyamotoZ h : Set (GL (Fin 4) K)) := by
    have := mul_mem (mul_mem (inv_mem haC) hgC) (inv_mem hnC)
    rwa [show a⁻¹ * (a * i * n) * n⁻¹ = i by group] at this
  obtain ⟨a₀, rfl⟩ := hi
  have hz : miyamotoXGL h 0 0 0 1 ∈ miyamotoZ h := ⟨1, map_one _, rfl⟩
  have e := (mem_centralizer_singleton_iff_conj).1
    (mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hiC _ hz))
  rw [miyamotoI2Hom_conj, miyamotoXGL_inj] at e
  have hN : ((a₀ : K) * h.bar (a₀ : K)) ^ 2 = 1 := by
    rw [mul_pow, ← map_pow]
    simpa using e.2.2.2
  have hi' : miyamotoI2Hom h a₀ ∈ miyamotoI2pow h :=
    (miyamotoI2Hom_mem_I2pow_iff h a₀).2 (eq_one_of_sq_eq_one hN)
  exact mul_mem (mul_mem (mem_sup_left ha) (mem_sup_right (mem_sup_left hi')))
    (mem_sup_right (mem_sup_right hn))

end CentralizerZ


section NormalizerP

variable [CharP K 2]

theorem normalizer_P_le_normalizer_A1 :
    normalizer (miyamotoP h : Set (GL (Fin 4) K)) ≤
      normalizer (miyamotoA1 h : Set (GL (Fin 4) K)) := by
  have := h.finite
  have hA := isElementaryAbelian_miyamotoA1 h
  intro g hg
  set B := (miyamotoA1 h).map (MulAut.conj g).toMonoidHom with hBdef
  have hBP : B ≤ miyamotoP h := by
    rintro _ ⟨x, hx, rfl⟩
    exact (mem_normalizer_iff.1 hg x).1 (miyamotoA1_le_P h hx)
  have hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have e : x * y = y * x := by
      simpa using congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : miyamotoA1 h) ⟨y, hy⟩)
    rw [← map_mul, ← map_mul, e]
  have hcard : Nat.card B = (2 ^ f) ^ 4 := by
    rw [hBdef, card_map_of_injective (MulAut.conj g).injective, card_miyamotoA1]
  have hB : B = miyamotoA1 h := (card_le_and_eq_A1_of_commute h hBP hcomm).2 hcard.ge
  refine mem_normalizer_iff.2 fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · rw [← hB]
    exact ⟨x, hx, rfl⟩
  · rw [← hB] at hx
    obtain ⟨y, hy, e⟩ := hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at e
    rw [mul_left_inj, mul_right_inj] at e
    exact e ▸ hy

omit [CharP K 2] in
theorem row_zero_of_col_three {g : GL (Fin 4) K} (hg : g ∈ gramSU h (miyamotoJ4 K))
    (h03 : (g : Matrix (Fin 4) (Fin 4) K) 0 3 = 0) (h13 : (g : Matrix (Fin 4) (Fin 4) K) 1 3 = 0)
    (h23 : (g : Matrix (Fin 4) (Fin 4) K) 2 3 = 0) :
    (g : Matrix (Fin 4) (Fin 4) K) 0 1 = 0 ∧ (g : Matrix (Fin 4) (Fin 4) K) 0 2 = 0 := by
  have hU := (mem_gramSU.1 hg).1
  have e03 := unitary_entry h hU 0 3
  have e13 := unitary_entry h hU 1 3
  have e23 := unitary_entry h hU 2 3
  simp [miyamotoJ4, h03, h13, h23] at e03 e13 e23
  have h33 : (g : Matrix (Fin 4) (Fin 4) K) 3 3 ≠ 0 := right_ne_zero_of_mul_eq_one e03
  exact ⟨by simpa [h33] using e13, by simpa [h33] using e23⟩

theorem normalizer_miyamotoP :
    gramSU h (miyamotoJ4 K) ⊓ normalizer (miyamotoP h : Set (GL (Fin 4) K)) =
      miyamotoP h ⊔ miyamotoI h := by
  refine le_antisymm (fun g hg => ?_) (sup_le (le_inf (miyamotoUnipotent_le_SU h false false)
    le_normalizer) (le_inf (miyamotoI_le_gramSU h)
      (miyamotoI_le_normalizer_unipotent h false false)))
  obtain ⟨hgS, hgN⟩ := mem_inf.1 hg
  obtain ⟨h02, h03, h12, h13⟩ :=
    shapeOne_of_mem_normalizer_A1 h (normalizer_P_le_normalizer_A1 h hgN)
  have hgZ : g ∈ normalizer (miyamotoZ h : Set (GL (Fin 4) K)) := by
    rw [← centerIn_miyamotoP h]
    exact normalizer_le_normalizer_centerIn _ hgN
  obtain ⟨-, -, h23⟩ := shapeTwo_of_mem_normalizer_Z h hgZ
  obtain ⟨h01, -⟩ := row_zero_of_col_three h hgS h03 h13 h23
  obtain ⟨p, hp, d, hd, rfl⟩ := exists_mul_of_lower h hgS h01 h02 h03 h12 h13 h23
  exact mul_mem (mem_sup_left hp) (mem_sup_right hd)

omit [CharP K 2] in
theorem miyamotoP_inf_I : miyamotoP h ⊓ miyamotoI h = ⊥ := by
  refine (eq_bot_iff_forall _).2 fun x ⟨hxP, hxI⟩ => ?_
  obtain ⟨a, b, c, d, -, -, rfl⟩ := (mem_P h).1 hxP
  obtain ⟨p, -, e⟩ := hxI
  have e' := congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K)) e
  simp only [coe_miyamotoIHom, coe_miyamotoXGL] at e'
  have e10 := congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M 1 0) e'
  have e21 := congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M 2 1) e'
  have e20 := congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M 2 0) e'
  have e30 := congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M 3 0) e'
  simp [miyamotoX] at e10 e21 e20 e30
  rw [← e10, ← e21, ← e20, ← e30, miyamotoXGL_zero]

end NormalizerP

end CFSG.LocalAnalysis.EvenBN.U4
