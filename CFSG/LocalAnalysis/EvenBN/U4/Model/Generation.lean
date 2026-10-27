module

public import CFSG.LocalAnalysis.EvenBN.U4.Model.ParabolicG

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

section SL2

variable {k : Type*} [Field k]

@[expose] def upperSL2 (s : k) : SpecialLinearGroup (Fin 2) k :=
  ⟨!![1, s; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def lowerSL2 (b : k) : SpecialLinearGroup (Fin 2) k :=
  ⟨!![1, 0; b, 1], by simp [Matrix.det_fin_two]⟩

theorem coe_upperSL2 (s : k) :
    ((upperSL2 s : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = !![1, s; 0, 1] :=
  rfl

theorem coe_lowerSL2 (b : k) :
    ((lowerSL2 b : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = !![1, 0; b, 1] :=
  rfl

theorem mem_of_lowerSL2_upperSL2 {G : Type*} [Group G] (φ : SpecialLinearGroup (Fin 2) k →* G)
    {H : Subgroup G} (hl : ∀ b, φ (lowerSL2 b) ∈ H) (hu : ∀ s, φ (upperSL2 s) ∈ H)
    (m : SpecialLinearGroup (Fin 2) k) : φ m ∈ H := by
  have key : ∀ m : SpecialLinearGroup (Fin 2) k, (m : Matrix (Fin 2) (Fin 2) k) 1 0 ≠ 0 →
      φ m ∈ H := by
    intro m hm
    have hdet := m.2
    rw [Matrix.det_fin_two] at hdet
    have e : m = upperSL2 (((m : Matrix (Fin 2) (Fin 2) k) 0 0 - 1) /
        (m : Matrix (Fin 2) (Fin 2) k) 1 0) * lowerSL2 ((m : Matrix (Fin 2) (Fin 2) k) 1 0) *
        upperSL2 (((m : Matrix (Fin 2) (Fin 2) k) 1 1 - 1) /
          (m : Matrix (Fin 2) (Fin 2) k) 1 0) := by
      ext i j
      simp only [Matrix.SpecialLinearGroup.coe_mul, coe_upperSL2, coe_lowerSL2]
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;>
        first | ring1 | linear_combination hdet | linear_combination -hdet
    rw [e, map_mul, map_mul]
    exact mul_mem (mul_mem (hu _) (hl _)) (hu _)
  by_cases hm : (m : Matrix (Fin 2) (Fin 2) k) 1 0 = 0
  · have hdet := m.2
    rw [Matrix.det_fin_two, hm, mul_zero, sub_zero] at hdet
    have h00 : (m : Matrix (Fin 2) (Fin 2) k) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
    have e : m = lowerSL2 (-1) * (lowerSL2 1 * m) := by
      rw [← mul_assoc]
      ext i j
      simp only [Matrix.SpecialLinearGroup.coe_mul, coe_lowerSL2]
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [e, map_mul]
    refine mul_mem (hl _) (key _ ?_)
    simpa [Matrix.SpecialLinearGroup.coe_mul, coe_lowerSL2, Matrix.mul_apply, Fin.sum_univ_two, hm]
      using h00
  · exact key m hm

end SL2

section Roots

theorem miyamotoR1_inv : (miyamotoR1 K)⁻¹ = miyamotoR1 K :=
  inv_eq_of_mul_eq_one_right miyamotoR1_mul_self

theorem miyamotoR2_inv : (miyamotoR2 K)⁻¹ = miyamotoR2 K :=
  inv_eq_of_mul_eq_one_right miyamotoR2_mul_self

theorem coe_miyamotoR1 : ((miyamotoR1 K : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
    !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0] :=
  rfl

theorem coe_miyamotoR2 : ((miyamotoR2 K : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
    !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1] :=
  rfl

theorem mem_map_conj_inv_iff {G : Type*} [Group G] {A : Subgroup G} {g y : G} :
    y ∈ A.map (MulAut.conj g⁻¹).toMonoidHom ↔ g * y * g⁻¹ ∈ A := by
  rw [mem_map_equiv, MulAut.conj_symm_apply, inv_inv]

theorem miyamotoN1Hom_lowerSL2 (a : K) :
    miyamotoN1Hom h (lowerSL2 a) = miyamotoXGL h a 0 0 0 := by
  apply Units.ext
  rw [coe_miyamotoN1Hom, coe_lowerSL2, coe_miyamotoXGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [miyamotoN1Mat, miyamotoX]

theorem miyamotoN2Hom_lowerSL2 (b : h.fixedField) :
    miyamotoN2Hom h (lowerSL2 b) = miyamotoXGL h 0 b 0 0 := by
  apply Units.ext
  rw [coe_miyamotoN2Hom, coe_lowerSL2, coe_miyamotoXGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [miyamotoN2Mat, miyamotoX]

theorem coe_miyamotoN1Hom_upperSL2 (a : K) :
    ((miyamotoN1Hom h (upperSL2 a) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      !![1, a, 0, 0; 0, 1, 0, 0; 0, 0, 1, h.bar a; 0, 0, 0, 1] := by
  rw [coe_miyamotoN1Hom, coe_upperSL2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [miyamotoN1Mat]

theorem coe_miyamotoN2Hom_upperSL2 (s : h.fixedField) :
    ((miyamotoN2Hom h (upperSL2 s) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      !![1, 0, 0, 0; 0, 1, (s : K), 0; 0, 0, 1, 0; 0, 0, 0, 1] := by
  rw [coe_miyamotoN2Hom, coe_upperSL2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [miyamotoN2Mat]

theorem miyamotoRootB_le_N2 : miyamotoRootB h ≤ miyamotoN2 h := by
  rintro _ ⟨b, hb, rfl⟩
  rw [show b = ((⟨b, hb⟩ : h.fixedField) : K) from rfl, ← miyamotoN2Hom_lowerSL2]
  exact ⟨_, rfl⟩

theorem miyamotoRootA_le_N1 : miyamotoRootA h ≤ miyamotoN1 h := by
  rintro _ ⟨a, rfl⟩
  rw [← miyamotoN1Hom_lowerSL2]
  exact ⟨_, rfl⟩

variable [CharP K 2]

theorem mem_miyamotoUpper2_iff {y : GL (Fin 4) K} :
    y ∈ (miyamotoA1 h).map (MulAut.conj (miyamotoR2 K)⁻¹).toMonoidHom ⊓
        (miyamotoA1 h).map
          (MulAut.conj (miyamotoR2 K * miyamotoR1 K * miyamotoR2 K)⁻¹).toMonoidHom ↔
      ∃ s : h.fixedField, y = miyamotoN2Hom h (upperSL2 s) := by
  have hw : (miyamotoR2 K * miyamotoR1 K * miyamotoR2 K)⁻¹ =
      miyamotoR2 K * miyamotoR1 K * miyamotoR2 K := by
    rw [_root_.mul_inv_rev, _root_.mul_inv_rev, miyamotoR1_inv, miyamotoR2_inv, mul_assoc]
  rw [mem_inf, mem_map_conj_inv_iff, mem_map_conj_inv_iff, hw, miyamotoR2_inv]
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨b, c, d, hb, hd, e1⟩ := (mem_A1 h).1 h1
    have hy : y = miyamotoR2 K * miyamotoXGL h 0 b c d * miyamotoR2 K := by
      rw [← e1]
      calc y = (miyamotoR2 K * miyamotoR2 K) * y * (miyamotoR2 K * miyamotoR2 K) := by
            rw [miyamotoR2_mul_self, one_mul, mul_one]
        _ = _ := by group
    rw [hy] at h2
    obtain ⟨b', c', d', -, -, e2⟩ := (mem_A1 h).1 h2
    have e10 := congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K) 1 0) e2
    have e12 := congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K) 1 2) e2
    simp [Units.val_mul, coe_miyamotoR1, coe_miyamotoR2, miyamotoX, Matrix.mul_apply,
      Fin.sum_univ_four] at e10 e12
    subst e10 e12
    refine ⟨⟨b, hb⟩, ?_⟩
    rw [hy]
    apply Units.ext
    rw [coe_miyamotoN2Hom_upperSL2]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Units.val_mul, coe_miyamotoR2, miyamotoX, Matrix.mul_apply, Fin.sum_univ_four]
  · rintro ⟨s, rfl⟩
    refine ⟨(mem_A1 h).2 ⟨s, 0, 0, s.2, map_zero _, ?_⟩,
      (mem_A1 h).2 ⟨0, 0, s, map_zero _, s.2, ?_⟩⟩
    · apply Units.ext
      rw [coe_miyamotoXGL]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Units.val_mul, coe_miyamotoR2,
        coe_miyamotoN2Hom_upperSL2, miyamotoX, Matrix.mul_apply, Fin.sum_univ_four]
    · apply Units.ext
      rw [coe_miyamotoXGL]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Units.val_mul, coe_miyamotoR1, coe_miyamotoR2,
        coe_miyamotoN2Hom_upperSL2, miyamotoX, Matrix.mul_apply, Fin.sum_univ_four]

theorem mem_miyamotoUpper1_iff {y : GL (Fin 4) K} :
    y ∈ (miyamotoA1 h).map (MulAut.conj (miyamotoR2 K * miyamotoR1 K)⁻¹).toMonoidHom ⊓
        (miyamotoA2 h).map (MulAut.conj (miyamotoR1 K)⁻¹).toMonoidHom ↔
      ∃ a d : K, h.bar d = d ∧ y = miyamotoN1Hom h (upperSL2 a) * miyamotoXGL h 0 d 0 0 := by
  have hw : (miyamotoR2 K * miyamotoR1 K)⁻¹ = miyamotoR1 K * miyamotoR2 K := by
    rw [_root_.mul_inv_rev, miyamotoR1_inv, miyamotoR2_inv]
  rw [mem_inf, mem_map_conj_inv_iff, mem_map_conj_inv_iff, hw, miyamotoR1_inv]
  have key : ∀ a d : K, miyamotoR1 K * miyamotoXGL h a 0 0 d * miyamotoR1 K =
      miyamotoN1Hom h (upperSL2 a) * miyamotoXGL h 0 d 0 0 := by
    intro a d
    apply Units.ext
    simp only [Units.val_mul]
    rw [coe_miyamotoN1Hom_upperSL2]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coe_miyamotoR1, miyamotoX, Matrix.mul_apply, Fin.sum_univ_four]
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨a, c, d, hd, e2⟩ := (mem_A2 h).1 h2
    have hy : y = miyamotoR1 K * miyamotoXGL h a 0 c d * miyamotoR1 K := by
      rw [← e2]
      calc y = (miyamotoR1 K * miyamotoR1 K) * y * (miyamotoR1 K * miyamotoR1 K) := by
            rw [miyamotoR1_mul_self, one_mul, mul_one]
        _ = _ := by group
    rw [hy] at h1
    obtain ⟨b', c', d', -, -, e1⟩ := (mem_A1 h).1 h1
    have e10 := congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K) 1 0) e1
    simp [Units.val_mul, coe_miyamotoR1, coe_miyamotoR2, miyamotoX, Matrix.mul_apply,
      Fin.sum_univ_four] at e10
    subst e10
    refine ⟨a, d, (add_bar_eq_zero_iff h).1 (by simpa using hd), ?_⟩
    rw [hy, key]
  · rintro ⟨a, d, hd, rfl⟩
    rw [← key]
    have e : miyamotoR1 K * (miyamotoR1 K * miyamotoXGL h a 0 0 d * miyamotoR1 K) *
        miyamotoR1 K = miyamotoXGL h a 0 0 d := by
      calc _ = (miyamotoR1 K * miyamotoR1 K) * miyamotoXGL h a 0 0 d *
            (miyamotoR1 K * miyamotoR1 K) := by group
        _ = _ := by rw [miyamotoR1_mul_self, one_mul, mul_one]
    refine ⟨(mem_A1 h).2 ⟨0, a, d, map_zero _, hd, ?_⟩, ?_⟩
    · apply Units.ext
      rw [coe_miyamotoXGL]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Units.val_mul, coe_miyamotoR1, coe_miyamotoR2, miyamotoX, Matrix.mul_apply,
          Fin.sum_univ_four]
    · rw [e]
      exact (miyamotoXGL_mem_A2 h).2 ⟨rfl, by simp [hd, CharTwo.add_self_eq_zero]⟩

end Roots

section LeviGeneration

variable [CharP K 2]

theorem miyamotoA2_sup_N2_eq :
    miyamotoA2 h ⊔ miyamotoN2 h = miyamotoP h ⊔
      ((miyamotoA1 h).map (MulAut.conj (miyamotoR2 K)⁻¹).toMonoidHom ⊓
        (miyamotoA1 h).map
          (MulAut.conj (miyamotoR2 K * miyamotoR1 K * miyamotoR2 K)⁻¹).toMonoidHom) := by
  apply le_antisymm
  · refine sup_le ((miyamotoA2_le_P h).trans le_sup_left) ?_
    rintro _ ⟨m, rfl⟩
    refine mem_of_lowerSL2_upperSL2 (miyamotoN2Hom h) (fun b => mem_sup_left ?_)
      (fun s => mem_sup_right ((mem_miyamotoUpper2_iff h).2 ⟨s, rfl⟩)) m
    rw [miyamotoN2Hom_lowerSL2]
    exact (miyamotoRootB_le_A1 h).trans (miyamotoA1_le_P h) ⟨b, b.2, rfl⟩
  · refine sup_le (fun x hx => ?_) fun y hy => ?_
    · rw [← SetLike.mem_coe, ← miyamotoA2_mul_rootB h] at hx
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      exact mul_mem (mem_sup_left ha) (mem_sup_right (miyamotoRootB_le_N2 h hb))
    · obtain ⟨s, rfl⟩ := (mem_miyamotoUpper2_iff h).1 hy
      exact mem_sup_right ⟨_, rfl⟩

theorem miyamotoA1_sup_N1_eq :
    miyamotoA1 h ⊔ miyamotoN1 h = miyamotoP h ⊔
      ((miyamotoA1 h).map (MulAut.conj (miyamotoR2 K * miyamotoR1 K)⁻¹).toMonoidHom ⊓
        (miyamotoA2 h).map (MulAut.conj (miyamotoR1 K)⁻¹).toMonoidHom) := by
  apply le_antisymm
  · refine sup_le ((miyamotoA1_le_P h).trans le_sup_left) ?_
    rintro _ ⟨m, rfl⟩
    refine mem_of_lowerSL2_upperSL2 (miyamotoN1Hom h) (fun a => mem_sup_left ?_)
      (fun a => mem_sup_right ((mem_miyamotoUpper1_iff h).2 ⟨a, 0, map_zero _, ?_⟩)) m
    · rw [miyamotoN1Hom_lowerSL2]
      exact (miyamotoRootA_le_A2 h).trans (miyamotoA2_le_P h) ⟨a, rfl⟩
    · rw [miyamotoXGL_zero, mul_one]
  · refine sup_le (fun x hx => ?_) fun y hy => ?_
    · rw [← SetLike.mem_coe, ← miyamotoA1_mul_rootA h] at hx
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      exact mul_mem (mem_sup_left ha) (mem_sup_right (miyamotoRootA_le_N1 h hb))
    · obtain ⟨a, d, hd, rfl⟩ := (mem_miyamotoUpper1_iff h).1 hy
      exact mul_mem (mem_sup_right ⟨_, rfl⟩)
        (mem_sup_left ((miyamotoXGL_mem_A1 h).2 ⟨rfl, hd, map_zero _⟩))

end LeviGeneration

section Generation

theorem miyamotoI_le_N1_sup_N2 : miyamotoI h ≤ miyamotoN1 h ⊔ miyamotoN2 h := by
  rintro _ ⟨p, hp, rfl⟩
  have hF := (miyamotoIParam_eq_one_iff h p).1 hp
  have h1 : (p.1 : K) ≠ 0 := p.1.ne_zero
  have h2 : (p.2 : K) ≠ 0 := p.2.ne_zero
  have hb1 : h.bar (p.1 : K) ≠ 0 := by simp
  have hb2 : h.bar (p.2 : K) ≠ 0 := by simp
  obtain ⟨n₁, hn₁, e₁⟩ := exists_mem_miyamotoN1_coe_eq h (m := !![(p.1 : K), 0; 0, (p.1 : K)⁻¹])
    (by simp [Matrix.det_fin_two, h1])
  have hFi : h.bar (((p.1 : K) * p.2)⁻¹) = ((p.1 : K) * p.2)⁻¹ := by rw [map_inv₀, hF]
  obtain ⟨n₂, hn₂, e₂⟩ := exists_mem_miyamotoN2_coe_eq h
    (m := !![(p.1 : K) * p.2, 0; 0, ((p.1 : K) * p.2)⁻¹])
    (by simp only [Matrix.det_fin_two_of]; field_simp; ring)
    (fun i j => by
      fin_cases i <;> fin_cases j
      · exact hF
      · exact map_zero _
      · exact map_zero _
      · exact hFi)
  have e : miyamotoIHom h p = n₁ * n₂ := by
    apply Units.ext
    rw [Units.val_mul, e₁, e₂, coe_miyamotoIHom]
    ext i j
    rw [map_mul] at hF
    fin_cases i <;> fin_cases j <;>
      simp [miyamotoN1Mat, miyamotoN2Mat, Matrix.mul_apply, Fin.sum_univ_four]
    all_goals field_simp
    all_goals first | linear_combination hF | linear_combination -hF
  rw [e]
  exact mul_mem (mem_sup_left hn₁) (mem_sup_right hn₂)

variable [CharP K 2]

theorem miyamoto_generation :
    (miyamotoA1 h ⊔ miyamotoN1 h) ⊔ (miyamotoA2 h ⊔ miyamotoN2 h) = gramSU h (miyamotoJ4 K) := by
  apply le_antisymm
  · exact sup_le (sup_le (miyamotoUnipotent_le_SU h true false) (miyamotoN1_le_gramSU h))
      (sup_le (miyamotoUnipotent_le_SU h false true) (miyamotoN2_le_gramSU h))
  have hc2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hbb := h.bar_bar
  set H := (miyamotoA1 h ⊔ miyamotoN1 h) ⊔ (miyamotoA2 h ⊔ miyamotoN2 h) with hH
  have hA1 : miyamotoA1 h ≤ H := le_sup_left.trans le_sup_left
  have hN1 : miyamotoN1 h ≤ H := le_sup_right.trans le_sup_left
  have hA2 : miyamotoA2 h ≤ H := le_sup_left.trans le_sup_right
  have hN2 : miyamotoN2 h ≤ H := le_sup_right.trans le_sup_right
  have hI : miyamotoI h ≤ H := (miyamotoI_le_N1_sup_N2 h).trans (sup_le hN1 hN2)
  have hr1 : miyamotoR1 K ∈ H := hN1 (miyamotoR1_mem_N1 h)
  have hr2 : miyamotoR2 K ∈ H := hN2 (miyamotoR2_mem_N2 h)
  have hSU : ∀ {x : GL (Fin 4) K}, x ∈ H → x ∈ gramSU h (miyamotoJ4 K) := fun hx =>
    (sup_le (sup_le (miyamotoUnipotent_le_SU h true false) (miyamotoN1_le_gramSU h))
      (sup_le (miyamotoUnipotent_le_SU h false true) (miyamotoN2_le_gramSU h))) hx
  have hstab : ∀ g ∈ gramSU h (miyamotoJ4 K), (g : Matrix (Fin 4) (Fin 4) K) 0 3 = 0 →
      (g : Matrix (Fin 4) (Fin 4) K) 1 3 = 0 → (g : Matrix (Fin 4) (Fin 4) K) 2 3 = 0 →
        g ∈ H := by
    intro g hg h03 h13 h23
    obtain ⟨a, ha, i, hi, n, hn, rfl⟩ := exists_mul_of_shapeTwo h hg h03 h13 h23
    exact mul_mem (mul_mem (hA2 ha) (hI (miyamotoI2_le_I h hi))) (hN2 hn)
  have hdecomp : ∀ {g p w : GL (Fin 4) K}, g ∈ gramSU h (miyamotoJ4 K) → p ∈ H → w ∈ H →
      (((w⁻¹ * p⁻¹ * g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 3 = 0) →
      (((w⁻¹ * p⁻¹ * g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 1 3 = 0) →
      (((w⁻¹ * p⁻¹ * g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 2 3 = 0) → g ∈ H := by
    intro g p w hg hp hw e0 e1 e2
    have hg' := hstab _ (mul_mem (mul_mem (inv_mem (hSU hw)) (inv_mem (hSU hp))) hg) e0 e1 e2
    have : g = p * w * (w⁻¹ * p⁻¹ * g) := by group
    rw [this]
    exact mul_mem (mul_mem hp hw) hg'
  intro g hg
  have e33 := unitary_entry h (mem_gramSU.1 hg).1 3 3
  simp [miyamotoJ4] at e33
  by_cases h0 : (g : Matrix (Fin 4) (Fin 4) K) 0 3 = 0
  · by_cases h1 : (g : Matrix (Fin 4) (Fin 4) K) 1 3 = 0
    · by_cases h2 : (g : Matrix (Fin 4) (Fin 4) K) 2 3 = 0
      · exact hstab g hg h0 h1 h2
      · have hp : miyamotoXGL h (h.bar ((g : Matrix (Fin 4) (Fin 4) K) 3 3 /
            (g : Matrix (Fin 4) (Fin 4) K) 2 3)) 0 0 0 ∈ H :=
          hA2 (miyamotoRootA_le_A2 h ⟨_, rfl⟩)
        refine hdecomp hg hp hr1 ?_ ?_ ?_ <;>
          simp [miyamotoR1_inv, miyamotoXGL_inv h (map_zero h.bar), Units.val_mul, coe_miyamotoR1,
            miyamotoX, Matrix.mul_apply, Fin.sum_univ_four, h0, h1, hbb]
        rw [div_mul_cancel₀ _ h2, CharTwo.add_self_eq_zero]
    · have hb1 : h.bar ((g : Matrix (Fin 4) (Fin 4) K) 1 3) ≠ 0 := by simpa using h1
      have hb : h.bar ((g : Matrix (Fin 4) (Fin 4) K) 2 3 / (g : Matrix (Fin 4) (Fin 4) K) 1 3) =
          (g : Matrix (Fin 4) (Fin 4) K) 2 3 / (g : Matrix (Fin 4) (Fin 4) K) 1 3 := by
        rw [h0, map_zero, zero_mul, mul_zero, zero_add, add_zero] at e33
        rw [map_div₀, div_eq_div_iff hb1 h1]
        linear_combination e33 - (h.bar ((g : Matrix (Fin 4) (Fin 4) K) 1 3) *
          (g : Matrix (Fin 4) (Fin 4) K) 2 3) * hc2
      have hp : miyamotoXGL h 0 ((g : Matrix (Fin 4) (Fin 4) K) 2 3 /
          (g : Matrix (Fin 4) (Fin 4) K) 1 3) (h.bar ((g : Matrix (Fin 4) (Fin 4) K) 3 3 /
            (g : Matrix (Fin 4) (Fin 4) K) 1 3)) 0 ∈ H :=
        hA1 ((miyamotoXGL_mem_A1 h).2 ⟨rfl, hb, map_zero _⟩)
      refine hdecomp hg hp (mul_mem hr2 hr1) ?_ ?_ ?_ <;>
        simp [_root_.mul_inv_rev, miyamotoR1_inv, miyamotoR2_inv, miyamotoXGL_inv h hb,
          Units.val_mul, coe_miyamotoR1, coe_miyamotoR2, miyamotoX, Matrix.mul_apply,
          Fin.sum_univ_four, h0, hbb]
      all_goals rw [div_mul_cancel₀ _ h1, CharTwo.add_self_eq_zero]
  · have hp : miyamotoXGL h ((g : Matrix (Fin 4) (Fin 4) K) 1 3 /
        (g : Matrix (Fin 4) (Fin 4) K) 0 3) 0
        ((g : Matrix (Fin 4) (Fin 4) K) 2 3 / (g : Matrix (Fin 4) (Fin 4) K) 0 3)
        ((g : Matrix (Fin 4) (Fin 4) K) 3 3 / (g : Matrix (Fin 4) (Fin 4) K) 0 3) ∈ H := by
      refine hA2 ((miyamotoXGL_mem_A2 h).2 ⟨rfl, ?_⟩)
      have hb0 : h.bar ((g : Matrix (Fin 4) (Fin 4) K) 0 3) ≠ 0 := by simpa using h0
      simp only [map_div₀]
      field_simp
      linear_combination e33
    refine hdecomp hg hp (mul_mem (mul_mem hr1 hr2) hr1) ?_ ?_ ?_ <;>
      simp [_root_.mul_inv_rev, miyamotoR1_inv, miyamotoR2_inv, miyamotoXGL_inv h (map_zero h.bar),
        Units.val_mul, coe_miyamotoR1, coe_miyamotoR2, miyamotoX, Matrix.mul_apply,
        Fin.sum_univ_four]
    all_goals first
      | rw [div_mul_cancel₀ _ h0, CharTwo.add_self_eq_zero]
      | (have hb0 : h.bar ((g : Matrix (Fin 4) (Fin 4) K) 0 3) ≠ 0 := by simpa using h0
         field_simp
         linear_combination ((g : Matrix (Fin 4) (Fin 4) K) 3 3 *
           h.bar ((g : Matrix (Fin 4) (Fin 4) K) 0 3) + (g : Matrix (Fin 4) (Fin 4) K) 1 3 *
           h.bar ((g : Matrix (Fin 4) (Fin 4) K) 2 3) + h.bar ((g : Matrix (Fin 4) (Fin 4) K) 1 3) *
           (g : Matrix (Fin 4) (Fin 4) K) 2 3) * hc2)

end Generation

section Pull

variable {G : Type} [Group G] (L : Subgroup G) (η : L ≃* gramSU h (miyamotoJ4 K))

@[expose] def miyamotoR1G : G := ((η.symm ⟨miyamotoR1 K, miyamotoR1_mem_gramSU h⟩ : L) : G)

@[expose] def miyamotoR2G : G :=
  ((η.symm ⟨miyamotoR2 K, by have := h.charP; exact miyamotoR2_mem_gramSU h⟩ : L) : G)

theorem miyamotoPull_map_conj (M : Subgroup (GL (Fin 4) K)) (g : gramSU h (miyamotoJ4 K)) :
    miyamotoPull h L η (M.map (MulAut.conj (g : GL (Fin 4) K)⁻¹).toMonoidHom) =
      (miyamotoPull h L η M).map (MulAut.conj ((η.symm g : L) : G)⁻¹).toMonoidHom := by
  ext x
  rw [mem_map_conj_inv_iff, mem_miyamotoPull]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_map_conj_inv_iff] at hy
    have hy' : ((g * y * g⁻¹ : gramSU h (miyamotoJ4 K)) : GL (Fin 4) K) ∈ M := by
      rw [coe_mul, coe_mul, coe_inv]
      exact hy
    rw [← coe_symm_conj]
    exact (symm_mem_miyamotoPull_iff h L η).2 hy'
  · intro hx
    have hxL : x ∈ L := by
      have hL := miyamotoPull_le h L η M hx
      have := mul_mem (mul_mem (inv_mem (η.symm g).2) hL) (η.symm g).2
      rwa [show ((η.symm g : L) : G)⁻¹ * (((η.symm g : L) : G) * x * ((η.symm g : L) : G)⁻¹) *
        ((η.symm g : L) : G) = x by group] at this
    refine ⟨η ⟨x, hxL⟩, ?_, by rw [MulEquiv.symm_apply_apply]⟩
    rw [mem_map_conj_inv_iff]
    have hx' : x = ((η.symm (η ⟨x, hxL⟩) : L) : G) := by rw [MulEquiv.symm_apply_apply]
    rw [hx', ← coe_symm_conj, symm_mem_miyamotoPull_iff] at hx
    simpa using hx

theorem coe_symm_mul (g g' : gramSU h (miyamotoJ4 K)) :
    ((η.symm (g * g') : L) : G) = ((η.symm g : L) : G) * ((η.symm g' : L) : G) := by
  rw [map_mul, coe_mul]

variable [CharP K 2]

theorem miyamoto_generationG :
    (miyamotoA1G h L η ⊔ miyamotoN1G h L η) ⊔ (miyamotoA2G h L η ⊔ miyamotoN2G h L η) = L := by
  have h1 := miyamotoUnipotent_le_SU h true false
  have h2 := miyamotoUnipotent_le_SU h false true
  rw [← miyamotoPull_sup h L η h1 (miyamotoN1_le_gramSU h),
    ← miyamotoPull_sup h L η h2 (miyamotoN2_le_gramSU h),
    ← miyamotoPull_sup h L η (sup_le h1 (miyamotoN1_le_gramSU h))
      (sup_le h2 (miyamotoN2_le_gramSU h)), miyamoto_generation h, miyamotoPull_gramSU]

theorem miyamotoA2G_sup_N2G_eq :
    miyamotoA2G h L η ⊔ miyamotoN2G h L η = miyamotoPG h L η ⊔
      ((miyamotoA1G h L η).map (MulAut.conj (miyamotoR2G h L η)⁻¹).toMonoidHom ⊓
        (miyamotoA1G h L η).map (MulAut.conj (miyamotoR2G h L η * miyamotoR1G h L η *
          miyamotoR2G h L η)⁻¹).toMonoidHom) := by
  have hA1 := miyamotoUnipotent_le_SU h true false
  set r₁ : gramSU h (miyamotoJ4 K) := ⟨miyamotoR1 K, miyamotoR1_mem_gramSU h⟩
  set r₂ : gramSU h (miyamotoJ4 K) := ⟨miyamotoR2 K, miyamotoR2_mem_gramSU h⟩
  have e1 : miyamotoPull h L η ((miyamotoA1 h).map (MulAut.conj (miyamotoR2 K)⁻¹).toMonoidHom) =
      (miyamotoA1G h L η).map (MulAut.conj (miyamotoR2G h L η)⁻¹).toMonoidHom :=
    miyamotoPull_map_conj h L η (miyamotoA1 h) r₂
  have e2 : miyamotoPull h L η ((miyamotoA1 h).map
      (MulAut.conj (miyamotoR2 K * miyamotoR1 K * miyamotoR2 K)⁻¹).toMonoidHom) =
      (miyamotoA1G h L η).map (MulAut.conj (miyamotoR2G h L η * miyamotoR1G h L η *
        miyamotoR2G h L η)⁻¹).toMonoidHom := by
    have := miyamotoPull_map_conj h L η (miyamotoA1 h) (r₂ * r₁ * r₂)
    rwa [coe_symm_mul, coe_symm_mul] at this
  have hc1 : ∀ x ∈ (miyamotoA1 h).map (MulAut.conj (miyamotoR2 K)⁻¹).toMonoidHom,
      x ∈ gramSU h (miyamotoJ4 K) := by
    rintro _ ⟨y, hy, rfl⟩
    exact mul_mem (mul_mem (inv_mem (inv_mem r₂.2)) (hA1 hy)) (inv_mem r₂.2)
  have hle : (miyamotoA1 h).map (MulAut.conj (miyamotoR2 K)⁻¹).toMonoidHom ⊓
      (miyamotoA1 h).map
        (MulAut.conj (miyamotoR2 K * miyamotoR1 K * miyamotoR2 K)⁻¹).toMonoidHom ≤
      gramSU h (miyamotoJ4 K) := fun x hx => hc1 x hx.1
  have := congrArg (miyamotoPull h L η) (miyamotoA2_sup_N2_eq h)
  rw [miyamotoPull_sup h L η (miyamotoUnipotent_le_SU h false true) (miyamotoN2_le_gramSU h),
    miyamotoPull_sup h L η (miyamotoUnipotent_le_SU h false false) hle, miyamotoPull_inf] at this
  rw [this, e1, e2]

theorem miyamotoA1G_sup_N1G_eq :
    miyamotoA1G h L η ⊔ miyamotoN1G h L η = miyamotoPG h L η ⊔
      ((miyamotoA1G h L η).map (MulAut.conj (miyamotoR2G h L η *
          miyamotoR1G h L η)⁻¹).toMonoidHom ⊓
        (miyamotoA2G h L η).map (MulAut.conj (miyamotoR1G h L η)⁻¹).toMonoidHom) := by
  have hA1 := miyamotoUnipotent_le_SU h true false
  have hA2 := miyamotoUnipotent_le_SU h false true
  set r₁ : gramSU h (miyamotoJ4 K) := ⟨miyamotoR1 K, miyamotoR1_mem_gramSU h⟩
  set r₂ : gramSU h (miyamotoJ4 K) := ⟨miyamotoR2 K, miyamotoR2_mem_gramSU h⟩
  have e1 : miyamotoPull h L η ((miyamotoA1 h).map
      (MulAut.conj (miyamotoR2 K * miyamotoR1 K)⁻¹).toMonoidHom) =
      (miyamotoA1G h L η).map (MulAut.conj (miyamotoR2G h L η *
        miyamotoR1G h L η)⁻¹).toMonoidHom := by
    have := miyamotoPull_map_conj h L η (miyamotoA1 h) (r₂ * r₁)
    rwa [coe_symm_mul] at this
  have e2 : miyamotoPull h L η ((miyamotoA2 h).map (MulAut.conj (miyamotoR1 K)⁻¹).toMonoidHom) =
      (miyamotoA2G h L η).map (MulAut.conj (miyamotoR1G h L η)⁻¹).toMonoidHom :=
    miyamotoPull_map_conj h L η (miyamotoA2 h) r₁
  have hle : (miyamotoA1 h).map (MulAut.conj (miyamotoR2 K * miyamotoR1 K)⁻¹).toMonoidHom ⊓
      (miyamotoA2 h).map (MulAut.conj (miyamotoR1 K)⁻¹).toMonoidHom ≤
      gramSU h (miyamotoJ4 K) := by
    rintro x ⟨-, ⟨y, hy, rfl⟩⟩
    exact mul_mem (mul_mem (inv_mem (inv_mem r₁.2)) (hA2 hy)) (inv_mem r₁.2)
  have := congrArg (miyamotoPull h L η) (miyamotoA1_sup_N1_eq h)
  rw [miyamotoPull_sup h L η hA1 (miyamotoN1_le_gramSU h),
    miyamotoPull_sup h L η (miyamotoUnipotent_le_SU h false false) hle, miyamotoPull_inf] at this
  rw [this, e1, e2]

end Pull

end CFSG.LocalAnalysis.EvenBN.U4
