module

public import CFSG.LocalAnalysis.EvenBN.U4.Model.Basic

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag
open scoped commutatorElement

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

section Weights

theorem miyamotoIHom_injective : Function.Injective (miyamotoIHom h) := by
  intro p p' e
  have e1 := congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K) 0 0) e
  have e2 := congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K) 1 1) e
  simp [miyamotoIHom, miyamotoDiag] at e1 e2
  exact Prod.ext (Units.ext e1) (Units.ext e2)

theorem miyamotoIHom_mem_gramSU_iff (p : Kˣ × Kˣ) :
    miyamotoIHom h p ∈ gramSU h (miyamotoJ4 K) ↔ miyamotoIParam h p = 1 := by
  rw [mem_gramSU]
  have hu : ((miyamotoIHom h p : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      diagonal ![(p.1 : K), p.2, (h.bar p.2)⁻¹, (h.bar p.1)⁻¹] := by
    simp [miyamotoIHom, miyamotoDiag]
  have hJ : ((((miyamotoIHom h p : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar)ᵀ *
      miyamotoJ4 K * miyamotoIHom h p) = miyamotoJ4 K := by
    rw [hu]
    have h1 : h.bar (p.1 : K) ≠ 0 := by simp
    have h2 : h.bar (p.2 : K) ≠ 0 := by simp
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [miyamotoJ4, Matrix.mul_apply, Fin.sum_univ_four, diagonal, map_inv₀, h.bar_bar]
  have hdet : (((miyamotoIHom h p : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)).det =
      ((miyamotoIParam h p : Kˣ) : K) := by
    rw [hu, det_diagonal, Fin.prod_univ_four]
    simp [miyamotoIParam]
    ring
  rw [hdet]
  constructor
  · rintro ⟨-, hd⟩
    exact Units.ext hd
  · intro hp
    exact ⟨hJ, by rw [hp, Units.val_one]⟩

theorem miyamotoIHom_mem_miyamotoI_iff (p : Kˣ × Kˣ) :
    miyamotoIHom h p ∈ miyamotoI h ↔ miyamotoIParam h p = 1 := by
  constructor
  · rintro ⟨p', hp', e⟩
    rw [← miyamotoIHom_injective h e]
    exact hp'
  · exact fun hp => ⟨p, hp, rfl⟩

theorem miyamotoI_le_gramSU : miyamotoI h ≤ gramSU h (miyamotoJ4 K) := by
  rintro _ ⟨p, hp, rfl⟩
  exact (miyamotoIHom_mem_gramSU_iff h p).2 hp

@[expose] def miyamotoWeightA : Kˣ × Kˣ →* Kˣ :=
  MonoidHom.fst Kˣ Kˣ * (MonoidHom.snd Kˣ Kˣ)⁻¹

@[expose] def miyamotoWeightB : Kˣ × Kˣ →* Kˣ :=
  MonoidHom.snd Kˣ Kˣ * (Units.map h.bar.toMonoidHom).comp (MonoidHom.snd Kˣ Kˣ)

@[expose] def miyamotoWeightC : Kˣ × Kˣ →* Kˣ :=
  MonoidHom.fst Kˣ Kˣ * (Units.map h.bar.toMonoidHom).comp (MonoidHom.snd Kˣ Kˣ)

@[expose] def miyamotoWeightZ : Kˣ × Kˣ →* Kˣ :=
  MonoidHom.fst Kˣ Kˣ * (Units.map h.bar.toMonoidHom).comp (MonoidHom.fst Kˣ Kˣ)

@[simp] theorem coe_miyamotoWeightA (p : Kˣ × Kˣ) :
    ((miyamotoWeightA p : Kˣ) : K) = (p.1 : K) * (p.2 : K)⁻¹ := by
  simp [miyamotoWeightA]

@[simp] theorem coe_miyamotoWeightB (p : Kˣ × Kˣ) :
    ((miyamotoWeightB h p : Kˣ) : K) = (p.2 : K) * h.bar p.2 := by
  simp [miyamotoWeightB]

@[simp] theorem coe_miyamotoWeightC (p : Kˣ × Kˣ) :
    ((miyamotoWeightC h p : Kˣ) : K) = (p.1 : K) * h.bar p.2 := by
  simp [miyamotoWeightC]

@[simp] theorem coe_miyamotoWeightZ (p : Kˣ × Kˣ) :
    ((miyamotoWeightZ h p : Kˣ) : K) = (p.1 : K) * h.bar p.1 := by
  simp [miyamotoWeightZ]

theorem miyamotoIHom_conj_rootA (p : Kˣ × Kˣ) (a : K) :
    (miyamotoIHom h p)⁻¹ * miyamotoXGL h a 0 0 0 * miyamotoIHom h p =
      miyamotoXGL h (miyamotoWeightA p * a) 0 0 0 := by
  rw [miyamotoIHom_conj]
  simp

theorem miyamotoIHom_conj_rootB (p : Kˣ × Kˣ) (b : K) :
    (miyamotoIHom h p)⁻¹ * miyamotoXGL h 0 b 0 0 * miyamotoIHom h p =
      miyamotoXGL h 0 (miyamotoWeightB h p * b) 0 0 := by
  rw [miyamotoIHom_conj]
  simp

theorem miyamotoIHom_conj_rootC (p : Kˣ × Kˣ) (c : K) :
    (miyamotoIHom h p)⁻¹ * miyamotoXGL h 0 0 c 0 * miyamotoIHom h p =
      miyamotoXGL h 0 0 (miyamotoWeightC h p * c) 0 := by
  rw [miyamotoIHom_conj]
  simp

theorem miyamotoIHom_conj_Z (p : Kˣ × Kˣ) (d : K) :
    (miyamotoIHom h p)⁻¹ * miyamotoXGL h 0 0 0 d * miyamotoIHom h p =
      miyamotoXGL h 0 0 0 (miyamotoWeightZ h p * d) := by
  rw [miyamotoIHom_conj]
  simp

theorem miyamotoR1_mul_self : miyamotoR1 K * miyamotoR1 K = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [miyamotoR1, Matrix.mul_apply, Fin.sum_univ_four]

theorem miyamotoR2_mul_self : miyamotoR2 K * miyamotoR2 K = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [miyamotoR2, Matrix.mul_apply, Fin.sum_univ_four]

theorem miyamotoR1_conj_miyamotoIHom (p : Kˣ × Kˣ) :
    (miyamotoR1 K)⁻¹ * miyamotoIHom h p * miyamotoR1 K = miyamotoIHom h p.swap := by
  apply Units.ext
  simp only [Units.val_mul]
  change _ * diagonal _ * _ = diagonal _
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;> simp [miyamotoR1, Fin.sum_univ_four]

theorem miyamotoR2_conj_miyamotoIHom (p : Kˣ × Kˣ) :
    (miyamotoR2 K)⁻¹ * miyamotoIHom h p * miyamotoR2 K =
      miyamotoIHom h (p.1, (Units.map h.bar.toMonoidHom p.2)⁻¹) := by
  apply Units.ext
  simp only [Units.val_mul]
  change _ * diagonal _ * _ = diagonal _
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;> simp [miyamotoR2, Fin.sum_univ_four, h.bar_bar]

theorem miyamotoR2_conj_rootC (c : K) :
    (miyamotoR2 K)⁻¹ * miyamotoXGL h 0 0 c 0 * miyamotoR2 K = miyamotoXGL h c 0 0 0 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [miyamotoR2, miyamotoX, Matrix.mul_apply, Fin.sum_univ_four]

theorem miyamotoR2_conj_Z (d : K) :
    (miyamotoR2 K)⁻¹ * miyamotoXGL h 0 0 0 d * miyamotoR2 K = miyamotoXGL h 0 0 0 d := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [miyamotoR2, miyamotoX, Matrix.mul_apply, Fin.sum_univ_four]

@[expose] def miyamotoI1r2 : Subgroup (GL (Fin 4) K) :=
  (miyamotoI1 h).map (MulAut.conj (miyamotoR2 K)⁻¹).toMonoidHom

theorem miyamotoI1Hom_eq {t : Kˣ} (ht : h.bar t = t) :
    miyamotoI1Hom t = miyamotoIHom h (t, t) := by
  have : Units.map h.bar.toMonoidHom t = t := Units.ext ht
  change miyamotoDiag t t t⁻¹ t⁻¹ = miyamotoDiag t t (Units.map h.bar.toMonoidHom t)⁻¹
    (Units.map h.bar.toMonoidHom t)⁻¹
  rw [this]

theorem mem_miyamotoI1 {g : GL (Fin 4) K} :
    g ∈ miyamotoI1 h ↔ ∃ t : Kˣ, h.bar t = t ∧ g = miyamotoIHom h (t, t) := by
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨Units.map h.fixedField.subtype.toMonoidHom t, (t : h.fixedField).2, ?_⟩
    rw [MonoidHom.comp_apply]
    exact miyamotoI1Hom_eq h (t : h.fixedField).2
  · rintro ⟨t, ht, rfl⟩
    have ht0 : (⟨t, ht⟩ : h.fixedField) ≠ 0 := fun e => t.ne_zero (congrArg Subtype.val e)
    refine ⟨Units.mk0 _ ht0, ?_⟩
    have e : Units.map h.fixedField.subtype.toMonoidHom (Units.mk0 _ ht0) = t := Units.ext rfl
    rw [MonoidHom.comp_apply, e, miyamotoI1Hom_eq h ht]

theorem mem_miyamotoI1r2 {g : GL (Fin 4) K} :
    g ∈ miyamotoI1r2 h ↔ ∃ t : Kˣ, h.bar t = t ∧ g = miyamotoIHom h (t, t⁻¹) := by
  have key : ∀ t : Kˣ, h.bar t = t → (MulAut.conj (miyamotoR2 K)⁻¹).toMonoidHom
      (miyamotoIHom h (t, t)) = miyamotoIHom h (t, t⁻¹) := by
    intro t ht
    have : Units.map h.bar.toMonoidHom t = t := Units.ext ht
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [miyamotoR2_conj_miyamotoIHom, this]
  constructor
  · rintro ⟨g', hg', rfl⟩
    obtain ⟨t, ht, rfl⟩ := (mem_miyamotoI1 h).1 hg'
    exact ⟨t, ht, key t ht⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨_, (mem_miyamotoI1 h).2 ⟨t, ht, rfl⟩, key t ht⟩

theorem mem_centralizer_singleton_iff_conj {G : Type*} [Group G] {g D : G} :
    g ∈ centralizer ({D} : Set G) ↔ D⁻¹ * g * D = g := by
  rw [mem_centralizer_singleton_iff]
  constructor
  · intro e
    rw [mul_assoc, e, inv_mul_cancel_left]
  · intro e
    calc g * D = D * (D⁻¹ * g * D) := by group
      _ = D * g := by rw [e]

theorem exists_fixed_unit_sq_ne_one (hf : 2 ≤ f) : ∃ t : Kˣ, h.bar t = t ∧ (t : K) ^ 2 ≠ 1 := by
  have := h.finite
  have hcard : ({0, 1} : Set K).ncard < {d : K | h.bar d = d}.ncard := by
    rw [ncard_fixed h, Set.ncard_pair zero_ne_one]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨t, ht, ht01⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hcard
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at ht01
  refine ⟨Units.mk0 t ht01.1, ht, fun e => ht01.2 ?_⟩
  have : CharP K 2 := h.charP
  have e' : (t + 1) ^ 2 = 0 := by
    simp only [Units.val_mk0] at e
    linear_combination e + (t + 1) * CharTwo.two_eq_zero (R := K)
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 e'
  linear_combination this - CharTwo.two_eq_zero (R := K)

end Weights

section Centralizers

theorem eq_zero_of_mul_eq_self {u x : K} (hu : u ≠ 1) (e : u * x = x) : x = 0 := by
  have : (u - 1) * x = 0 := by linear_combination e
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hu)

theorem miyamotoP_inf_centralizer_I1 (hf : 2 ≤ f) :
    miyamotoP h ⊓ centralizer (miyamotoI1 h : Set (GL (Fin 4) K)) = miyamotoRootA h := by
  obtain ⟨t, ht, ht2⟩ := exists_fixed_unit_sq_ne_one h hf
  have ht2' : (t : K) * t ≠ 1 := by rwa [← sq]
  apply le_antisymm
  · rintro g ⟨hgP, hgC⟩
    obtain ⟨a, b, c, d, -, -, rfl⟩ := (mem_P h).1 hgP
    have e := (mem_centralizer_singleton_iff_conj).1 (centralizer_le
      (Set.singleton_subset_iff.2 ((mem_miyamotoI1 h).2 ⟨t, ht, rfl⟩)) hgC)
    rw [miyamotoIHom_conj, miyamotoXGL_inj] at e
    simp only [ht] at e
    rw [eq_zero_of_mul_eq_self ht2' e.2.1, eq_zero_of_mul_eq_self ht2' e.2.2.1,
      eq_zero_of_mul_eq_self ht2' e.2.2.2]
    exact ⟨a, rfl⟩
  · rintro _ ⟨a, rfl⟩
    refine ⟨(miyamotoXGL_mem_P h).2 ⟨map_zero _, by simp⟩, mem_centralizer_iff.2 fun g hg => ?_⟩
    obtain ⟨s, -, rfl⟩ := (mem_miyamotoI1 h).1 hg
    refine (mem_centralizer_singleton_iff.1 ((mem_centralizer_singleton_iff_conj).2 ?_)).symm
    rw [miyamotoIHom_conj_rootA]
    simp

theorem miyamotoP_inf_centralizer_I1r2 (hf : 2 ≤ f) :
    miyamotoP h ⊓ centralizer (miyamotoI1r2 h : Set (GL (Fin 4) K)) = miyamotoRootC h := by
  obtain ⟨t, ht, ht2⟩ := exists_fixed_unit_sq_ne_one h hf
  have ht0 : (t : K) ≠ 0 := t.ne_zero
  have ht2' : (t : K) * t ≠ 1 := by rwa [← sq]
  have ht2'' : (t : K)⁻¹ * (t : K)⁻¹ ≠ 1 := by
    rw [← mul_inv]
    exact fun e => ht2' (inv_eq_one.1 e)
  apply le_antisymm
  · rintro g ⟨hgP, hgC⟩
    obtain ⟨a, b, c, d, -, -, rfl⟩ := (mem_P h).1 hgP
    have e := (mem_centralizer_singleton_iff_conj).1 (centralizer_le
      (Set.singleton_subset_iff.2 ((mem_miyamotoI1r2 h).2 ⟨t, ht, rfl⟩)) hgC)
    rw [miyamotoIHom_conj, miyamotoXGL_inj] at e
    simp only [Units.val_inv_eq_inv_val, map_inv₀, ht, inv_inv] at e
    rw [eq_zero_of_mul_eq_self ht2' e.1, eq_zero_of_mul_eq_self ht2'' e.2.1,
      eq_zero_of_mul_eq_self ht2' e.2.2.2]
    exact ⟨c, rfl⟩
  · rintro _ ⟨c, rfl⟩
    refine ⟨(miyamotoXGL_mem_P h).2 ⟨map_zero _, by simp⟩, mem_centralizer_iff.2 fun g hg => ?_⟩
    obtain ⟨s, hs, rfl⟩ := (mem_miyamotoI1r2 h).1 hg
    refine (mem_centralizer_singleton_iff.1 ((mem_centralizer_singleton_iff_conj).2 ?_)).symm
    rw [miyamotoIHom_conj_rootC]
    have hs0 : (s : K) ≠ 0 := s.ne_zero
    simp [map_inv₀, hs, hs0]

theorem exists_miyamotoIParam_eq_one_weightB_eq_one (γ : Kˣ) :
    ∃ p : Kˣ × Kˣ, miyamotoIParam h p = 1 ∧ miyamotoWeightB h p = 1 ∧
      miyamotoWeightA p = γ := by
  have := h.finite
  have hbb := h.bar_bar
  set μ := (Units.map h.normHom).ker
  have hcard : Nat.card μ = 2 ^ f + 1 := h.card_ker_normUnits_and_surjective.1
  have hcop : (Nat.card μ).Coprime 4 := by
    rw [hcard, show (4 : ℕ) = 2 ^ 2 by norm_num]
    refine Nat.Coprime.pow_right 2 (Nat.coprime_two_right.2 ?_)
    exact (Nat.even_pow.2 ⟨even_two, by have := h.one_le; omega⟩).add_one
  set ε : Kˣ := Units.map h.bar.toMonoidHom γ * γ⁻¹
  have hε : ε ∈ μ := by
    rw [UnitaryFieldData.mem_ker_normUnits, UnitaryFieldData.norm]
    have hg0 : (γ : K) ≠ 0 := γ.ne_zero
    have hgb : h.bar (γ : K) ≠ 0 := by simp [hg0]
    simp only [ε, Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
      map_mul, hbb, Units.val_inv_eq_inv_val, map_inv₀]
    field_simp
  set β₀ : μ := (powCoprime hcop).symm ⟨ε, hε⟩
  have hβ4 : (β₀ : Kˣ) ^ 4 = ε := by
    have := (powCoprime hcop).apply_symm_apply ⟨ε, hε⟩
    rw [powCoprime_apply] at this
    exact congrArg Subtype.val this
  have hβN : ((β₀ : Kˣ) : K) * h.bar (β₀ : Kˣ) = 1 := by
    have := (UnitaryFieldData.mem_ker_normUnits h).1 β₀.2
    exact this
  refine ⟨(γ * β₀, β₀), ?_, Units.ext ?_, Units.ext ?_⟩
  · apply Units.ext
    have hb0 : ((β₀ : Kˣ) : K) ≠ 0 := (β₀ : Kˣ).ne_zero
    have hg0 : (γ : K) ≠ 0 := γ.ne_zero
    have hbar : h.bar ((β₀ : Kˣ) : K) = ((β₀ : Kˣ) : K)⁻¹ := eq_inv_of_mul_eq_one_right hβN
    have h4 : ((β₀ : Kˣ) : K) ^ 4 = h.bar (γ : K) * (γ : K)⁻¹ := by
      have := congrArg Units.val hβ4
      simpa [ε] using this
    have hgb : h.bar (γ : K) ≠ 0 := by simp [hg0]
    simp only [miyamotoIParam, MonoidHom.mul_apply, MonoidHom.coe_fst, MonoidHom.coe_snd,
      MonoidHom.inv_apply, MonoidHom.coe_comp, Function.comp_apply, Units.val_mul,
      Units.val_inv_eq_inv_val, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
      map_mul, hbar,
      Units.val_one]
    field_simp
    rw [h4]
    field_simp
  · simp [hβN]
  · simp

end Centralizers

end CFSG.LocalAnalysis.EvenBN.U4
