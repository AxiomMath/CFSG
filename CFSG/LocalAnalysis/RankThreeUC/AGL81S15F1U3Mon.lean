module

public import CFSG.LieType.Universal.Unitary.Comparison

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace F1Proof

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

section Monomial

variable {F : Type} [Field F]

@[expose] def dMat (a b c : F) : Matrix (Fin 3) (Fin 3) F := Matrix.diagonal ![a, b, c]

@[expose] def sMat' (a b c : F) : Matrix (Fin 3) (Fin 3) F := !![0, a, 0; b, 0, 0; 0, 0, c]

theorem dMat_mul_dMat (a b c a' b' c' : F) :
    dMat a b c * dMat a' b' c' = dMat (a * a') (b * b') (c * c') := by
  unfold dMat
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  fin_cases i <;> simp

theorem dMat_mul_sMat' (a b c a' b' c' : F) :
    dMat a b c * sMat' a' b' c' = sMat' (a * a') (b * b') (c * c') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dMat, sMat', Matrix.mul_apply, Fin.sum_univ_three]

theorem sMat'_mul_dMat (a b c a' b' c' : F) :
    sMat' a b c * dMat a' b' c' = sMat' (a * b') (b * a') (c * c') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dMat, sMat', Matrix.mul_apply, Fin.sum_univ_three]

theorem sMat'_mul_sMat' (a b c a' b' c' : F) :
    sMat' a b c * sMat' a' b' c' = dMat (a * b') (b * a') (c * c') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dMat, sMat', Matrix.mul_apply, Fin.sum_univ_three]

theorem dMat_one : dMat (1 : F) 1 1 = 1 := by
  unfold dMat
  rw [← Matrix.diagonal_one]
  congr 1
  ext i
  fin_cases i <;> simp

@[expose] def dGL (a b c : Fˣ) : GL (Fin 3) F :=
  ⟨dMat a b c, dMat (a⁻¹ : Fˣ) (b⁻¹ : Fˣ) (c⁻¹ : Fˣ), by
    rw [dMat_mul_dMat]; simp [dMat_one], by rw [dMat_mul_dMat]; simp [dMat_one]⟩

@[expose] def sGL (a b c : Fˣ) : GL (Fin 3) F :=
  ⟨sMat' a b c, sMat' (b⁻¹ : Fˣ) (a⁻¹ : Fˣ) (c⁻¹ : Fˣ), by
    rw [sMat'_mul_sMat']; simp [dMat_one], by rw [sMat'_mul_sMat']; simp [dMat_one]⟩

theorem coe_dGL (a b c : Fˣ) : ((dGL a b c : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
    dMat (a : F) b c := rfl

theorem coe_sGL (a b c : Fˣ) : ((sGL a b c : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
    sMat' (a : F) b c := rfl

theorem dGL_mul_dGL (a b c a' b' c' : Fˣ) :
    dGL a b c * dGL a' b' c' = (dGL (a * a') (b * b') (c * c') : GL (Fin 3) F) :=
  Units.ext (by simp [coe_dGL, dMat_mul_dMat])

theorem dGL_mul_sGL (a b c a' b' c' : Fˣ) :
    dGL a b c * sGL a' b' c' = (sGL (a * a') (b * b') (c * c') : GL (Fin 3) F) :=
  Units.ext (by simp [coe_dGL, coe_sGL, dMat_mul_sMat'])

theorem sGL_mul_dGL (a b c a' b' c' : Fˣ) :
    sGL a b c * dGL a' b' c' = (sGL (a * b') (b * a') (c * c') : GL (Fin 3) F) :=
  Units.ext (by simp [coe_dGL, coe_sGL, sMat'_mul_dMat])

theorem sGL_mul_sGL (a b c a' b' c' : Fˣ) :
    sGL a b c * sGL a' b' c' = (dGL (a * b') (b * a') (c * c') : GL (Fin 3) F) :=
  Units.ext (by simp [coe_dGL, coe_sGL, sMat'_mul_sMat'])

theorem dGL_inv (a b c : Fˣ) : (dGL a b c : GL (Fin 3) F)⁻¹ = dGL a⁻¹ b⁻¹ c⁻¹ := rfl

theorem sGL_inv (a b c : Fˣ) : (sGL a b c : GL (Fin 3) F)⁻¹ = sGL b⁻¹ a⁻¹ c⁻¹ := rfl

theorem dGL_one : (dGL 1 1 1 : GL (Fin 3) F) = 1 := Units.ext (by simp [coe_dGL, dMat_one])

theorem dMat_eq_one_iff {a b c : F} : dMat a b c = 1 ↔ a = 1 ∧ b = 1 ∧ c = 1 := by
  constructor
  · intro h
    have e0 := congrFun (congrFun h 0) 0
    have e1 := congrFun (congrFun h 1) 1
    have e2 := congrFun (congrFun h 2) 2
    simp [dMat] at e0 e1 e2
    exact ⟨e0, e1, e2⟩
  · rintro ⟨rfl, rfl, rfl⟩
    exact dMat_one

theorem det_dMat (a b c : F) : (dMat a b c).det = a * b * c := by
  simp [dMat, Matrix.det_diagonal, Fin.prod_univ_three]

theorem det_sMat' (a b c : F) : (sMat' a b c).det = -(a * b * c) := by
  simp [sMat', Matrix.det_fin_three]

variable (σ : F ≃+* F)

theorem conjTr_dMat (a b c : F) : conjTr σ (dMat a b c) = dMat (σ a) (σ b) (σ c) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [conjTr, dMat, Matrix.diagonal_apply]

theorem conjTr_sMat' (a b c : F) : conjTr σ (sMat' a b c) = sMat' (σ b) (σ a) (σ c) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [conjTr, sMat']

theorem dGL_mem_SUid {a b c : Fˣ} :
    (dGL a b c : GL (Fin 3) F) ∈ SUid σ 3 ↔
      (σ a * a = 1 ∧ σ b * b = 1 ∧ σ c * c = 1) ∧ (a : F) * b * c = 1 := by
  rw [mem_SUid, coe_dGL, det_dMat, conjTr_dMat, dMat_mul_dMat, dMat_eq_one_iff]
  tauto

theorem sGL_mem_SUid {a b c : Fˣ} :
    (sGL a b c : GL (Fin 3) F) ∈ SUid σ 3 ↔
      (σ a * a = 1 ∧ σ b * b = 1 ∧ σ c * c = 1) ∧ (a : F) * b * c = -1 := by
  rw [mem_SUid, coe_sGL, det_sMat', conjTr_sMat', sMat'_mul_sMat', dMat_eq_one_iff]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨h3, h2, h4⟩, neg_eq_iff_eq_neg.mp h1⟩
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩
    exact ⟨by rw [h4, neg_neg], h2, h1, h3⟩

end Monomial

section Wreath

variable {F : Type} [Field F]

theorem inv_mul_inv_aux {G : Type*} [CommGroup G] (a b c d : G) :
    (a * b)⁻¹ * (c * d)⁻¹ = ((a * c) * (b * d))⁻¹ := by
  rw [← mul_inv]
  congr 1
  ac_rfl

theorem inv_mul_inv_aux' {G : Type*} [CommGroup G] (a b c d : G) :
    (a * b)⁻¹ * (c * d)⁻¹ = ((a * d) * (b * c))⁻¹ := by
  rw [← mul_inv]
  congr 1
  ac_rfl

@[expose] def stdMon (N : ℕ) : Subgroup (GL (Fin 3) F) where
  carrier := {g | ∃ α β : Fˣ, α ^ N = 1 ∧ β ^ N = 1 ∧
    (g = dGL α β (α * β)⁻¹ ∨ g = sGL α β (-(α * β)⁻¹))}
  one_mem' := ⟨1, 1, one_pow _, one_pow _, Or.inl (by simp [dGL_one])⟩
  mul_mem' := by
    rintro _ _ ⟨α, β, hα, hβ, rfl | rfl⟩ ⟨α', β', hα', hβ', rfl | rfl⟩
    · refine ⟨α * α', β * β', by rw [mul_pow, hα, hα', one_mul], by rw [mul_pow, hβ, hβ', one_mul],
        Or.inl ?_⟩
      rw [dGL_mul_dGL, inv_mul_inv_aux]
    · refine ⟨α * α', β * β', by rw [mul_pow, hα, hα', one_mul], by rw [mul_pow, hβ, hβ', one_mul],
        Or.inr ?_⟩
      rw [dGL_mul_sGL, mul_neg, inv_mul_inv_aux]
    · refine ⟨α * β', β * α', by rw [mul_pow, hα, hβ', one_mul], by rw [mul_pow, hβ, hα', one_mul],
        Or.inr ?_⟩
      rw [sGL_mul_dGL, neg_mul, inv_mul_inv_aux']
    · refine ⟨α * β', β * α', by rw [mul_pow, hα, hβ', one_mul], by rw [mul_pow, hβ, hα', one_mul],
        Or.inl ?_⟩
      rw [sGL_mul_sGL, neg_mul_neg, inv_mul_inv_aux']
  inv_mem' := by
    rintro _ ⟨α, β, hα, hβ, rfl | rfl⟩
    · refine ⟨α⁻¹, β⁻¹, by rw [inv_pow, hα, inv_one], by rw [inv_pow, hβ, inv_one], Or.inl ?_⟩
      rw [dGL_inv, mul_inv]
    · refine ⟨β⁻¹, α⁻¹, by rw [inv_pow, hβ, inv_one], by rw [inv_pow, hα, inv_one], Or.inr ?_⟩
      rw [sGL_inv, inv_neg, mul_inv, mul_inv, inv_inv, inv_inv, mul_comm β⁻¹ α⁻¹]
      rw [show (α⁻¹ * β⁻¹)⁻¹ = α * β by rw [mul_inv, inv_inv, inv_inv]]

end Wreath

section Injectivity

variable {F : Type} [Field F]

theorem dGL_inj {a b c a' b' c' : Fˣ} (h : (dGL a b c : GL (Fin 3) F) = dGL a' b' c') :
    a = a' ∧ b = b' := by
  have h' := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) h
  simp only [coe_dGL] at h'
  have e0 := congrFun (congrFun h' 0) 0
  have e1 := congrFun (congrFun h' 1) 1
  simp [dMat] at e0 e1
  exact ⟨Units.ext e0, Units.ext e1⟩

theorem sGL_inj {a b c a' b' c' : Fˣ} (h : (sGL a b c : GL (Fin 3) F) = sGL a' b' c') :
    a = a' ∧ b = b' := by
  have h' := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) h
  simp only [coe_sGL] at h'
  have e0 := congrFun (congrFun h' 0) 1
  have e1 := congrFun (congrFun h' 1) 0
  simp [sMat'] at e0 e1
  exact ⟨Units.ext e0, Units.ext e1⟩

theorem dGL_ne_sGL (a b c a' b' c' : Fˣ) : (dGL a b c : GL (Fin 3) F) ≠ sGL a' b' c' := by
  intro h
  have h' := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) h
  simp only [coe_dGL, coe_sGL] at h'
  have e0 := congrFun (congrFun h' 0) 0
  simp [dMat, sMat'] at e0

@[expose] noncomputable def stdMonMap (N : ℕ) :
    Bool × ↥(rootsOfUnity N F) × ↥(rootsOfUnity N F) → GL (Fin 3) F :=
  fun x => if x.1 then sGL (x.2.1 : Fˣ) (x.2.2 : Fˣ) (-((x.2.1 : Fˣ) * (x.2.2 : Fˣ))⁻¹)
    else dGL (x.2.1 : Fˣ) (x.2.2 : Fˣ) ((x.2.1 : Fˣ) * (x.2.2 : Fˣ))⁻¹

theorem stdMonMap_injective (N : ℕ) : Function.Injective (stdMonMap (F := F) N) := by
  rintro ⟨b, α, β⟩ ⟨b', α', β'⟩ h
  simp only [stdMonMap] at h
  cases b <;> cases b' <;> simp only [Bool.false_eq_true, ↓reduceIte] at h
  · obtain ⟨h1, h2⟩ := dGL_inj h
    simp [Subtype.ext h1, Subtype.ext h2]
  · exact (dGL_ne_sGL _ _ _ _ _ _ h).elim
  · exact (dGL_ne_sGL _ _ _ _ _ _ h.symm).elim
  · obtain ⟨h1, h2⟩ := sGL_inj h
    simp [Subtype.ext h1, Subtype.ext h2]

theorem range_stdMonMap (N : ℕ) :
    Set.range (stdMonMap (F := F) N) = (stdMon (F := F) N : Set (GL (Fin 3) F)) := by
  ext g
  constructor
  · rintro ⟨⟨b, α, β⟩, rfl⟩
    have hα : (α : Fˣ) ^ N = 1 := (mem_rootsOfUnity N _).1 α.2
    have hβ : (β : Fˣ) ^ N = 1 := (mem_rootsOfUnity N _).1 β.2
    cases b
    · exact ⟨α, β, hα, hβ, Or.inl rfl⟩
    · exact ⟨α, β, hα, hβ, Or.inr rfl⟩
  · rintro ⟨α, β, hα, hβ, rfl | rfl⟩
    · exact ⟨⟨false, ⟨α, (mem_rootsOfUnity N _).2 hα⟩, ⟨β, (mem_rootsOfUnity N _).2 hβ⟩⟩, rfl⟩
    · exact ⟨⟨true, ⟨α, (mem_rootsOfUnity N _).2 hα⟩, ⟨β, (mem_rootsOfUnity N _).2 hβ⟩⟩, rfl⟩

theorem card_stdMon (N : ℕ) (hroots : Nat.card (rootsOfUnity N F) = N) :
    Nat.card (stdMon (F := F) N) = 2 * N ^ 2 := by
  have h1 : Nat.card (stdMon (F := F) N) = Nat.card (Set.range (stdMonMap (F := F) N)) := by
    rw [range_stdMonMap]; rfl
  rw [h1, ← Nat.card_congr (Equiv.ofInjective _ (stdMonMap_injective N)), Nat.card_prod,
    Nat.card_prod, hroots]
  simp [Nat.card_eq_fintype_card]
  ring

end Injectivity

section Standard

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

theorem unitary_norm_eq_one {N : ℕ} (hN : N ∣ p ^ f + 1) {α : Fˣ} (hα : α ^ N = 1) :
    unitaryInvolution F p f (α : F) * α = 1 := by
  rw [unitaryInvolution_apply]
  obtain ⟨k, hk⟩ := hN
  have h1 : (α : F) ^ N = 1 := by
    have := congrArg Units.val hα
    simpa using this
  have : (α : F) ^ (p ^ f + 1) = 1 := by
    rw [hk, pow_mul, h1, one_pow]
  rw [← pow_succ]
  exact this

theorem stdMon_le_SUid {N : ℕ} (hNe : Even N) (hN : N ∣ p ^ f + 1) :
    stdMon (F := F) N ≤ SUid (unitaryInvolution F p f) 3 := by
  have h3 : ∀ α β : Fˣ, α ^ N = 1 → β ^ N = 1 → ((α * β)⁻¹) ^ N = 1 := by
    intro α β hα hβ
    rw [inv_pow, mul_pow, hα, hβ]; simp
  have h4 : ∀ α β : Fˣ, α ^ N = 1 → β ^ N = 1 → (-(α * β)⁻¹) ^ N = 1 := by
    intro α β hα hβ
    rw [hNe.neg_pow]
    exact h3 α β hα hβ
  rintro _ ⟨α, β, hα, hβ, rfl | rfl⟩
  · rw [dGL_mem_SUid]
    refine ⟨⟨unitary_norm_eq_one hN hα, unitary_norm_eq_one hN hβ,
      unitary_norm_eq_one hN (h3 α β hα hβ)⟩, ?_⟩
    have h1 := α.ne_zero
    have h2 := β.ne_zero
    simp [Units.val_inv_eq_inv_val]
    field_simp
  · rw [sGL_mem_SUid]
    refine ⟨⟨unitary_norm_eq_one hN hα, unitary_norm_eq_one hN hβ,
      unitary_norm_eq_one hN (h4 α β hα hβ)⟩, ?_⟩
    have h1 := α.ne_zero
    have h2 := β.ne_zero
    simp [Units.val_inv_eq_inv_val]
    field_simp

end Standard



end F1Proof

end CFSG.LocalAnalysis.RankThreeUC.S15
