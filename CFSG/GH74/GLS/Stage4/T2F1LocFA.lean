module

public import CFSG.GH74.GLS.Stage4.T2SL2A

public noncomputable section

namespace CFSG.GH74.GLS.Stage4.Rest.F1Loc

open CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2 Subgroup


theorem sl2_UL_W {F : Type} [Field F] : (sl2U (1 : F) * sl2L (-1) * sl2U 1 : SL2 F) = sl2W F := by
  apply t2A_ext <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem sl2_ULU_entry {F : Type} [Field F] (c : F) :
    ((sl2U c * sl2L (-c) * sl2U c : SL2 F) : Matrix (Fin 2) (Fin 2) F) 1 0 = -c := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem map_sl2U {F F' : Type} [Field F] [Field F'] (σ : F →+* F') (c : F) :
    Matrix.SpecialLinearGroup.map σ (sl2U c) = sl2U (σ c) := by
  apply sl2_ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.map_apply_coe]

theorem map_sl2L {F F' : Type} [Field F] [Field F'] (σ : F →+* F') (c : F) :
    Matrix.SpecialLinearGroup.map σ (sl2L c) = sl2L (σ c) := by
  apply sl2_ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.map_apply_coe]

theorem exists_ringHom_of_sq_mul {F : Type} [Field F] (h2 : (2 : F) ≠ 0) (α : F → F)
    (hadd : ∀ a b, α (a + b) = α a + α b) (h1 : α 1 = 1)
    (hsq : ∀ t c : F, α (t ^ 2 * c) = α (t ^ 2) * α c) :
    ∃ σ : F →+* F, ∀ x, σ x = α x := by
  have h0 : α 0 = 0 := by
    have := hadd 0 0
    simpa using this
  have hneg : ∀ a, α (-a) = - α a := fun a => by
    have := hadd (-a) a
    rw [neg_add_cancel, h0] at this
    exact eq_neg_of_add_eq_zero_left this.symm
  have hP : ∀ s : F, (∀ c, α (s * c) = α s * α c) → (∀ c, α (-s * c) = α (-s) * α c) := by
    intro s hs c
    rw [neg_mul, hneg, hneg, hs, neg_mul]
  have hA : ∀ s s' : F, (∀ c, α (s * c) = α s * α c) → (∀ c, α (s' * c) = α s' * α c) →
      (∀ c, α ((s + s') * c) = α (s + s') * α c) := by
    intro s s' hs hs' c
    rw [add_mul, hadd, hadd, hs, hs', add_mul]
  have hall : ∀ y c : F, α (y * c) = α y * α c := by
    intro y
    have e : y = (y / 2 + 1) ^ 2 + (-((y / 2) ^ 2) + -(1 ^ 2)) := by
      field_simp
      ring
    rw [e]
    exact hA _ _ (hsq (y / 2 + 1)) (hA _ _ (hP _ (hsq (y / 2))) (hP _ (by
      intro c
      have := hsq 1 c
      simpa using this)))
  refine ⟨{ toFun := α
            map_one' := h1
            map_mul' := ?_
            map_zero' := h0
            map_add' := hadd }, fun x => rfl⟩
  intro a b
  exact hall a b

theorem exists_fieldAut {G : Type} [Group G] {F : Type} [Field F] [Finite F]
    (h2 : (2 : F) ≠ 0) (φ : SL2 F →* G) (hφ : Function.Injective φ) (f : G)
    (hU : ∀ c : F, ∃ c' : F, f * φ (sl2U c) * f⁻¹ = φ (sl2U c'))
    (hT : ∀ t : Fˣ, ∃ t' : Fˣ, f * φ (sl2D t) * f⁻¹ = φ (sl2D t'))
    (hW : f * φ (sl2W F) = φ (sl2W F) * f) :
    ∃ σ : F ≃+* F, ∀ M : SL2 F,
      f * φ M * f⁻¹ = φ (Matrix.SpecialLinearGroup.map (σ : F →+* F) M) := by
  classical
  choose α hα using hU
  choose τ hτ using hT
  have hadd : ∀ a b, α (a + b) = α a + α b := by
    intro a b
    apply sl2U_injective (F := F)
    apply hφ
    calc φ (sl2U (α (a + b))) = f * φ (sl2U (a + b)) * f⁻¹ := (hα _).symm
      _ = (f * φ (sl2U a) * f⁻¹) * (f * φ (sl2U b) * f⁻¹) := by
          rw [sl2U_add, map_mul]; group
      _ = φ (sl2U (α a)) * φ (sl2U (α b)) := by rw [hα, hα]
      _ = φ (sl2U (α a + α b)) := by rw [sl2U_add, map_mul]
  have h0 : α 0 = 0 := by
    have := hadd 0 0
    simpa using this
  have hneg : ∀ a, α (-a) = - α a := fun a => by
    have := hadd (-a) a
    rw [neg_add_cancel, h0] at this
    exact eq_neg_of_add_eq_zero_left this.symm
  have hW' : f * φ (sl2W F) * f⁻¹ = φ (sl2W F) := by rw [hW]; group
  have hWi : f * (φ (sl2W F))⁻¹ * f⁻¹ = (φ (sl2W F))⁻¹ := by
    have : f * (φ (sl2W F))⁻¹ * f⁻¹ = (f * φ (sl2W F) * f⁻¹)⁻¹ := by group
    rw [this, hW']
  have hL : ∀ c : F, f * φ (sl2L c) * f⁻¹ = φ (sl2L (α c)) := by
    intro c
    have e1 : sl2L c = sl2W F * sl2U (-c) * (sl2W F)⁻¹ := by
      rw [t2A_W_conj_U, neg_neg]
    have e2 : sl2L (α c) = sl2W F * sl2U (α (-c)) * (sl2W F)⁻¹ := by
      rw [t2A_W_conj_U, hneg, neg_neg]
    calc f * φ (sl2L c) * f⁻¹
        = (f * φ (sl2W F) * f⁻¹) * (f * φ (sl2U (-c)) * f⁻¹) * (f * (φ (sl2W F))⁻¹ * f⁻¹) := by
          rw [e1, map_mul, map_mul, map_inv]; group
      _ = φ (sl2W F) * φ (sl2U (α (-c))) * (φ (sl2W F))⁻¹ := by rw [hW', hα, hWi]
      _ = φ (sl2L (α c)) := by rw [e2, map_mul, map_mul, map_inv]
  have htor : ∀ (t : Fˣ) (c : F), α ((t : F) ^ 2 * c) = ((τ t : Fˣ) : F) ^ 2 * α c := by
    intro t c
    apply sl2U_injective (F := F)
    apply hφ
    calc φ (sl2U (α ((t : F) ^ 2 * c))) = f * φ (sl2U ((t : F) ^ 2 * c)) * f⁻¹ := (hα _).symm
      _ = f * φ (sl2D t * sl2U c * (sl2D t)⁻¹) * f⁻¹ := by rw [t2A_conj_U]
      _ = (f * φ (sl2D t) * f⁻¹) * (f * φ (sl2U c) * f⁻¹) * (f * φ (sl2D t) * f⁻¹)⁻¹ := by
          rw [map_mul, map_mul, map_inv]; group
      _ = φ (sl2D (τ t)) * φ (sl2U (α c)) * (φ (sl2D (τ t)))⁻¹ := by rw [hτ, hα]
      _ = φ (sl2U (((τ t : Fˣ) : F) ^ 2 * α c)) := by
          rw [← map_inv, ← map_mul, ← map_mul, t2A_conj_U]
  have hone : α 1 = 1 := by
    have h1 : φ (sl2W F) = φ (sl2U (α 1) * sl2L (-α 1) * sl2U (α 1)) := by
      calc φ (sl2W F) = f * φ (sl2W F) * f⁻¹ := hW'.symm
        _ = f * φ (sl2U 1 * sl2L (-1) * sl2U 1) * f⁻¹ := by rw [sl2_UL_W]
        _ = (f * φ (sl2U 1) * f⁻¹) * (f * φ (sl2L (-1)) * f⁻¹) * (f * φ (sl2U 1) * f⁻¹) := by
            rw [map_mul, map_mul]; group
        _ = φ (sl2U (α 1) * sl2L (-α 1) * sl2U (α 1)) := by
            rw [hα, hL, hneg, map_mul, map_mul]
    have h3 := congrArg (fun x : SL2 F => (x : Matrix (Fin 2) (Fin 2) F) 1 0) (hφ h1)
    simp only [coe_sl2W, sl2_ULU_entry] at h3
    simpa using h3.symm
  have hsq : ∀ t c : F, α (t ^ 2 * c) = α (t ^ 2) * α c := by
    intro t c
    by_cases ht : t = 0
    · subst ht; simp [h0]
    · have h1 := htor (Units.mk0 t ht) c
      have h2' := htor (Units.mk0 t ht) 1
      simp only [Units.val_mk0, mul_one, hone] at h1 h2'
      rw [h1, h2']
  obtain ⟨σ₀, hσ₀⟩ := exists_ringHom_of_sq_mul h2 α hadd hone hsq
  have hbij : Function.Bijective σ₀ := Finite.injective_iff_bijective.1 σ₀.injective
  let σ : F ≃+* F := RingEquiv.ofBijective σ₀ hbij
  have hσ : ∀ x, (σ : F →+* F) x = α x := fun x => hσ₀ x
  refine ⟨σ, ?_⟩
  let A : SL2 F →* G := (MulAut.conj f).toMonoidHom.comp φ
  let B : SL2 F →* G := φ.comp (Matrix.SpecialLinearGroup.map (σ : F →+* F))
  have hAB : A = B := by
    apply MonoidHom.eq_of_eqOn_dense (s := ((uSub F : Set (SL2 F)) ∪ (lSub F : Set (SL2 F))))
    · rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq, uSub_sup_lSub]
    · intro M hM
      rcases hM with hM | hM
      · obtain ⟨c, rfl⟩ := mem_uSub.1 hM
        show f * φ (sl2U c) * f⁻¹ = φ (Matrix.SpecialLinearGroup.map (σ : F →+* F) (sl2U c))
        rw [hα, map_sl2U, hσ]
      · obtain ⟨c, rfl⟩ := mem_lSub.1 hM
        show f * φ (sl2L c) * f⁻¹ = φ (Matrix.SpecialLinearGroup.map (σ : F →+* F) (sl2L c))
        rw [hL, map_sl2L, hσ]
  intro M
  exact congrArg (fun X : SL2 F →* G => X M) hAB


section Powers

variable {G : Type} [Group G] {F : Type} [Field F]

theorem conj_pow_sl2U (φ : SL2 F →* G) (f : G) (σ : F ≃+* F)
    (hσ : ∀ M : SL2 F, f * φ M * f⁻¹ = φ (Matrix.SpecialLinearGroup.map (σ : F →+* F) M))
    (k : ℕ) (c : F) :
    f ^ k * φ (sl2U c) * (f ^ k)⁻¹ = φ (sl2U ((σ ^ k) c)) := by
  induction k generalizing c with
  | zero => simp
  | succ k ih =>
    have e : f ^ (k + 1) * φ (sl2U c) * (f ^ (k + 1))⁻¹ =
        f * (f ^ k * φ (sl2U c) * (f ^ k)⁻¹) * f⁻¹ := by rw [pow_succ']; group
    rw [e, ih, hσ, map_sl2U, pow_succ']
    rfl

theorem pow_eq_one_of_pow_eq_one (φ : SL2 F →* G) (hφ : Function.Injective φ) (f : G)
    (σ : F ≃+* F)
    (hσ : ∀ M : SL2 F, f * φ M * f⁻¹ = φ (Matrix.SpecialLinearGroup.map (σ : F →+* F) M))
    {r : ℕ} (hr : f ^ r = 1) : σ ^ r = 1 := by
  ext c
  have h := conj_pow_sl2U φ f σ hσ r c
  rw [hr, inv_one, one_mul, mul_one] at h
  have h2 := sl2U_injective (hφ h)
  simpa using h2.symm

theorem centralizes_iff (φ : SL2 F →* G) (hφ : Function.Injective φ) (f : G) (σ : F ≃+* F)
    (hσ : ∀ M : SL2 F, f * φ M * f⁻¹ = φ (Matrix.SpecialLinearGroup.map (σ : F →+* F) M))
    (M : SL2 F) :
    f * φ M * f⁻¹ = φ M ↔ ∀ i j, σ ((M : Matrix (Fin 2) (Fin 2) F) i j) = (M : Matrix (Fin 2) (Fin 2) F) i j := by
  rw [hσ]
  constructor
  · intro h i j
    have := congrArg (fun x : SL2 F => (x : Matrix (Fin 2) (Fin 2) F) i j) (hφ h)
    simpa [Matrix.SpecialLinearGroup.map_apply_coe] using this
  · intro h
    congr 1
    apply Subtype.ext
    ext i j
    simpa [Matrix.SpecialLinearGroup.map_apply_coe] using h i j

end Powers

section Fixed

variable {F : Type} [Field F]

@[expose] def fixF (σ : F ≃+* F) : Subfield F := FixedPoints.subfield (Subgroup.zpowers σ) F

theorem mem_fixF {σ : F ≃+* F} {x : F} : x ∈ fixF σ ↔ σ x = x := by
  constructor
  · intro hx
    have := hx ⟨σ, mem_zpowers σ⟩
    simpa using this
  · intro hx g
    obtain ⟨g, k, rfl⟩ := g
    show (σ ^ k) x = x
    induction k using Int.induction_on with
    | zero => simp
    | succ k ih =>
      rw [zpow_add_one]
      show (σ ^ k) (σ x) = x
      rw [hx]; exact ih
    | pred k ih =>
      rw [zpow_sub_one]
      show (σ ^ (-(k : ℤ))) (σ⁻¹ x) = x
      have : σ⁻¹ x = x := by
        show σ.symm x = x
        rw [RingEquiv.symm_apply_eq]
        exact hx.symm
      rw [this]; exact ih


theorem finite_ringEquiv (F : Type) [Field F] [Finite F] : Finite (F ≃+* F) :=
  Finite.of_injective (fun σ : F ≃+* F => (σ : F → F)) DFunLike.coe_injective

theorem card_fixF_pow [Finite F] (σ : F ≃+* F) :
    Nat.card (fixF σ) ^ orderOf σ = Nat.card F := by
  have : Finite (F ≃+* F) := finite_ringEquiv F
  have : Fintype (zpowers σ) := Fintype.ofFinite _
  have : Fintype F := Fintype.ofFinite F
  have : Fintype (fixF σ) := Fintype.ofFinite _
  have h1 : Module.finrank (fixF σ) F = Nat.card (zpowers σ) := by
    have := FixedPoints.finrank_eq_card (zpowers σ) F
    rw [Nat.card_eq_fintype_card]
    exact this
  rw [Nat.card_zpowers] at h1
  have h2 := Module.card_eq_pow_finrank (K := fixF σ) (V := F)
  rw [h1] at h2
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact h2.symm


theorem card_fixF_eq [Finite F] (σ : F ≃+* F) {p n : ℕ} (hp : p.Prime) (hF : Nat.card F = p ^ n) :
    ∃ m, Nat.card (fixF σ) = p ^ m ∧ m * orderOf σ = n := by
  have : Finite (F ≃+* F) := finite_ringEquiv F
  have hpos : 0 < orderOf σ := orderOf_pos σ
  have h := card_fixF_pow σ
  rw [hF] at h
  have hd : Nat.card (fixF σ) ∣ p ^ n := by
    rw [← h]; exact dvd_pow_self _ hpos.ne'
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp).1 hd
  refine ⟨m, hm, ?_⟩
  rw [hm, ← pow_mul] at h
  exact Nat.pow_right_injective hp.two_le h

@[expose] def slFixIncl (σ : F ≃+* F) : SL2 (fixF σ) →* SL2 F :=
  Matrix.SpecialLinearGroup.map (fixF σ).subtype

theorem slFixIncl_apply (σ : F ≃+* F) (A : SL2 (fixF σ)) (i j : Fin 2) :
    ((slFixIncl σ A : SL2 F) : Matrix (Fin 2) (Fin 2) F) i j =
      (((A : Matrix (Fin 2) (Fin 2) (fixF σ)) i j : fixF σ) : F) := by
  simp [slFixIncl, Matrix.SpecialLinearGroup.map_apply_coe]

theorem slFixIncl_injective (σ : F ≃+* F) : Function.Injective (slFixIncl σ) := by
  intro A B h
  apply Subtype.ext
  ext i j
  have := congrArg (fun X : SL2 F => (X : Matrix (Fin 2) (Fin 2) F) i j) h
  simpa [slFixIncl_apply] using this

theorem mem_range_slFixIncl (σ : F ≃+* F) (M : SL2 F) :
    M ∈ (slFixIncl σ).range ↔ ∀ i j, σ ((M : Matrix (Fin 2) (Fin 2) F) i j) = (M : Matrix (Fin 2) (Fin 2) F) i j := by
  constructor
  · rintro ⟨A, rfl⟩ i j
    rw [slFixIncl_apply]
    exact mem_fixF.1 ((A : Matrix (Fin 2) (Fin 2) (fixF σ)) i j).2
  · intro h
    let B : Matrix (Fin 2) (Fin 2) (fixF σ) := Matrix.of fun i j => ⟨(M : Matrix (Fin 2) (Fin 2) F) i j, mem_fixF.2 (h i j)⟩
    have hB : B.det = 1 := by
      apply (fixF σ).subtype.injective
      rw [map_one]
      have := M.2
      rw [← this]
      rw [RingHom.map_det]
      congr 1
    let A : SL2 (fixF σ) := ⟨B, hB⟩
    refine ⟨A, ?_⟩
    apply Subtype.ext
    ext i j
    rw [slFixIncl_apply]
    rfl

end Fixed

end CFSG.GH74.GLS.Stage4.Rest.F1Loc
