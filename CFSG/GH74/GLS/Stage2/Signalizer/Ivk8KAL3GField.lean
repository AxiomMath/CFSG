module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL3Gen
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL3Aut
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KACover
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3GField

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Matrix Subgroup CFSG CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.GH74.GLS.IVK
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.GH74.KGroups.L3Eps
open scoped MatrixGroups

section Lift

variable {F : Type} [Field F]

noncomputable def kaGfθ (σ : F ≃+* F) : SL(3, F) →* SL(3, F) :=
  (SpecialLinearGroup.map σ.toRingHom).comp
    (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 3 F).toMonoidHom

theorem kaGfθ_proj (σ : F ≃+* F) (g : SL(3, F)) :
    (fieldAut 3 F σ * dualAut 3 F) (proj 3 F g) = proj 3 F (kaGfθ σ g) := by
  rw [MulAut.mul_apply, dualAut_proj, fieldAut_proj]
  rfl

theorem coe_kaGfθ (σ : F ≃+* F) (g : SL(3, F)) :
    ((kaGfθ σ g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      ((adjugate (g : Matrix (Fin 3) (Fin 3) F))ᵀ).map σ := by
  simp [kaGfθ, SpecialLinearGroup.map_apply_coe,
    CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut]

end Lift

section Unitary

variable {F : Type} [Field F] [Finite F] {p e : ℕ} [Fact p.Prime] [CharP F p]

theorem kaGfσσ (hF : Nat.card F = (p ^ e) ^ 2) (σ : F ≃+* F) (hσ : ∀ x, σ x = x ^ p ^ e)
    (x : F) : σ (σ x) = x := by
  have h1 : ∀ y, σ y = unitaryInvolution F p e y := fun y => by
    rw [unitaryInvolution_apply]
    exact hσ y
  rw [h1, h1]
  exact unitaryInvolution_involutive hF x

theorem kaGfθ_fix_iff (hF : Nat.card F = (p ^ e) ^ 2) (σ : F ≃+* F) (hσ : ∀ x, σ x = x ^ p ^ e)
    (g : SL(3, F)) :
    kaGfθ σ g = g ↔
      ((g : Matrix (Fin 3) (Fin 3) F).map σ)ᵀ * (g : Matrix (Fin 3) (Fin 3) F) = 1 := by
  have hσσ := kaGfσσ hF σ hσ
  have hdet : (g : Matrix (Fin 3) (Fin 3) F).det = 1 := g.2
  constructor
  · intro h
    have h1 := congrArg (fun x : SL(3, F) => (x : Matrix (Fin 3) (Fin 3) F)) h
    simp only [coe_kaGfθ] at h1
    have h2 : (adjugate (g : Matrix (Fin 3) (Fin 3) F))ᵀ =
        (g : Matrix (Fin 3) (Fin 3) F).map σ := by
      ext i j
      have := congrFun (congrFun h1 i) j
      simp only [Matrix.map_apply] at this
      rw [Matrix.map_apply]
      calc ((adjugate (g : Matrix (Fin 3) (Fin 3) F))ᵀ) i j
          = σ (σ (((adjugate (g : Matrix (Fin 3) (Fin 3) F))ᵀ) i j)) := (hσσ _).symm
        _ = σ ((g : Matrix (Fin 3) (Fin 3) F) i j) := by rw [this]
    have h3 : adjugate (g : Matrix (Fin 3) (Fin 3) F) =
        ((g : Matrix (Fin 3) (Fin 3) F).map σ)ᵀ := by
      rw [← h2, transpose_transpose]
    rw [← h3, adjugate_mul, hdet, one_smul]
  · intro h
    apply Subtype.ext
    rw [coe_kaGfθ]
    have hadj : adjugate (g : Matrix (Fin 3) (Fin 3) F) =
        ((g : Matrix (Fin 3) (Fin 3) F).map σ)ᵀ := by
      rw [← Matrix.inv_eq_left_inv h, Matrix.inv_def, hdet, Ring.inverse_one, one_smul]
    rw [hadj, transpose_transpose]
    ext i j
    simp [hσσ]

omit [Finite F] [Fact p.Prime] [CharP F p] in
theorem suSL_injective (q : ℕ) : Function.Injective (suSL (F := F) q) := by
  intro A B h
  apply Subtype.ext
  apply Units.ext
  have := congrArg (fun x : SL(3, F) => (x : Matrix (Fin 3) (Fin 3) F)) h
  simpa [coe_suSL] using this

theorem kaFix_gfθ_eq_range (hF : Nat.card F = (p ^ e) ^ 2) (σ : F ≃+* F)
    (hσ : ∀ x, σ x = x ^ p ^ e) : kaFix (kaGfθ σ) = (suSL (F := F) (p ^ e)).range := by
  have hσ' : (unitaryInvolution F p e : F ≃+* F) = σ :=
    RingEquiv.ext fun x => by rw [unitaryInvolution_apply, hσ]
  ext g
  rw [mem_kaFix, kaGfθ_fix_iff hF σ hσ]
  constructor
  · intro h
    have hmem : (Matrix.SpecialLinearGroup.toGL g : GL (Fin 3) F) ∈ StatedSU 3 (p ^ e) F := by
      rw [← SUid_eq_statedSU hF 3]
      refine ⟨by simp, ?_⟩
      show ((g : Matrix (Fin 3) (Fin 3) F).map (unitaryInvolution F p e))ᵀ * g = 1
      rw [hσ']
      exact h
    exact ⟨⟨_, hmem⟩, Matrix.SpecialLinearGroup.ext _ _ fun i j => rfl⟩
  · rintro ⟨B, rfl⟩
    have hB : (B : GL (Fin 3) F) ∈ SUid (unitaryInvolution F p e) 3 := by
      rw [SUid_eq_statedSU hF 3]
      exact B.2
    have h2 := hB.2
    change ((B : GL (Fin 3) F).val.map (unitaryInvolution F p e))ᵀ * (B : GL (Fin 3) F).val = 1
      at h2
    rw [hσ'] at h2
    exact h2

theorem kaFix_gfθ_quasisimple (hF : Nat.card F = (p ^ e) ^ 2) (hp2 : p ≠ 2) (σ : F ≃+* F)
    (hσ : ∀ x, σ x = x ^ p ^ e) : CFSG.IsQuasisimple ↥(kaFix (kaGfθ σ)) := by
  have hne : (3, p ^ e) ≠ (3, 2) := by
    intro h
    have h1 : p ^ e = 2 := (Prod.mk.inj h).2
    have h2 : Odd (p ^ e) := ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
    rw [h1] at h2
    exact absurd h2 (by decide)
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    ((MonoidHom.ofInjective (suSL_injective (F := F) (p ^ e))).trans
      (MulEquiv.subgroupCongr (kaFix_gfθ_eq_range hF σ hσ).symm))
    (isQuasisimple_statedSU_of_card hF (le_refl 3) hne).1

end Unitary

section Omega

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem kaGf_fix_of_sq_fix (τ : F ≃+* F) (hτ : Odd (orderOf τ)) (ω : F)
    (h : (τ ^ 2) ω = ω) : τ ω = ω := by
  obtain ⟨k, hk⟩ := hτ
  have h1 : τ ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one τ
  have h2 : τ = (τ ^ 2) ^ (k + 1) := by
    calc τ = τ ^ (2 * k + 1) * τ := by rw [h1, one_mul]
      _ = (τ ^ 2) ^ (k + 1) := by rw [← pow_succ, ← pow_mul]; congr 1
  have hmem : τ ^ 2 ∈ MulAction.stabilizer (F ≃+* F) ω := by
    rw [MulAction.mem_stabilizer_iff]
    exact h
  have h3 := Subgroup.pow_mem _ hmem (k + 1)
  rw [MulAction.mem_stabilizer_iff] at h3
  rw [h2]
  exact h3

omit [Finite F] in
theorem kaGf_fix_of_trace (τ : F ≃+* F) (hτ : Odd (orderOf τ)) {ω : F} (hω0 : ω ≠ 0)
    (hω2 : ω * ω ≠ 1) (h : τ (ω + ω⁻¹) = ω + ω⁻¹) : τ ω = ω := by
  have hu0 : τ ω ≠ 0 := fun h0 => hω0 (τ.injective (by rw [h0, map_zero]))
  rw [map_add, map_inv₀] at h
  have h1 : (τ ω - ω) * (τ ω * ω - 1) = 0 := by
    field_simp at h
    linear_combination h
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact sub_eq_zero.mp h2
  · exfalso
    have h3 : τ ω = ω⁻¹ := eq_inv_of_mul_eq_one_left (sub_eq_zero.mp h2)
    have h4 : (τ ^ 2) ω = ω := by
      rw [pow_two]
      change τ (τ ω) = ω
      rw [h3, map_inv₀, h3, inv_inv]
    have h5 := kaGf_fix_of_sq_fix τ hτ ω h4
    rw [h3] at h5
    apply hω2
    field_simp at h5
    linear_combination -h5

theorem kaGf_exists_omega {q : ℕ} (hF : Nat.card F = q ^ 2) (hq : 2 ≤ q) :
    ∃ ω : F, orderOf ω = q + 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  have hcard : Nat.card Fˣ = q ^ 2 - 1 := by
    rw [Nat.card_units, hF]
  have hdvd : q - 1 ∣ orderOf g := by
    rw [hg, hcard]
    refine ⟨q + 1, ?_⟩
    obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring_nf
    omega
  refine ⟨((g ^ (q - 1) : Fˣ) : F), ?_⟩
  rw [orderOf_units, orderOf_pow_of_dvd (by omega) hdvd, hg, hcard]
  rw [Nat.div_eq_of_eq_mul_right (by omega : 0 < q - 1)]
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  ring_nf
  omega

theorem kaGf_eq_one_of_fixed {q : ℕ} (hF : Nat.card F = q ^ 2) (hq : 2 ≤ q) {ω : F}
    (hω : orderOf ω = q + 1) (τ : F ≃+* F) (hfix : τ ω = ω) : τ = 1 := by
  have hmem : ω ∈ fixedField τ := (mem_fixedField_iff τ ω).mpr hfix
  have ht := fixedField_card_pow τ
  have hω0 : ω ≠ 0 := by
    rintro rfl
    rw [orderOf_zero] at hω
    omega
  have hN : q + 2 ≤ Nat.card (fixedField τ) := by
    have : Fintype (fixedField τ) := Fintype.ofFinite _
    have h0 : (⟨ω, hmem⟩ : fixedField τ) ≠ 0 := fun h0 => hω0 (congrArg Subtype.val h0)
    have h1 := FiniteField.pow_card_sub_one_eq_one (⟨ω, hmem⟩ : fixedField τ) h0
    have h2 : ω ^ (Fintype.card (fixedField τ) - 1) = 1 := by
      have := congrArg (fun z : fixedField τ => (z : F)) h1
      simpa using this
    rw [← Nat.card_eq_fintype_card] at h2
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [hω] at h3
    have h4 := Nat.le_of_dvd (by have := one_lt_card_fixedField τ; omega) h3
    omega
  by_contra hne
  have hm : 2 ≤ orderOf τ := by
    have := orderOf_pos τ
    have : orderOf τ ≠ 1 := fun h => hne (orderOf_eq_one_iff.mp h)
    omega
  have : (q + 2) ^ 2 ≤ q ^ 2 := by
    calc (q + 2) ^ 2 ≤ Nat.card (fixedField τ) ^ 2 := Nat.pow_le_pow_left hN 2
      _ ≤ Nat.card (fixedField τ) ^ orderOf τ := Nat.pow_le_pow_right (by omega) hm
      _ = q ^ 2 := by rw [ht, hF]
  nlinarith

end Omega

section Diag

variable {F : Type} [Field F]

@[expose] noncomputable def kaGfDiag (a : F) (ha : a ≠ 0) : SL(3, F) :=
  ⟨Matrix.diagonal ![a, a⁻¹, 1], by simp [Matrix.det_diagonal, Fin.prod_univ_three, ha]⟩

@[expose] def kaGfPerm : SL(3, F) :=
  ⟨!![0, 1, 0; 0, 0, 1; 1, 0, 0], by simp [Matrix.det_fin_three]⟩

theorem coe_kaGfDiag (a : F) (ha : a ≠ 0) :
    ((kaGfDiag a ha : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = Matrix.diagonal ![a, a⁻¹, 1] :=
  rfl

theorem coe_kaGfPerm :
    ((kaGfPerm : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = !![0, 1, 0; 0, 0, 1; 1, 0, 0] :=
  rfl

theorem trace_kaGfDiag (a : F) (ha : a ≠ 0) :
    Matrix.trace ((kaGfDiag a ha : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = a + a⁻¹ + 1 := by
  rw [coe_kaGfDiag, Matrix.trace_diagonal, Fin.sum_univ_three]
  simp

theorem kaGf_comm_scalar {a : F} (ha : a ≠ 0) (ha1 : a ≠ 1) (ha2 : a * a ≠ 1)
    (T : Matrix (Fin 3) (Fin 3) F)
    (hD : T * ((kaGfDiag a ha : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      ((kaGfDiag a ha : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * T)
    (hP : T * ((kaGfPerm : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      ((kaGfPerm : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * T) :
    ∃ c : F, T = c • (1 : Matrix (Fin 3) (Fin 3) F) := by
  rw [coe_kaGfDiag] at hD
  rw [coe_kaGfPerm] at hP
  have h01 : a⁻¹ - a ≠ 0 := by
    intro h
    apply ha2
    have : a⁻¹ = a := sub_eq_zero.mp h
    calc a * a = a⁻¹ * a := by rw [this]
      _ = 1 := inv_mul_cancel₀ ha
  have h02 : (1 : F) - a ≠ 0 := fun h => ha1 (sub_eq_zero.mp h).symm
  have h12 : (1 : F) - a⁻¹ ≠ 0 := by
    intro h
    apply ha1
    have : a⁻¹ = 1 := (sub_eq_zero.mp h).symm
    simpa using this
  have key : ∀ i j : Fin 3, T i j * (![a, a⁻¹, 1] : Fin 3 → F) j =
      (![a, a⁻¹, 1] : Fin 3 → F) i * T i j := by
    intro i j
    have := congrFun (congrFun hD i) j
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul] using this
  have t01 : T 0 1 = 0 := by
    have h := key 0 1
    simp at h
    have : T 0 1 * (a⁻¹ - a) = 0 := by linear_combination h
    exact (mul_eq_zero.mp this).resolve_right h01
  have t10 : T 1 0 = 0 := by
    have h := key 1 0
    simp at h
    have : T 1 0 * (a - a⁻¹) = 0 := by linear_combination h
    exact (mul_eq_zero.mp this).resolve_right (fun h' => h01 (by linear_combination -h'))
  have t02 : T 0 2 = 0 := by
    have h := key 0 2
    simp at h
    have : T 0 2 * (1 - a) = 0 := by linear_combination h
    exact (mul_eq_zero.mp this).resolve_right h02
  have t20 : T 2 0 = 0 := by
    have h := key 2 0
    simp at h
    have : T 2 0 * (a - 1) = 0 := by linear_combination h
    exact (mul_eq_zero.mp this).resolve_right (fun h' => h02 (by linear_combination -h'))
  have t12 : T 1 2 = 0 := by
    have h := key 1 2
    simp at h
    have : T 1 2 * (1 - a⁻¹) = 0 := by linear_combination h
    exact (mul_eq_zero.mp this).resolve_right h12
  have t21 : T 2 1 = 0 := by
    have h := key 2 1
    simp at h
    have : T 2 1 * (a⁻¹ - 1) = 0 := by linear_combination h
    exact (mul_eq_zero.mp this).resolve_right (fun h' => h12 (by linear_combination -h'))
  have p01 := congrFun (congrFun hP 0) 1
  have p12 := congrFun (congrFun hP 1) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three] at p01 p12
  refine ⟨T 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [t01, t10, t02, t20, t12, t21]
  · exact p01.symm
  · exact p12.symm.trans p01.symm

end Diag

section Rigid

variable {F : Type} [Field F] [Finite F] {p e : ℕ} [Fact p.Prime] [CharP F p]

theorem kaGfDiag_mem (hF : Nat.card F = (p ^ e) ^ 2) (σ : F ≃+* F)
    (hσ : ∀ x, σ x = x ^ p ^ e) {a : F} (ha : a ≠ 0) (ha1 : a ^ (p ^ e + 1) = 1) :
    kaGfDiag a ha ∈ kaFix (kaGfθ σ) := by
  rw [mem_kaFix, kaGfθ_fix_iff hF σ hσ, coe_kaGfDiag]
  have h1 : σ a * a = 1 := by
    rw [hσ, ← pow_succ]
    exact ha1
  have h2 : (σ a)⁻¹ * a⁻¹ = 1 := by
    rw [← mul_inv, h1, inv_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal_apply, h1, h2]

theorem kaGfPerm_mem (hF : Nat.card F = (p ^ e) ^ 2) (σ : F ≃+* F)
    (hσ : ∀ x, σ x = x ^ p ^ e) : (kaGfPerm : SL(3, F)) ∈ kaFix (kaGfθ σ) := by
  rw [mem_kaFix, kaGfθ_fix_iff hF σ hσ, coe_kaGfPerm]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem kaL3_gfield_pure (hF : Nat.card F = (p ^ e) ^ 2) (hp2 : p ≠ 2) (σ : F ≃+* F)
    (hσ : ∀ x, σ x = x ^ p ^ e) : KAAll (fieldAut 3 F σ * dualAut 3 F) := by
  have hLq := kaFix_gfθ_quasisimple hF hp2 σ hσ
  have hker : ∀ z ∈ (proj 3 F).ker, ∀ g : SL(3, F), g * z = z * g := by
    intro z hz g
    rw [ker_proj] at hz
    exact Subgroup.mem_center_iff.mp (scalars_le_center 3 F hz) g
  have hq3 : 3 ≤ p ^ e := by
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    rw [hF] at h1
    have h2 : 1 < p ^ e := by
      by_contra h
      push Not at h
      have : (p ^ e) ^ 2 ≤ 1 ^ 2 := Nat.pow_le_pow_left h 2
      omega
    obtain ⟨k, hk⟩ := ((Fact.out : p.Prime).odd_of_ne_two hp2).pow (n := e)
    omega
  obtain ⟨ω, hω⟩ := kaGf_exists_omega hF (by omega)
  have hωpow : ω ^ (p ^ e + 1) = 1 := by
    rw [← hω]
    exact pow_orderOf_eq_one ω
  have hω0 : ω ≠ 0 := by
    rintro rfl
    rw [orderOf_zero] at hω
    omega
  have hω1 : ω ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hω
    omega
  have hω2 : ω * ω ≠ 1 := by
    intro h
    have h1 : ω ^ 2 = 1 := by rw [pow_two]; exact h
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hω] at h2
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  refine ka_all_of_cover (ka_conj_injective_of_center_bot center_projectiveSL_three_eq_bot)
    (proj 3 F) (proj_surjective 3 F) hker (kaGfθ σ)
    (fun g => kaGfθ_proj σ g) (kaFix (kaGfθ σ)) le_rfl
    (Subgroup.isPerfect_iff.mp hLq.1) (fun g hg => hg) hLq ?_
  intro p' hp' hp'2 β hord _ hfix
  have : Fact p'.Prime := ⟨hp'⟩
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hord) ⟨β, Subgroup.mem_zpowers β⟩
  rw [Subgroup.orderOf_mk] at hm
  have hβ : β ^ (p' ^ m) = 1 := by rw [← hm]; exact pow_orderOf_eq_one β
  refine kaL3_aut_fixing_trivial (Ω := kaFix (kaGfθ σ))
    (fun A τ h => semiSL_fix_of_perfect A τ hLq.1 h)
    (fun T hT => kaGf_comm_scalar hω0 hω1 hω2 T (hT _ (kaGfDiag_mem hF σ hσ hω0 hωpow))
      (hT _ (kaGfPerm_mem hF σ hσ)))
    ?_ ((hp'.odd_of_ne_two hp'2).pow) hβ (fun g hg => hfix _ ⟨g, hg, rfl⟩)
  intro τ hτodd htr
  refine kaGf_eq_one_of_fixed hF (by omega) hω τ (kaGf_fix_of_trace τ hτodd hω0 hω2 ?_)
  have h1 := htr (kaGfDiag ω hω0) (kaGfDiag_mem hF σ hσ hω0 hωpow)
  rw [trace_kaGfDiag, map_add, map_one] at h1
  linear_combination h1

end Rigid

section General

variable {F : Type} [Field F] [Finite F]

theorem kaL3_gfield {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card F = p ^ f) (A : GL (Fin 3) F) (σ : F ≃+* F) (hσ : σ ≠ 1)
    (hα : (conjAut 3 F A * fieldAut 3 F σ * dualAut 3 F) ^ 2 = 1) :
    KAAll (conjAut 3 F A * fieldAut 3 F σ * dualAut 3 F) := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := by
    have := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨hfe, hσpow, H, hH⟩ :=
    odd_linear_graph_field_involution_conjugacy hp hf hK (le_refl 3) A σ hσ hα
  obtain ⟨e, he⟩ : ∃ e, f = 2 * e := ⟨f / 2, by obtain ⟨k, hk⟩ := hfe; omega⟩
  have hF : Nat.card F = (p ^ e) ^ 2 := by rw [hK, he, ← pow_mul, mul_comm]
  have hσe : ∀ x, σ x = x ^ p ^ e := fun x => by
    rw [hσpow x, show f / 2 = e by omega]
  have hK0 := kaL3_gfield_pure hF hp2 σ hσe
  have h := KAAll.of_mulEquiv (conjAut 3 F H : projectiveSL 3 F ≃* projectiveSL 3 F) hK0
  rw [ka_congr_eq_mul_aut] at h
  rw [hH]
  exact h

end General

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
