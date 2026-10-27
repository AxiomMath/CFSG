module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFooteSquare
public import CFSG.Foundations.Basic

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG GorensteinWalter CatalogueSchreierLinearTwo Subgroup
open CFSG.Glauberman.Dickson (h826_pglMap h826_pglMap_mk h826_pglMap_injective)

theorem perfectResidual_eq_of_two_mul {G : Type*} [Group G] [Finite G] {P : Subgroup G}
    (hP : Group.IsPerfect P) (h2 : 2 * Nat.card P = Nat.card G) : perfectResidual G = P := by
  have hidx : P.index = 2 := by
    have h := P.card_mul_index
    rw [← h2, mul_comm 2] at h
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h
  have hcomm : commutator G ≤ P := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [commutatorElement_def, Subgroup.mul_mem_iff_of_index_two hidx,
      Subgroup.mul_mem_iff_of_index_two hidx, Subgroup.mul_mem_iff_of_index_two hidx,
      inv_mem_iff, inv_mem_iff]
    tauto
  show (⨅ n : ℕ, derivedSeries G n) = P
  apply le_antisymm
  · calc (⨅ n : ℕ, derivedSeries G n) ≤ derivedSeries G 1 := iInf_le _ 1
      _ = commutator G := derivedSeries_one G
      _ ≤ P := hcomm
  · apply le_iInf
    intro n
    induction n with
    | zero =>
      rw [derivedSeries_zero]
      exact le_top
    | succ n ih =>
      rw [derivedSeries_succ]
      calc P = ⁅P, P⁆ := (Subgroup.isPerfect_iff.mp hP).symm
        _ ≤ ⁅derivedSeries G n, derivedSeries G n⁆ := Subgroup.commutator_mono ih ih

theorem factorization_two_pgl_psl {j : ℕ} (hj : 1 ≤ j) :
    ((2 * j + 1) * ((2 * j + 1) ^ 2 - 1)).factorization 2 =
      ((2 * j + 1) ^ 2 * (((2 * j + 1) ^ 2) ^ 2 - 1) / 2).factorization 2 := by
  have h1 : (2 * j + 1) ^ 2 - 1 = 4 * j * (j + 1) := Nat.sub_eq_of_eq_add (by ring)
  have h2 : ((2 * j + 1) ^ 2) ^ 2 - 1 = 4 * j * (j + 1) * (4 * j * (j + 1) + 2) :=
    Nat.sub_eq_of_eq_add (by ring)
  have h3 : (2 * j + 1) ^ 2 * (4 * j * (j + 1) * (4 * j * (j + 1) + 2)) / 2 =
      (2 * j + 1) ^ 2 * (4 * j * (j + 1)) * (2 * (j * (j + 1)) + 1) := by
    rw [show (2 * j + 1) ^ 2 * (4 * j * (j + 1) * (4 * j * (j + 1) + 2)) =
      2 * ((2 * j + 1) ^ 2 * (4 * j * (j + 1)) * (2 * (j * (j + 1)) + 1)) by ring]
    exact Nat.mul_div_cancel_left _ two_pos
  rw [h1, h2, h3]
  have hX : 4 * j * (j + 1) ≠ 0 := Nat.mul_ne_zero (Nat.mul_ne_zero (by norm_num) (by omega))
    (by omega)
  have hr : 2 * j + 1 ≠ 0 := by omega
  have hr2 : (2 * j + 1) ^ 2 ≠ 0 := pow_ne_zero _ hr
  have hm : 2 * (j * (j + 1)) + 1 ≠ 0 := by omega
  have hodd1 : (2 * j + 1).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (Nat.two_not_dvd_two_mul_add_one j)
  have hodd2 : (2 * (j * (j + 1)) + 1).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (Nat.two_not_dvd_two_mul_add_one _)
  rw [Nat.factorization_mul hr hX, Nat.factorization_mul (Nat.mul_ne_zero hr2 hX) hm,
    Nat.factorization_mul hr2 hX, Nat.factorization_pow]
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, hodd1, hodd2]
  ring

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem pgl2FieldAut_pglMap {σ : F ≃+* F} {K₀ : Subfield F} (hK₀ : ∀ x, x ∈ K₀ ↔ σ x = x)
    (y : PGL2 K₀) : pgl2FieldAut F σ (h826_pglMap K₀.subtype y) = h826_pglMap K₀.subtype y := by
  obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective y
  rw [h826_pglMap_mk, pgl2FieldAut_mk]
  congr 1
  ext i j
  simp only [Matrix.GeneralLinearGroup.map, RingEquiv.toRingHom_eq_coe, Units.coe_map]
  exact (hK₀ _).mp (Subtype.mem _)

theorem card_fieldCent_eq {σ : F ≃+* F} {K₀ : Subfield F} (hK₀ : ∀ x, x ∈ K₀ ↔ σ x = x)
    (h90 : ∀ c : F, c * σ c = 1 → ∃ y : Fˣ, (y : F) / σ y = c) (hσσ : ∀ x, σ (σ x) = x)
    (hcard : Nat.card F = Nat.card K₀ ^ 2) (hodd : IsOddPrimePower (Nat.card F)) :
    Nat.card (fieldCent σ) = Nat.card (PGL2 K₀) := by
  refine le_antisymm (card_fieldCent_le hK₀ h90 hσσ) ?_
  have hle : (h826_pglMap K₀.subtype).range ≤
      (fieldCent σ).map Matrix.ProjectiveSpecialLinearGroup.toPGL := by
    rintro _ ⟨y, rfl⟩
    have hfix := pgl2FieldAut_pglMap hK₀ y
    obtain ⟨z, hz⟩ := mem_psl2Range_of_pgl2FieldAut_fixed hK₀ h90 hσσ hcard hodd hfix
    refine ⟨z, ?_, hz⟩
    show psl2FieldAut F σ z = z
    apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
    rw [psl2FieldAut_toPGL, hz, hfix]
  calc Nat.card (PGL2 K₀) = Nat.card (h826_pglMap K₀.subtype).range :=
        Nat.card_congr
          (MonoidHom.ofInjective (h826_pglMap_injective _ K₀.subtype_injective)).toEquiv
    _ ≤ Nat.card ((fieldCent σ).map Matrix.ProjectiveSpecialLinearGroup.toPGL) :=
        Subgroup.card_le_of_le hle
    _ = Nat.card (fieldCent σ) :=
        Subgroup.card_map_of_injective Matrix.ProjectiveSpecialLinearGroup.toPGL_injective

theorem eq_one_or_eq_of_fixes {σ : F ≃+* F} (hσ1 : σ ≠ 1) {K₀ : Subfield F}
    (hK₀ : ∀ x, x ∈ K₀ ↔ σ x = x) (hcard : Nat.card F = Nat.card K₀ ^ 2) {τ : F ≃+* F}
    (hτ : ∀ x ∈ K₀, τ x = x) : τ = 1 ∨ τ = σ := by
  have hfin : Module.finrank K₀ F = 2 := by
    have h := Module.natCard_eq_pow_finrank (K := K₀) (V := F)
    rw [hcard] at h
    exact (Nat.pow_right_injective (Finite.one_lt_card (α := K₀)) h).symm
  have hGal : Nat.card (F ≃ₐ[K₀] F) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, hfin]
  let τA : F ≃ₐ[K₀] F := { toRingEquiv := τ, commutes' := fun x => hτ x x.2 }
  let σA : F ≃ₐ[K₀] F := { toRingEquiv := σ, commutes' := fun x => (hK₀ x).mp x.2 }
  have hσA : σA ≠ 1 := fun h => hσ1 (by ext x; exact DFunLike.congr_fun h x)
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : F ≃ₐ[K₀] F)).mp hGal
  by_cases hτ1 : τA = 1
  · left
    ext x
    exact DFunLike.congr_fun hτ1 x
  · right
    have h := (hy τA hτ1).trans (hy σA hσA).symm
    ext x
    exact DFunLike.congr_fun h x

private def fcUpper {K : Type*} [CommRing K] (t : K) : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two]⟩

private def fcLower {K : Type*} [CommRing K] (t : K) : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, 0; t, 1], by simp [Matrix.det_fin_two]⟩

omit [Finite F] in
theorem exists_scalar_of_fixes {K₀ : Subfield F} (M : GL (Fin 2) F) (τ : F ≃+* F)
    (S : Matrix.SpecialLinearGroup (Fin 2) K₀)
    (h : semilinearAction F (SemidirectProduct.inl (Matrix.ProjGenLinGroup.mk M) *
      SemidirectProduct.inr τ) (psl2Sub K₀ (S : PSL2 K₀)) = psl2Sub K₀ (S : PSL2 K₀)) :
    ∃ c : F, c ≠ 0 ∧ ∀ i j : Fin 2,
      ((M : Matrix (Fin 2) (Fin 2) F) i 0 * τ ((S : Matrix (Fin 2) (Fin 2) K₀) 0 j : F) +
        (M : Matrix (Fin 2) (Fin 2) F) i 1 * τ ((S : Matrix (Fin 2) (Fin 2) K₀) 1 j : F)) * c =
      ((S : Matrix (Fin 2) (Fin 2) K₀) i 0 : F) * (M : Matrix (Fin 2) (Fin 2) F) 0 j +
        ((S : Matrix (Fin 2) (Fin 2) K₀) i 1 : F) * (M : Matrix (Fin 2) (Fin 2) F) 1 j := by
  have h1 := congrArg Matrix.ProjectiveSpecialLinearGroup.toPGL h
  rw [map_mul, MulAut.mul_apply, semilinearAction_inl, semilinearAction_inr, toPGL_pglAction,
    psl2FieldAut_toPGL, toPGL_psl2Sub, Matrix.ProjectiveSpecialLinearGroup.toPGL_mk,
    h826_pglMap_mk, pgl2FieldAut_mk, mul_inv_eq_iff_eq_mul, ← map_mul, ← map_mul] at h1
  obtain ⟨c, hc⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp h1
  refine ⟨c, c.ne_zero, fun i j => ?_⟩
  have := congrArg (fun C : GL (Fin 2) F => (C : Matrix (Fin 2) (Fin 2) F) i j) hc
  simp [Matrix.GeneralLinearGroup.map, Matrix.scalar_apply, Matrix.diagonal_apply,
    Matrix.mul_apply, Fin.sum_univ_two] at this
  exact this

theorem eq_of_fixes_psl2Sub {σ : F ≃+* F} (hσ1 : σ ≠ 1) {K₀ : Subfield F}
    (hK₀ : ∀ x, x ∈ K₀ ↔ σ x = x) (hcard : Nat.card F = Nat.card K₀ ^ 2) (x : PGammaL2 F)
    (hx : ∀ g : PSL2 K₀, semilinearAction F x (psl2Sub K₀ g) = psl2Sub K₀ g) :
    x = 1 ∨ x = SemidirectProduct.inr σ := by
  obtain ⟨M, hM⟩ := Matrix.ProjGenLinGroup.mk_surjective x.left
  have hxe : x = SemidirectProduct.inl (Matrix.ProjGenLinGroup.mk M) *
      SemidirectProduct.inr x.right := by
    rw [hM]
    exact (SemidirectProduct.inl_left_mul_inr_right x).symm
  have key := fun S : Matrix.SpecialLinearGroup (Fin 2) K₀ =>
    exists_scalar_of_fixes M x.right S (by rw [← hxe]; exact hx _)
  have hdet := M.det_ne_zero
  rw [Matrix.det_fin_two] at hdet
  obtain ⟨c₁, -, h₁⟩ := key (fcUpper 1)
  have u00 := h₁ 0 0
  have u01 := h₁ 0 1
  have u10 := h₁ 1 0
  have u11 := h₁ 1 1
  simp [fcUpper] at u00 u01 u10 u11
  have hc₁ : c₁ = 1 := by
    by_contra hne
    have hne' : c₁ - 1 ≠ 0 := sub_ne_zero.mpr hne
    have h10 : (M : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
      have : (M : Matrix (Fin 2) (Fin 2) F) 1 0 * (c₁ - 1) = 0 := by linear_combination u10
      exact (mul_eq_zero.mp this).resolve_right hne'
    have h00 : (M : Matrix (Fin 2) (Fin 2) F) 0 0 = 0 := by
      have : (M : Matrix (Fin 2) (Fin 2) F) 0 0 * (c₁ - 1) = 0 := by
        linear_combination u00 + h10
      exact (mul_eq_zero.mp this).resolve_right hne'
    apply hdet
    rw [h00, h10]
    ring
  subst hc₁
  have h10 : (M : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by linear_combination -u00
  have h11 : (M : Matrix (Fin 2) (Fin 2) F) 1 1 = (M : Matrix (Fin 2) (Fin 2) F) 0 0 := by
    linear_combination -u01
  obtain ⟨c₂, -, h₂⟩ := key (fcLower 1)
  have l00 := h₂ 0 0
  have l01 := h₂ 0 1
  simp [fcLower] at l00 l01
  have hc₂ : c₂ = 1 := by
    by_contra hne
    have hne' : c₂ - 1 ≠ 0 := sub_ne_zero.mpr hne
    have h01 : (M : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
      have : (M : Matrix (Fin 2) (Fin 2) F) 0 1 * (c₂ - 1) = 0 := by linear_combination l01
      exact (mul_eq_zero.mp this).resolve_right hne'
    have h00 : (M : Matrix (Fin 2) (Fin 2) F) 0 0 = 0 := by
      have : (M : Matrix (Fin 2) (Fin 2) F) 0 0 * (c₂ - 1) = 0 := by
        linear_combination l00 - h01 * c₂
      exact (mul_eq_zero.mp this).resolve_right hne'
    apply hdet
    rw [h00, h10]
    ring
  subst hc₂
  have h01 : (M : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by linear_combination l00
  have hM00 : (M : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
    intro h
    apply hdet
    rw [h, h10]
    ring
  have hMone : Matrix.ProjGenLinGroup.mk M = 1 := by
    rw [← map_one (Matrix.ProjGenLinGroup.mk (n := Fin 2) (R := F)),
      Matrix.ProjGenLinGroup.mk_eq_mk_iff]
    refine ⟨Units.mk0 _ (inv_ne_zero hM00), Matrix.GeneralLinearGroup.ext fun i j => ?_⟩
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.scalar_apply, Matrix.mul_apply, Fin.sum_univ_two, h10, h01, h11, hM00]
  have hτ : ∀ t ∈ K₀, x.right t = t := by
    intro t ht
    obtain ⟨c, -, h⟩ := key (fcUpper ⟨t, ht⟩)
    have e00 := h 0 0
    have e01 := h 0 1
    simp [fcUpper, h10, h01, h11] at e00 e01
    have hc : c = 1 := by
      have : (M : Matrix (Fin 2) (Fin 2) F) 0 0 * (c - 1) = 0 := by linear_combination e00
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hM00)
    subst hc
    have : (M : Matrix (Fin 2) (Fin 2) F) 0 0 * (x.right t - t) = 0 := by
      linear_combination e01
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hM00)
  rcases eq_one_or_eq_of_fixes hσ1 hK₀ hcard hτ with h | h
  · left
    rw [hxe, hMone, h, map_one, map_one, mul_one]
  · right
    rw [hxe, hMone, h, map_one, one_mul]

end CFSG.ComponentClassification.AutL2Facts
