module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog516CL4Diag
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4DarbouxL
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdOm8Fac
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.ComponentClassification.GSThmB.Cent516

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.CatFactsL4U4 InvClassL TBlocks HBlocks Blocks StabL

variable {K : Type} [Field K]

theorem graph_not_inner [Finite K] (A : GL (Fin 4) K) :
    conjAut 4 K A * dualAut 4 K ∉ OuterAutomorphisms.inner (projectiveSL 4 K) := by
  intro h
  obtain ⟨X, hX⟩ := OddSelector.exists_conjAut_of_mem_inner h
  have h1 : conjAut 4 K (SpecialLinearGroup.toGL X) =
      conjAut 4 K A * fieldAut 4 K 1 * dualAut 4 K ^ 1 := by
    rw [map_one, mul_one, pow_one, ← hX]
  obtain ⟨-, h0, -⟩ := OddSelector.eq_of_conjAut_eq_normalForm (by norm_num) le_rfl h1
  exact absurd h0 one_ne_zero

theorem fixed_of_form {A P : GL (Fin 4) K} (s : SpecialLinearGroup (Fin 4) K)
    (hs : (s : Matrix (Fin 4) (Fin 4) K)ᵀ * ((P : Matrix (Fin 4) (Fin 4) K)ᵀ *
      ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * P) * s =
        (P : Matrix (Fin 4) (Fin 4) K)ᵀ * ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          P) :
    (conjAut 4 K A * dualAut 4 K) (conjAut 4 K P (proj 4 K s)) =
      conjAut 4 K P (proj 4 K s) := by
  rw [conjAut_proj]
  apply conjAut_dualAut_proj_of_transpose_mul_mul
  rw [coe_slConjugation]
  exact conj_transpose_mul_mul (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]) hs

@[expose] def sbd (a b : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 4) (Fin 4) K :=
  !![a 0 0, 0, a 0 1, 0; 0, b 0 0, 0, b 0 1; a 1 0, 0, a 1 1, 0; 0, b 1 0, 0, b 1 1]

theorem sbd_mul (a b a' b' : Matrix (Fin 2) (Fin 2) K) :
    sbd a b * sbd a' b' = sbd (a * a') (b * b') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sbd, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two]

theorem sbd_one : sbd (1 : Matrix (Fin 2) (Fin 2) K) 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sbd]

theorem det_sbd (a b : Matrix (Fin 2) (Fin 2) K) : (sbd a b).det = a.det * b.det := by
  rw [sbd, Matrix.det_succ_row_zero, Matrix.det_fin_two, Matrix.det_fin_two]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]
  ring

theorem sbd_formA (a b : Matrix (Fin 2) (Fin 2) K) (ha : a.det = 1) (hb : b.det = 1) :
    (sbd a b)ᵀ * formA * sbd a b = formA := by
  rw [Matrix.det_fin_two] at ha hb
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sbd, formA, Matrix.mul_apply, Fin.sum_univ_four] <;>
    first
      | ring1
      | linear_combination ha
      | linear_combination -ha
      | linear_combination hb
      | linear_combination -hb

@[expose] def sbdSL : SpecialLinearGroup (Fin 2) K →* SpecialLinearGroup (Fin 4) K where
  toFun a := ⟨sbd (a : Matrix (Fin 2) (Fin 2) K) 1, by rw [det_sbd, a.2, det_one, one_mul]⟩
  map_one' := Subtype.ext sbd_one
  map_mul' a b := Subtype.ext (by
    change sbd _ 1 = sbd _ 1 * sbd _ 1
    rw [sbd_mul, Matrix.one_mul]
    rfl)

theorem coe_sbdSL (a : SpecialLinearGroup (Fin 2) K) :
    ((sbdSL a : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      sbd (a : Matrix (Fin 2) (Fin 2) K) 1 := rfl

theorem sbd_order (h2 : (2 : K) ≠ 0) : orderOf (proj 4 K (sbdSL jSL)) = 4 := by
  have hx2 : proj 4 K (sbdSL jSL) ^ 2 = proj 4 K (sbdSL negOne2) := by
    rw [← map_pow, ← map_pow, jSL_sq]
  refine orderOf_eq_prime_pow (p := 2) (n := 1) ?_ ?_
  · rw [pow_one, hx2]
    refine proj_ne_one_of_diag (i := 0) (j := 1) ?_
    rw [coe_sbdSL]
    simp [sbd, negOne2]
    intro h
    apply h2
    linear_combination -h
  · rw [show 2 ^ (1 + 1) = 2 * 2 from rfl, pow_mul, hx2, ← map_pow, ← map_pow, negOne2_sq,
      map_one, map_one]

@[expose] def cyc : Matrix (Fin 4) (Fin 4) K := !![0, 0, 1, 0; 1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1]

@[expose] def cyc' : Matrix (Fin 4) (Fin 4) K :=
  !![0, 0, -1, 0; 1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 0, 1]

@[expose] def eOne : Matrix (Fin 4) (Fin 4) K :=
  !![-1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, 1]

theorem sym_mats (d : K) :
    cyc.det = (1 : K) ∧ (cyc' : Matrix (Fin 4) (Fin 4) K).det = 1 ∧
      (cyc : Matrix (Fin 4) (Fin 4) K) * cyc * cyc = 1 ∧
      (cyc' : Matrix (Fin 4) (Fin 4) K) * cyc' * cyc' = 1 ∧
      (cyc' : Matrix (Fin 4) (Fin 4) K) = eOne * cyc ∧
      (eOne : Matrix (Fin 4) (Fin 4) K) * eOne = 1 ∧
      cycᵀ * diagonal ![1, 1, 1, d] * cyc = diagonal ![1, 1, 1, d] ∧
      cyc'ᵀ * diagonal ![1, 1, 1, d] * cyc' = diagonal ![1, 1, 1, d] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [cyc, Matrix.det_succ_row_zero]
    simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]
  · rw [cyc', Matrix.det_succ_row_zero]
    simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]
  all_goals
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cyc, cyc', eOne, Matrix.mul_apply, Fin.sum_univ_four, diagonal]

variable {Y : Type} [Group Y] [Finite K] {p f : ℕ}

theorem graph_outer (e : Y ⧸ center Y ≃* projectiveSL 4 K) (α : MulAut Y) {A : GL (Fin 4) K}
    (hα' : MulAut.congr e (barAut α) = conjAut 4 K A * dualAut 4 K) :
    ∀ x, barAut α ≠ MulAut.conj x := fun x h =>
  graph_not_inner A (hα' ▸ (inner_iff_congr e α).mp ⟨x, h⟩)

omit [Finite K] in
theorem inv_transpose_of {A : GL (Fin 4) K} {s : K}
    (hA : (A : Matrix (Fin 4) (Fin 4) K)ᵀ = s • (A : Matrix (Fin 4) (Fin 4) K))
    (hs : s * s = 1) :
    ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ =
      s • ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
  set R := ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
  have hAR : (A : Matrix (Fin 4) (Fin 4) K) * R = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hRA : R * (A : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h1 : Rᵀ * (A : Matrix (Fin 4) (Fin 4) K)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, hAR, Matrix.transpose_one]
  rw [hA, Matrix.mul_smul] at h1
  calc Rᵀ = Rᵀ * ((A : Matrix (Fin 4) (Fin 4) K) * R) := by rw [hAR, Matrix.mul_one]
    _ = s • ((s • (Rᵀ * (A : Matrix (Fin 4) (Fin 4) K))) * R) := by
        rw [Matrix.smul_mul, smul_smul, hs, one_smul, Matrix.mul_assoc]
    _ = s • R := by rw [h1, Matrix.one_mul]

variable [Finite Y] (hZ : Nat.card (center Y) = 2) (hp : p.Prime) (hp2 : p ≠ 2)
  (hK : Nat.card K = p ^ f) (h3 : p ^ f = 3) (e : Y ⧸ center Y ≃* projectiveSL 4 K)
  (α : MulAut Y) {A : GL (Fin 4) K}
  (hα' : MulAut.congr e (barAut α) = conjAut 4 K A * dualAut 4 K)

include hZ hp hp2 hK h3 hα' in
theorem graph_alt3 (hA : (A : Matrix (Fin 4) (Fin 4) K)ᵀ = -A) : Concl516 Y α (p ^ f) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (LieType.Steinberg.ringChar_ne_two_of_card_eq_pow
    hp hp2 hK)
  have hR := inv_transpose_of (A := A) (s := -1) (by rw [hA, neg_one_smul]) (by norm_num)
  rw [neg_one_smul] at hR
  obtain ⟨P, hPu, hPR⟩ := exists_transpose_mul_mul_eq_formA h2 hR
    (Matrix.isUnits_det_units A⁻¹)
  set P' : GL (Fin 4) K := Matrix.nonsingInvUnit P hPu
  set ρ := frameHom e P' sbdSL
  have hfix : ∀ g, barAut α (ρ g) = ρ g := fun g =>
    barAut_symm_fixed e α hα' (fixed_of_form (sbdSL g) (by
      change (sbd (g : Matrix (Fin 2) (Fin 2) K) 1)ᵀ * (Pᵀ * _ * P) * sbd _ 1 = Pᵀ * _ * P
      rw [hPR]
      exact sbd_formA _ _ g.2 det_one))
  have h4 : 4 ∣ Nat.card ρ.range := by
    have hmem : ((conjAut 4 K P').trans e.symm) (proj 4 K (sbdSL jSL)) ∈ ρ.range := ⟨_, rfl⟩
    have := orderOf_dvd_natCard (⟨_, hmem⟩ : ρ.range)
    rwa [Subgroup.orderOf_mk, MulEquiv.orderOf_eq, sbd_order h2] at this
  exact concl516_outer hZ α ρ hfix (Or.inr ⟨h3, _, elementary_good hp hp2 hK 2⟩)
    (graph_outer e α hα') h4

include hZ hp hp2 hK h3 hα' in
theorem graph_sym3 (hA : (A : Matrix (Fin 4) (Fin 4) K)ᵀ = A) : Concl516 Y α (p ^ f) := by
  classical
  have hK2 := LieType.Steinberg.ringChar_ne_two_of_card_eq_pow hp hp2 hK
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK2
  have hodd : Odd (Nat.card K) := by rw [hK]; exact (hp.odd_of_ne_two hp2).pow
  set R := ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hRdef
  have hRt : Rᵀ = R := by
    have := inv_transpose_of (A := A) (s := 1) (by rw [hA, one_smul]) (by norm_num)
    rwa [one_smul] at this
  set Q : QuadraticForm K (Fin 4 → K) := (toBilin' R).toQuadraticMap with hQ
  have hpolar : ∀ x y, QuadraticMap.polar Q x y = 2 * toBilin' R x y := fun x y => by
    rw [hQ, QuadraticMap.polar, LinearMap.BilinMap.toQuadraticMap_apply,
      LinearMap.BilinMap.toQuadraticMap_apply, LinearMap.BilinMap.toQuadraticMap_apply,
      map_add, map_add, LinearMap.add_apply, LinearMap.add_apply]
    have : toBilin' R y x = toBilin' R x y := by
      rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply', dotProduct_mulVec,
        ← mulVec_transpose, hRt, dotProduct_comm]
    rw [this]
    ring
  have hnd : Q.polarBilin.Nondegenerate := by
    have hpB : Q.polarBilin = toBilin' ((2 : K) • R) := by
      refine LinearMap.ext₂ fun x y => ?_
      rw [QuadraticMap.polarBilin_apply_apply, hpolar, map_smul, LinearMap.smul_apply,
        LinearMap.smul_apply, smul_eq_mul]
    rw [hpB]
    refine LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.2 ?_
    rw [det_smul]
    exact mul_ne_zero (pow_ne_zero _ h2) (Matrix.isUnits_det_units A⁻¹).ne_zero
  obtain ⟨eb, heo, hQe⟩ := Catalog7Std.Om8.exists_unit_orthogonal_basis hodd hnd
    (by rw [Module.finrank_fin_fun]; norm_num)
  set b := eb.reindex (finCongr (Module.finrank_fin_fun K)) with hb
  have hbo : ∀ i j : Fin 4, i ≠ j → toBilin' R (b i) (b j) = 0 := fun i j hij => by
    have h := heo ((finCongr (Module.finrank_fin_fun K)).symm i)
      ((finCongr (Module.finrank_fin_fun K)).symm j) (fun h => hij (by simpa using h))
    rw [hpolar] at h
    have h' := (mul_eq_zero.mp h).resolve_left h2
    rwa [hb, Module.Basis.reindex_apply, Module.Basis.reindex_apply]
  have hbu : ∀ i : Fin 4, (i : ℕ) < 3 → toBilin' R (b i) (b i) = 1 := fun i hi => by
    have h := hQe ((finCongr (Module.finrank_fin_fun K)).symm i) (by simpa using hi)
    rw [hQ, LinearMap.BilinMap.toQuadraticMap_apply] at h
    rwa [hb, Module.Basis.reindex_apply]
  set P : GL (Fin 4) K := ⟨(Pi.basisFun K (Fin 4)).toMatrix b, b.toMatrix (Pi.basisFun K (Fin 4)),
    Module.Basis.toMatrix_mul_toMatrix_flip _ _, Module.Basis.toMatrix_mul_toMatrix_flip _ _⟩
  set d := toBilin' R (b 3) (b 3)
  have hG : (P : Matrix (Fin 4) (Fin 4) K)ᵀ * R * P = diagonal ![1, 1, 1, d] := by
    have h1 := LinearMap.BilinForm.toMatrix_mul_basis_toMatrix (Pi.basisFun K (Fin 4)) b
      (toBilin' R)
    rw [LinearMap.BilinForm.toMatrix_basisFun, LinearMap.BilinForm.toMatrix'_toBilin'] at h1
    change ((Pi.basisFun K (Fin 4)).toMatrix b)ᵀ * R * (Pi.basisFun K (Fin 4)).toMatrix b = _
    rw [h1]
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply]
    by_cases hij : i = j
    · subst hij
      rw [diagonal_apply_eq]
      fin_cases i
      all_goals first | exact hbu _ (by decide) | rfl
    · rw [diagonal_apply_ne _ hij]
      exact hbo i j hij
  obtain ⟨hdc, hdc', hc3, hc3', hce, hee, hcG, hcG'⟩ := sym_mats (K := K) d
  set cs : SpecialLinearGroup (Fin 4) K := ⟨cyc, hdc⟩
  set cs' : SpecialLinearGroup (Fin 4) K := ⟨cyc', hdc'⟩
  set τ := (conjAut 4 K P).trans e.symm
  set T : Set (Y ⧸ center Y) := {τ (proj 4 K cs), τ (proj 4 K cs')}
  have hT : ∀ t ∈ T, barAut α t = t := by
    rintro t (rfl | rfl)
    · exact barAut_symm_fixed e α hα' (fixed_of_form cs (by rw [hG]; exact hcG))
    · exact barAut_symm_fixed e α hα' (fixed_of_form cs' (by rw [hG]; exact hcG'))
  have hord3 : ∀ M : SpecialLinearGroup (Fin 4) K,
      (M : Matrix (Fin 4) (Fin 4) K) * M * M = 1 → (M : Matrix (Fin 4) (Fin 4) K) 1 0 ≠ 0 →
        orderOf (τ (proj 4 K M)) = 3 := fun M hM hM10 => by
    rw [MulEquiv.orderOf_eq]
    refine orderOf_eq_prime ?_ (proj_ne_one_of_off (i := 1) (j := 0) (by decide) hM10)
    rw [← map_pow]
    have : M ^ 3 = 1 := Matrix.SpecialLinearGroup.ext _ _ fun i j => by
      rw [Matrix.SpecialLinearGroup.coe_pow, pow_three, ← Matrix.mul_assoc, hM,
        Matrix.SpecialLinearGroup.coe_one]
    rw [this, map_one]
  have hTo : ∀ t ∈ T, Odd (orderOf t) := by
    rintro t (rfl | rfl)
    · rw [hord3 cs hc3 (by simp [cs, cyc])]; decide
    · rw [hord3 cs' hc3' (by simp [cs', cyc'])]; decide
  have h2d : 2 ∣ Nat.card (closure T) := by
    set es : SpecialLinearGroup (Fin 4) K := ⟨eOne, by
      rw [eOne, Matrix.det_succ_row_zero]
      simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]⟩
    have hes : cs' = es * cs := Matrix.SpecialLinearGroup.ext _ _ fun i j => by
      rw [Matrix.SpecialLinearGroup.coe_mul]
      change (cyc' : Matrix (Fin 4) (Fin 4) K) i j = (eOne * cyc : Matrix (Fin 4) (Fin 4) K) i j
      rw [hce]
    have hmem : τ (proj 4 K es) ∈ closure T := by
      have h1 : τ (proj 4 K es) = τ (proj 4 K cs') * (τ (proj 4 K cs))⁻¹ := by
        rw [hes, map_mul, map_mul, mul_inv_cancel_right]
      rw [h1]
      exact mul_mem (subset_closure (Or.inr rfl)) (inv_mem (subset_closure (Or.inl rfl)))
    have hord : orderOf (τ (proj 4 K es)) = 2 := by
      rw [MulEquiv.orderOf_eq]
      refine orderOf_eq_prime ?_ ?_
      · rw [← map_pow]
        have : es ^ 2 = 1 := Matrix.SpecialLinearGroup.ext _ _ fun i j => by
          rw [Matrix.SpecialLinearGroup.coe_pow, pow_two]
          change (eOne * eOne : Matrix (Fin 4) (Fin 4) K) i j = _
          rw [hee]
          rfl
        rw [this, map_one]
      · refine proj_ne_one_of_diag (i := 0) (j := 1) ?_
        change eOne 0 0 ≠ (eOne : Matrix (Fin 4) (Fin 4) K) 1 1
        simp [eOne]
        intro h
        apply h2
        linear_combination -h
    have := orderOf_dvd_natCard (⟨_, hmem⟩ : closure T)
    rwa [Subgroup.orderOf_mk, hord] at this
  obtain ⟨N, hNfix, hNle, hNout, hN4⟩ := concl_odd_outer hZ α hT hTo (graph_outer e α hα')
    (four_dvd_card_closure_odd hTo h2d)
  exact ⟨N, hNfix, Or.inr ⟨h3, hNle⟩, Or.inr (Or.inr ⟨hNout, hN4⟩)⟩

end CFSG.ComponentClassification.GSThmB.Cent516
