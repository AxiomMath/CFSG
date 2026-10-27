module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM12Diag
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM12Final

public section

namespace CFSG.LocalAnalysis.GLTheoremA.SFM12

open Matrix CFSG.Open

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2]

theorem frob_apply4 (x : F) : (iterateFrobenius F 2 2 : F →+* F) x = x ^ 4 := by
  rw [frob_eq]
  norm_num

theorem map_frob4 (N : Matrix (Fin 6) (Fin 6) F) :
    N.map (iterateFrobenius F 2 2 : F →+* F) = N.map (fun x : F => x ^ 4) := by
  ext i j
  simp only [Matrix.map_apply]
  exact frob_apply4 _

theorem pow16_eq [Finite F] (hF : Nat.card F = 16) (x : F) : x ^ 16 = x := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = 16 := by rw [← Nat.card_eq_fintype_card, hF]
  have h := FiniteField.pow_card x
  rw [hcard] at h
  exact h

theorem unit_of_orthoEigen {f : Fin 6 → Fin 6 → F}
    (hf : ∀ i k, herm (f i) (f k) = if i = k then 1 else 0) :
    ((Matrix.of fun r c => f c r).map (fun x : F => x ^ 4))ᵀ * (Matrix.of fun r c => f c r) = 1 := by
  ext c c'
  rw [Matrix.mul_apply, Matrix.one_apply]
  have h := hf c c'
  unfold herm at h
  simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply] using h

theorem det_pow_five_of_unit {V : Matrix (Fin 6) (Fin 6) F}
    (hV : (V.map (fun x : F => x ^ 4))ᵀ * V = 1) : V.det ^ 5 = 1 := by
  have h1 := congrArg Matrix.det hV
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h1
  have h2 : (V.map (fun x : F => x ^ 4)).det = V.det ^ 4 := by
    have hm := RingHom.map_det (iterateFrobenius F 2 2 : F →+* F) V
    rw [frob_apply4, RingHom.mapMatrix_apply, map_frob4] at hm
    exact hm.symm
  rw [h2] at h1
  have h3 : V.det ^ 5 = V.det ^ 4 * V.det := by ring
  rw [h3]
  exact h1

theorem exists_basis_det_one {M : Matrix (Fin 6) (Fin 6) F}
    (hU : (M.map (fun x : F => x ^ 4))ᵀ * M = 1) (hx16 : ∀ x : F, x ^ 16 = x) {ζ : F}
    (hζ5 : ζ ^ 5 = 1) (hζ1 : ζ ≠ 1) (hM5 : M ^ 5 = 1) :
    ∃ f : Fin 6 → Fin 6 → F, OrthoEigen M ζ f ∧ (Matrix.of fun r c => f c r).det = 1 := by
  obtain ⟨f0, hf0⟩ := exists_OrthoEigen hU hx16 hζ5 hζ1 hM5 6 le_rfl
  set V : Matrix (Fin 6) (Fin 6) F := Matrix.of fun r c => f0 c r with hVdef
  have hV : (V.map (fun x : F => x ^ 4))ᵀ * V = 1 := unit_of_orthoEigen hf0.2
  have hδ5 : V.det ^ 5 = 1 := det_pow_five_of_unit hV
  have hδ0 : V.det ≠ 0 := by
    intro h0
    rw [h0] at hδ5
    norm_num at hδ5
  set c : F := V.det⁻¹ with hc
  have hc5 : c ^ 5 = 1 := by
    rw [hc, inv_pow, hδ5, inv_one]
  set s : Fin 6 → F := fun k => if k = 0 then c else 1 with hs
  have hs5 : ∀ k, s k ^ 5 = 1 := by
    intro k
    simp only [hs]
    split_ifs
    · exact hc5
    · simp
  refine ⟨fun k => s k • f0 k, ⟨?_, ?_⟩, ?_⟩
  · intro i
    obtain ⟨j, hj⟩ := hf0.1 i
    refine ⟨j, ?_⟩
    dsimp only
    rw [Matrix.mulVec_smul, hj, smul_comm]
  · intro i k
    dsimp only
    rw [herm_smul_left, herm_smul_right, hf0.2 i k]
    by_cases hik : i = k
    · subst hik
      rw [if_pos rfl, mul_one]
      linear_combination hs5 i
    · simp [hik]
  · show (Matrix.of fun r c' => (s c' • f0 c') r).det = 1
    have hVs : (Matrix.of fun r c' => (s c' • f0 c') r) = V * Matrix.diagonal s := by
      ext r c'
      simp [hVdef, Matrix.mul_diagonal, mul_comm]
    have hprod : ∏ k, s k = c := by
      simp [hs, Fin.prod_univ_succ]
    rw [hVs, Matrix.det_mul, Matrix.det_diagonal, hprod, hc]
    exact mul_inv_cancel₀ hδ0

theorem conj_diag_of_orthoEigen [Finite F] (hF : Nat.card F = (2 ^ 2) ^ 2)
    {g : ↥(StatedSU 6 (2 ^ 2) F)} {ζ : F} {f : Fin 6 → Fin 6 → F}
    (hf : OrthoEigen (g : GL (Fin 6) F).val ζ f) (hdet : (Matrix.of fun r c => f c r).det = 1) :
    ∃ P : ↥(StatedSU 6 (2 ^ 2) F), ∃ d : Fin 6 → F,
      ((P * g * P⁻¹ : ↥(StatedSU 6 (2 ^ 2) F)) : GL (Fin 6) F).val = Matrix.diagonal d := by
  have hx16 : ∀ x : F, x ^ 16 = x := pow16_eq (by rw [hF]; norm_num)
  choose jj hjj using hf.1
  set M : Matrix (Fin 6) (Fin 6) F := (g : GL (Fin 6) F).val with hMdef
  set V : Matrix (Fin 6) (Fin 6) F := Matrix.of fun r c => f c r with hVdef
  have hV : (V.map (fun x : F => x ^ 4))ᵀ * V = 1 := unit_of_orthoEigen hf.2
  set W : Matrix (Fin 6) (Fin 6) F := (V.map (fun x : F => x ^ 4))ᵀ with hWdef
  have hWV : W * V = 1 := hV
  have hVW : V * W = 1 := mul_eq_one_comm.1 hV
  have hVσφ : (V.map (fun x : F => x ^ 4)).map (iterateFrobenius F 2 2 : F →+* F) = V := by
    ext i j
    simp only [Matrix.map_apply, frob_apply4]
    rw [← pow_mul, show 4 * 4 = 16 from rfl, hx16]
  have hWφ : W.map (iterateFrobenius F 2 2 : F →+* F) = Vᵀ := by
    rw [hWdef, Matrix.transpose_map, hVσφ]
  have hdetW : W.det = 1 := by
    have h := congrArg Matrix.det hWV
    rw [Matrix.det_mul, hdet, mul_one, Matrix.det_one] at h
    exact h
  have hPmSU : (Units.mk W V hWV hVW : GL (Fin 6) F) ∈ StatedSU 6 (2 ^ 2) F := by
    rw [mem_SU_iff hF]
    simp only [Units.val_mk]
    exact ⟨hdetW, by rw [hWφ, Matrix.transpose_transpose]; exact hVW⟩
  obtain ⟨P, hPdef⟩ : ∃ P : ↥(StatedSU 6 (2 ^ 2) F), (P : GL (Fin 6) F) = Units.mk W V hWV hVW :=
    ⟨⟨Units.mk W V hWV hVW, hPmSU⟩, rfl⟩
  have hMV : M * V = V * Matrix.diagonal (fun k => ζ ^ jj k) := by
    ext r k
    have h := congrFun (hjj k) r
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
    rw [Matrix.mul_diagonal]
    simp only [Matrix.mul_apply, hVdef, Matrix.of_apply]
    linear_combination h
  have hinv : ((Units.mk W V hWV hVW)⁻¹ : GL (Fin 6) F).val = V := rfl
  refine ⟨P, fun k => ζ ^ jj k, ?_⟩
  show ((P : GL (Fin 6) F) * (g : GL (Fin 6) F) * (P : GL (Fin 6) F)⁻¹).val = _
  rw [hPdef, Units.val_mul, Units.val_mul, hinv]
  calc W * M * V = W * (M * V) := Matrix.mul_assoc _ _ _
    _ = W * (V * Matrix.diagonal (fun k => ζ ^ jj k)) := by rw [hMV]
    _ = (W * V) * Matrix.diagonal (fun k => ζ ^ jj k) := (Matrix.mul_assoc _ _ _).symm
    _ = Matrix.diagonal (fun k => ζ ^ jj k) := by rw [hWV, Matrix.one_mul]

theorem unitaryDiagFact_holds : UnitaryDiagFact := by
  intro F _ _ _ _ hF g hg5
  have hF16 : Nat.card F = 16 := by rw [hF]; norm_num
  have hx16 : ∀ x : F, x ^ 16 = x := pow16_eq hF16
  obtain ⟨ζ, hζ5, hζ1⟩ := exists_zeta hF16
  have hU : ((g : GL (Fin 6) F).val.map (fun x : F => x ^ 4))ᵀ * (g : GL (Fin 6) F).val = 1 := by
    have h := ((mem_SU_iff hF (g : GL (Fin 6) F)).1 g.2).2
    rw [map_frob4] at h
    exact h
  have hM5 : (g : GL (Fin 6) F).val ^ 5 = 1 := by
    have h := congrArg (fun x : ↥(StatedSU 6 (2 ^ 2) F) => ((x : GL (Fin 6) F)).val) hg5
    simpa [Units.val_pow_eq_pow_val] using h
  obtain ⟨f, hf, hdet⟩ := exists_basis_det_one hU hx16 hζ5 hζ1 hM5
  exact conj_diag_of_orthoEigen hF hf hdet

end CFSG.LocalAnalysis.GLTheoremA.SFM12
