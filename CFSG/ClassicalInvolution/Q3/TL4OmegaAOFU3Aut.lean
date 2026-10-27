module

public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFU3Orth

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.U3

open Matrix CFSG.ClassicalInvolution.Q3.Q3MFOU4 CFSG.ClassicalInvolution.Q3.Q3PP
  CFSG.ClassicalInvolution.Models CFSG.LieType.Universal.Unitary CFSG.ClassicalInvolution.Q3.Q3NM
  CFSG.ClassicalInvolution.Balance CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalInvolution.Phan
open scoped MatrixGroups

section Field

theorem pow_nine_F9 (a : F9) : a ^ 9 = a := by
  have : Fintype F9 := Fintype.ofFinite F9
  have hcard : Fintype.card F9 = 9 := by
    rw [← Nat.card_eq_fintype_card, card_F9]
    norm_num
  simpa [hcard] using FiniteField.pow_card a

theorem det_map_σ9 (M : Matrix (Fin 3) (Fin 3) F9) : (M.map σ9).det = σ9 M.det := by
  have h := RingHom.map_det (σ9 : F9 →+* F9) M
  rw [RingHom.mapMatrix_apply] at h
  exact h.symm

theorem norm_det_of_unitary {G : Matrix (Fin 3) (Fin 3) F9} (hgu : (G.map σ9)ᵀ * G = 1) :
    σ9 G.det * G.det = 1 := by
  have h := congrArg Matrix.det hgu
  rwa [Matrix.det_mul, Matrix.det_transpose, det_map_σ9, Matrix.det_one] at h

end Field

section Scalars

theorem scalar_of_commute_su3 (B : Matrix (Fin 3) (Fin 3) F9)
    (hB : ∀ x : Su F9 3 1 3, B * suMat x = suMat x * B) :
    ∃ a : F9, B = a • (1 : Matrix (Fin 3) (Fin 3) F9) := by
  have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 3 1 F9 :=
    ⟨Fact.out, le_rfl, by rw [card_F9, ← pow_mul, mul_comm]⟩
  refine CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.eq_smul_one_of_commute h (by norm_num)
    (le_refl 3) B fun y hy => ?_
  have hy' : y ∈ SUid σ9 3 := by
    rw [SUid_eq_statedSU card_F9]
    exact hy
  exact hB ⟨y, hy'⟩

theorem alpha_sq_matrix_three (φ : F9 ≃+* F9) (hφφ : ∀ c, φ (φ c) = c)
    (G Gi X : Matrix (Fin 3) (Fin 3) F9) :
    G * φ.mapMatrix (G * φ.mapMatrix X * Gi) * Gi =
      (G * φ.mapMatrix G) * X * (φ.mapMatrix Gi * Gi) := by
  have hmm : φ.mapMatrix (φ.mapMatrix X) = X := by
    ext i j
    simp [RingEquiv.mapMatrix_apply, hφφ]
  rw [map_mul, map_mul, hmm]
  simp only [Matrix.mul_assoc]

theorem inv_sq_matrix_three (φ : F9 ≃+* F9) (G Gi : Matrix (Fin 3) (Fin 3) F9)
    (hGiG : Gi * G = 1) : (φ.mapMatrix Gi * Gi) * (G * φ.mapMatrix G) = 1 := by
  calc (φ.mapMatrix Gi * Gi) * (G * φ.mapMatrix G)
      = φ.mapMatrix Gi * (Gi * G) * φ.mapMatrix G := by simp only [Matrix.mul_assoc]
    _ = φ.mapMatrix Gi * φ.mapMatrix G := by rw [hGiG, Matrix.mul_one]
    _ = φ.mapMatrix (Gi * G) := (map_mul _ _ _).symm
    _ = 1 := by rw [hGiG, map_one]

theorem sq_scalar_three (α : Su F9 3 1 3 →* Su F9 3 1 3) (hαα : α.comp α = MonoidHom.id _)
    (φ : F9 ≃+* F9) (hφφ : ∀ c, φ (φ c) = c) {G Gi : Matrix (Fin 3) (Fin 3) F9}
    (hGiG : Gi * G = 1)
    (hα : ∀ x, suMat (α x) = G * φ.mapMatrix (suMat x) * Gi) :
    ∃ c : F9, G * φ.mapMatrix G = c • (1 : Matrix (Fin 3) (Fin 3) F9) := by
  refine scalar_of_commute_su3 _ fun x => ?_
  have hx : suMat (α (α x)) = suMat x := by
    have := DFunLike.congr_fun hαα x
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply] at this
    rw [this]
  rw [hα (α x), hα x, alpha_sq_matrix_three φ hφφ] at hx
  have hP := inv_sq_matrix_three φ G Gi hGiG
  have key : ∀ (P Pi X : Matrix (Fin 3) (Fin 3) F9), P * X * Pi = X → Pi * P = 1 →
      P * X = X * P := by
    intro P Pi X h1 h2
    calc P * X = P * X * (Pi * P) := by rw [h2, Matrix.mul_one]
      _ = (P * X * Pi) * P := by simp only [Matrix.mul_assoc]
      _ = X * P := by rw [h1]
  exact key _ _ _ hx hP

theorem sq_bar_eq_one {G : Matrix (Fin 3) (Fin 3) F9} {c : F9} (hgu : (G.map σ9)ᵀ * G = 1)
    (hc : G * G.map σ9 = c • (1 : Matrix (Fin 3) (Fin 3) F9)) : c = 1 := by
  have h1 := congrArg Matrix.det hc
  rw [Matrix.det_mul, det_map_σ9, Matrix.det_smul, Matrix.det_one] at h1
  have h2 := norm_det_of_unitary hgu
  have h3 : c ^ 3 = 1 := by
    rw [Fintype.card_fin] at h1
    linear_combination h2 - h1
  rw [← pow_nine_F9 c, show (9 : ℕ) = 3 * 3 from rfl, pow_mul, h3, one_pow]

end Scalars

section Inner

theorem exists_conj_eq_of_unitary {G Gi : Matrix (Fin 3) (Fin 3) F9} (hGiG : Gi * G = 1)
    (hgu : (G.map σ9)ᵀ * G = 1) :
    ∃ s : Su F9 3 1 3, ∀ x : Su F9 3 1 3, suMat (s * x * s⁻¹) = G * suMat x * Gi := by
  have hGGi : G * Gi = 1 := mul_eq_one_comm.mp hGiG
  have hd0 : G.det ≠ 0 := by
    intro h
    have := congrArg Matrix.det hGiG
    rw [Matrix.det_mul, h, mul_zero, Matrix.det_one] at this
    exact zero_ne_one this
  set d := G.det with hd
  have hN := norm_det_of_unitary hgu
  have hd4 : d ^ 4 = 1 := by
    rw [σ9_apply] at hN
    linear_combination hN
  set l := d ^ 3 with hl
  have hl0 : l ≠ 0 := pow_ne_zero _ hd0
  have hl3 : l ^ 3 = d := by
    rw [hl, ← pow_mul, show 3 * 3 = 9 from rfl, pow_nine_F9]
  have hlN : σ9 l * l = 1 := by
    rw [σ9_apply, hl, ← pow_mul, ← pow_add]
    calc d ^ (3 * 3 + 3) = (d ^ 4) ^ 3 := by rw [← pow_mul]
      _ = 1 := by rw [hd4, one_pow]
  have hM : (l⁻¹ • G).det = 1 := by
    rw [Matrix.det_smul, Fintype.card_fin, inv_pow, hl3, inv_mul_cancel₀ hd0]
  have hMi : (l • Gi) * (l⁻¹ • G) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hl0, one_smul, hGiG]
  have hMi' : (l⁻¹ • G) * (l • Gi) = 1 := mul_eq_one_comm.mp hMi
  have hU : conjTr σ9 (l⁻¹ • G) * (l⁻¹ • G) = 1 := by
    have e : (l⁻¹ • G).map σ9 = σ9 l⁻¹ • G.map σ9 := by
      ext i j
      simp [map_mul]
    show ((l⁻¹ • G).map σ9)ᵀ * (l⁻¹ • G) = 1
    rw [e, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hgu, smul_smul, map_inv₀,
      ← mul_inv, hlN, inv_one, one_smul]
  refine ⟨⟨⟨l⁻¹ • G, l • Gi, hMi', hMi⟩, hM, hU⟩, fun x => ?_⟩
  rw [suMat_mul, suMat_mul]
  show (l⁻¹ • G) * suMat x * (l • Gi) = G * suMat x * Gi
  rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hl0,
    one_smul]

end Inner

section Outer

theorem oddCoreIn_fixed_su3_of_outer
    (ρ : MulAut (Su F9 3 1 3 ⧸ Subgroup.center (Su F9 3 1 3))) (hρ2 : ρ * ρ = 1)
    (hρout : ρ ∉ innSubgroup (Su F9 3 1 3 ⧸ Subgroup.center (Su F9 3 1 3))) :
    oddCoreIn (fixedSubgroup ρ) = ⊥ := by
  classical
  have hρ2' : ∀ x, ρ (ρ x) = x := fun x => by
    have := congrArg (fun f : MulAut (Su F9 3 1 3 ⧸ Subgroup.center (Su F9 3 1 3)) => f x) hρ2
    simpa using this
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨α, g, φ, hθ, hα, hgu, hφ⟩ := su_lift_of_ne (K := F9) (p := 3) (f := 1) card_F9
    (by norm_num) le_rfl (d := 3) (by norm_num) (by decide) _
    (QuotientGroup.mk' (Subgroup.center (Su F9 3 1 3))) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']) ρ
  obtain ⟨hφ', hαα⟩ := hφ hρ2'
  have hρmk : ∀ x : Su F9 3 1 3, ρ (QuotientGroup.mk x) = QuotientGroup.mk (α x) :=
    fun x => (hθ x).symm
  obtain ⟨G, hG⟩ : ∃ G : Matrix (Fin 3) (Fin 3) F9, G = (g : Matrix (Fin 3) (Fin 3) F9) :=
    ⟨_, rfl⟩
  obtain ⟨Gi, hGi⟩ : ∃ Gi : Matrix (Fin 3) (Fin 3) F9,
      Gi = ((g⁻¹ : GL (Fin 3) F9) : Matrix (Fin 3) (Fin 3) F9) := ⟨_, rfl⟩
  have hGiG : Gi * G = 1 := by rw [hG, hGi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hα' : ∀ x, suMat (α x) = G * φ.mapMatrix (suMat x) * Gi := fun x => by
    rw [hG, hGi]
    exact hα x
  have hgu' : (G.map σ9)ᵀ * G = 1 := by
    rw [hG]
    exact hgu
  rcases hφ' with rfl | rfl
  ·
    exfalso
    have hα1 : ∀ x, suMat (α x) = G * suMat x * Gi := fun x => by
      rw [hα', RingEquiv.mapMatrix_apply]
      rfl
    obtain ⟨s, hs⟩ := exists_conj_eq_of_unitary hGiG hgu'
    apply hρout
    refine ⟨QuotientGroup.mk s, MulEquiv.ext fun y => ?_⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    rw [MulAut.conj_apply, hρmk]
    show QuotientGroup.mk (s * x * s⁻¹) = QuotientGroup.mk (α x)
    congr 1
    exact suMat_injective (by rw [hα1, hs])
  ·
    obtain ⟨c, hc⟩ := sq_scalar_three α hαα σ9 σ9_σ9 hGiG hα'
    rw [RingEquiv.mapMatrix_apply] at hc
    have hc1 := sq_bar_eq_one hgu' hc
    exact oddCoreIn_fixed_orth ρ α hρmk hGiG hα' hgu' (by rw [hc, hc1, one_smul])

end Outer

end CFSG.ClassicalInvolution.Q3.TL4.U3
