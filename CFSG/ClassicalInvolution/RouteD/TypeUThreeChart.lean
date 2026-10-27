module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.ClassicalInvolution.RouteD.TypeUPatternBasic

public section

namespace CFSG.ClassicalInvolution.RouteD

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.ClassicalGroups.Unitary CFSG.ClassicalGroups.UnitaryFlag CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg CFSG.LieType.Universal.Unitary CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut Module

section Diagonalizer

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem exists_su_two_diagonalizer (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2)
    (U : Matrix (Fin 2) (Fin 2) K) (lam : K) (hlam : lam ≠ 0)
    (hlaml : unitaryInvolution K p f lam * lam = 1)
    (hU2 : U * U = (lam * lam) • (1 : Matrix (Fin 2) (Fin 2) K))
    (hUi : conjTr (unitaryInvolution K p f) U * U = 1) (hne1 : U ≠ lam • 1)
    (hne2 : U ≠ (-lam) • 1) :
    ∃ P : Su K p f 2, U * suMat P = suMat P * Matrix.diagonal ![-lam, lam] := by
  have hσ := isUnitaryInvolution_unitaryInvolution hK
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two hp2
  set σ₀ := unitaryInvolution K p f with hσ₀
  set M : Matrix (Fin 2) (Fin 2) K := lam⁻¹ • U with hM
  have hUM : U = lam • M := by rw [hM, smul_smul, mul_inv_cancel₀ hlam, one_smul]
  have hMM : M * M = 1 := by
    rw [hM, Matrix.smul_mul, Matrix.mul_smul, hU2, smul_smul, smul_smul]
    have : lam⁻¹ * lam⁻¹ * (lam * lam) = 1 := by field_simp
    rw [this, one_smul]
  have hσlam : σ₀ lam⁻¹ * lam⁻¹ = 1 := by
    rw [map_inv₀, ← mul_inv, hlaml, inv_one]
  have hconjTr_smul : ∀ (c : K) (A : Matrix (Fin 2) (Fin 2) K),
      conjTr σ₀ (c • A) = σ₀ c • conjTr σ₀ A := fun c A => by
    ext i j
    simp [conjTr]
  have hMi : conjTr σ₀ M * M = 1 := by
    rw [hM, hconjTr_smul, Matrix.smul_mul, Matrix.mul_smul, hUi, smul_smul, hσlam, one_smul]
  set E : Bool → Submodule K (Fin 2 → K) := fun b => cond b (eigSpace M 1) (eigSpace M (-1))
    with hE
  have hcompl : IsCompl (eigSpace M (-1)) (eigSpace M 1) := isCompl_eigSpace h2 hMM
  have horth : ∀ s t, s ≠ t → Orth σ₀ (E s) (E t) := by
    have key : Orth σ₀ (eigSpace M (-1)) (eigSpace M 1) := by
      intro v hv w hw
      rw [mem_eigSpace_neg_one] at hv
      rw [mem_eigSpace_one] at hw
      have h1 := herm_mulVec σ₀ M v w
      rw [hv, hw, hMi, Matrix.one_mulVec, herm_neg_left] at h1
      have h3 : (2 : K) * herm σ₀ v w = 0 := by linear_combination -h1
      exact (mul_eq_zero.mp h3).resolve_left h2
    intro s t hst u hu v hv
    cases s <;> cases t
    · exact absurd rfl hst
    · exact key u hu v hv
    · exact herm_eq_zero_comm σ₀ hσ.invol (key v hv u hu)
    · exact absurd rfl hst
  have hnd : ∀ s, Nondeg σ₀ (E s) := by
    refine nondeg_of_orth_of_iSup_eq_top E ?_ horth
    rw [iSup_bool_eq]
    exact (show eigSpace M 1 ⊔ eigSpace M (-1) = ⊤ by rw [sup_comm]; exact hcompl.sup_eq_top)
  have hsum := Submodule.finrank_add_eq_of_isCompl hcompl
  rw [Module.finrank_fin_fun] at hsum
  have hMne1 : M ≠ 1 := by
    intro h
    apply hne1
    rw [hUM, h]
  have hMne2 : M ≠ -1 := by
    intro h
    apply hne2
    rw [hUM, h, smul_neg, neg_smul]
  have hpos1 : 0 < finrank K (eigSpace M 1) := by
    rw [Module.finrank_pos_iff_exists_ne_zero]
    by_contra hcon
    push Not at hcon
    apply hMne2
    refine Matrix.ext fun a b => ?_
    have hbot : eigSpace M 1 = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      by_contra hv0
      exact hv0 (by simpa using congrArg Subtype.val (hcon ⟨v, hv⟩))
    have htop : eigSpace M (-1) = ⊤ := by
      have := hcompl.sup_eq_top
      rwa [hbot, sup_bot_eq] at this
    have hall : ∀ v, M *ᵥ v = -v := fun v =>
      mem_eigSpace_neg_one.mp (htop ▸ Submodule.mem_top)
    have := congrFun (hall (Pi.single b 1)) a
    simpa [Matrix.mulVec_single_one, Pi.single_apply, Matrix.one_apply] using this
  have hpos2 : 0 < finrank K (eigSpace M (-1)) := by
    rw [Module.finrank_pos_iff_exists_ne_zero]
    by_contra hcon
    push Not at hcon
    apply hMne1
    refine Matrix.ext fun a b => ?_
    have hbot : eigSpace M (-1) = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      by_contra hv0
      exact hv0 (by simpa using congrArg Subtype.val (hcon ⟨v, hv⟩))
    have htop : eigSpace M 1 = ⊤ := by
      have := hcompl.sup_eq_top
      rwa [hbot, bot_sup_eq] at this
    have hall : ∀ v, M *ᵥ v = v := fun v => mem_eigSpace_one.mp (htop ▸ Submodule.mem_top)
    have := congrFun (hall (Pi.single b 1)) a
    simpa [Matrix.mulVec_single_one, Pi.single_apply, Matrix.one_apply] using this
  have hd1 : finrank K (eigSpace M 1) = 1 := by omega
  have hd2 : finrank K (eigSpace M (-1)) = 1 := by omega
  let ε : Fin 2 → Bool := fun j => decide (j.val = 1)
  have hε : ∀ s, Nat.card {j // ε j = s} = finrank K (E s) := by
    intro s
    cases s
    · change _ = finrank K (eigSpace M (-1))
      rw [hd2, Nat.card_eq_fintype_card]
      decide
    · change _ = finrank K (eigSpace M 1)
      rw [hd1, Nat.card_eq_fintype_card]
      decide
  obtain ⟨P, hP⟩ := exists_su_adapted hσ (by omega : 0 < 2) E hnd horth ε hε
  have hMP : M * suMat P = suMat P * Matrix.diagonal ![(-1 : K), 1] := by
    ext a j
    rw [Matrix.mul_diagonal]
    fin_cases j
    · have := congr_fun (mem_eigSpace_neg_one.mp (hP 0)) a
      rw [suMat_smul, Matrix.mulVec_single_one] at this
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm] using this
    · have := congr_fun (mem_eigSpace_one.mp (hP 1)) a
      rw [suMat_smul, Matrix.mulVec_single_one] at this
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm] using this
  refine ⟨P, ?_⟩
  rw [hUM, Matrix.smul_mul, hMP]
  ext a j
  fin_cases j <;> simp [Matrix.mul_diagonal, Matrix.smul_apply, mul_comm]

end Diagonalizer

section Bd

variable {R : Type*} [CommRing R]

@[expose] def diagBlocks (Y Z : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 4) (Fin 4) R :=
  !![Y 0 0, Y 0 1, 0, 0; Y 1 0, Y 1 1, 0, 0; 0, 0, Z 0 0, Z 0 1; 0, 0, Z 1 0, Z 1 1]

theorem diagBlocks_mul (Y Z Y' Z' : Matrix (Fin 2) (Fin 2) R) :
    diagBlocks Y Z * diagBlocks Y' Z' = diagBlocks (Y * Y') (Z * Z') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagBlocks, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_four]

theorem diagBlocks_one : diagBlocks (1 : Matrix (Fin 2) (Fin 2) R) 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagBlocks]

theorem diagBlocks_smul (c : R) (Y Z : Matrix (Fin 2) (Fin 2) R) :
    c • diagBlocks Y Z = diagBlocks (c • Y) (c • Z) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagBlocks]

theorem diagBlocks_map {S : Type*} [CommRing S] (φ : R → S) (h0 : φ 0 = 0)
    (Y Z : Matrix (Fin 2) (Fin 2) R) :
    (diagBlocks Y Z).map φ = diagBlocks (Y.map φ) (Z.map φ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagBlocks, h0]

theorem diagBlocks_transpose (Y Z : Matrix (Fin 2) (Fin 2) R) :
    (diagBlocks Y Z)ᵀ = diagBlocks Yᵀ Zᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagBlocks]

theorem diagBlocks_inj {Y Z Y' Z' : Matrix (Fin 2) (Fin 2) R}
    (h : diagBlocks Y Z = diagBlocks Y' Z') : Y = Y' ∧ Z = Z' := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j
    · simpa [diagBlocks] using congrFun (congrFun h 0) 0
    · simpa [diagBlocks] using congrFun (congrFun h 0) 1
    · simpa [diagBlocks] using congrFun (congrFun h 1) 0
    · simpa [diagBlocks] using congrFun (congrFun h 1) 1
  · ext i j
    fin_cases i <;> fin_cases j
    · simpa [diagBlocks] using congrFun (congrFun h 2) 2
    · simpa [diagBlocks] using congrFun (congrFun h 2) 3
    · simpa [diagBlocks] using congrFun (congrFun h 3) 2
    · simpa [diagBlocks] using congrFun (congrFun h 3) 3

theorem eq_diagBlocks_of_zero (G : Matrix (Fin 4) (Fin 4) R) (z02 : G 0 2 = 0) (z03 : G 0 3 = 0)
    (z12 : G 1 2 = 0) (z13 : G 1 3 = 0) (z20 : G 2 0 = 0) (z21 : G 2 1 = 0) (z30 : G 3 0 = 0)
    (z31 : G 3 1 = 0) :
    G = diagBlocks !![G 0 0, G 0 1; G 1 0, G 1 1] !![G 2 2, G 2 3; G 3 2, G 3 3] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagBlocks, z02, z03, z12, z13, z20, z21, z30, z31]

end Bd

section Embeddings

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem suMat_blockEmb2_zero_eq_diagBlocks (A : Su K p f 2) :
    suMat (blockEmb2 K p f 3 ⟨0, by omega⟩ A) = diagBlocks (suMat A) 1 := by
  change blockMat (3 + 1) 0 (suMat A) = diagBlocks (suMat A) 1
  ext i j
  rw [blockMat_apply]
  fin_cases i <;> fin_cases j <;> simp [diagBlocks]

theorem suMat_blockEmb2_two_eq_diagBlocks (A : Su K p f 2) :
    suMat (blockEmb2 K p f 3 ⟨2, by omega⟩ A) = diagBlocks 1 (suMat A) := by
  change blockMat (3 + 1) 2 (suMat A) = diagBlocks 1 (suMat A)
  ext i j
  rw [blockMat_apply]
  fin_cases i <;> fin_cases j <;> simp [diagBlocks]

end Embeddings

section ConjConj

theorem conj_chart_eq_of_mul_eq {ι : Type} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R]
    (G Gi H Hi D Di : Matrix ι ι R) (hGiG : Gi * G = 1) (hHHi : H * Hi = 1) (hHiH : Hi * H = 1)
    (hDDi : D * Di = 1) (hGH : G * H = H * D) (X : Matrix ι ι R) :
    G * (H * X * Hi) * Gi = H * (D * X * Di) * Hi := by
  have hHiH' : ∀ Y : Matrix ι ι R, Hi * (H * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, hHiH, Matrix.one_mul]
  have hG : G = H * D * Hi := by
    calc G = G * (H * Hi) := by rw [hHHi, Matrix.mul_one]
      _ = (G * H) * Hi := by rw [Matrix.mul_assoc]
      _ = H * D * Hi := by rw [hGH]
  have hGi : Gi = H * Di * Hi := by
    have h1 : G * (H * Di * Hi) = 1 := by
      rw [hG]
      calc H * D * Hi * (H * Di * Hi) = H * (D * Di) * Hi := by
            simp only [Matrix.mul_assoc, hHiH']
        _ = 1 := by rw [hDDi, Matrix.mul_one, hHHi]
    calc Gi = Gi * (G * (H * Di * Hi)) := by rw [h1, Matrix.mul_one]
      _ = (Gi * G) * (H * Di * Hi) := (Matrix.mul_assoc _ _ _).symm
      _ = H * Di * Hi := by rw [hGiG, Matrix.one_mul]
  rw [hG, hGi]
  simp only [Matrix.mul_assoc, hHiH']

end ConjConj

section Chart

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem unitary_partner_chart_three (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) {Y : Type} [Group Y] (θ : Su K p f (3 + 1) →* Y)
    (hker : θ.ker ≤ Subgroup.center (Su K p f (3 + 1))) (σ : Y ≃* Y) (hσ : ∀ y, σ (σ y) = y)
    (hstab : ∀ x, σ (θ x) ∈ θ.range)
    (hfix : ∀ A : Su K p f 2, σ (θ (blockEmb2 K p f 3 ⟨2, by omega⟩ A)) =
      θ (blockEmb2 K p f 3 ⟨2, by omega⟩ A))
    (hmove : ∃ A : Su K p f 2, σ (θ (blockEmb2 K p f 3 ⟨0, by omega⟩ A)) ≠
      θ (blockEmb2 K p f 3 ⟨0, by omega⟩ A)) :
    ∃ h : Su K p f (3 + 1),
      (blockEmb2 K p f 3 ⟨0, by omega⟩).range.map (MulAut.conj h).toMonoidHom =
        (blockEmb2 K p f 3 ⟨0, by omega⟩).range ∧
      (∀ A : Su K p f 2, h * blockEmb2 K p f 3 ⟨2, by omega⟩ A * h⁻¹ =
        blockEmb2 K p f 3 ⟨2, by omega⟩ A) ∧
      ∀ x, σ (θ (h * x * h⁻¹)) = θ (h * conjSign hK (partnerSigns 3 0) x * h⁻¹) := by
  classical
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · simp at hq
    · exact hf
  have h : UnitaryFieldData p f K := ⟨Fact.out, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two hp2
  have := isPerfect_suTwo_of_card hK hq
  obtain ⟨α, g, φ, hlift, hmat, hiso, hφ, hsq⟩ :=
    unitaryAutClassification_ambient hK hp2 hq (by omega : 3 ≤ 3 + 1) θ hker σ hσ hstab
  have hα2 : ∀ A : Su K p f 2, α (blockEmb2 K p f 3 ⟨2, by omega⟩ A) =
      blockEmb2 K p f 3 ⟨2, by omega⟩ A := fun A =>
    DFunLike.congr_fun (lift_comp_eq_of_fixed hker hlift (blockEmb2 K p f 3 ⟨2, by omega⟩) hfix) A
  have hφinv : ∀ c, φ (φ c) = c := by
    rcases hφ with h1 | h1
    · subst h1
      intro c
      rfl
    · subst h1
      exact unitaryInvolution_involutive hK
  set σ₀ : K ≃+* K := unitaryInvolution K p f with hσ₀
  set G : Matrix (Fin 4) (Fin 4) K := (g : Matrix (Fin (3 + 1)) (Fin (3 + 1)) K) with hG
  set Gi : Matrix (Fin 4) (Fin 4) K :=
    ((g⁻¹ : GL (Fin (3 + 1)) K) : Matrix (Fin (3 + 1)) (Fin (3 + 1)) K) with hGi
  have hGGi : G * Gi = 1 := by rw [hG, hGi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hGiG : Gi * G = 1 := by rw [hG, hGi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  obtain ⟨u, hu1, hu2⟩ := exists_normOne_ne h hp2
  set c : K := ((u : Kˣ) : K) with hc
  have hcinv : (((u : Kˣ)⁻¹ : Kˣ) : K) = c⁻¹ := Units.val_inv_eq_inv_val _
  have hcσ : σ₀ c = c⁻¹ := eq_inv_of_mul_eq_one_left ((mem_normOne _).1 u.2)
  have hu2' : c⁻¹ ≠ c := by rw [← hcinv]; exact hu2
  have hrel : ∀ i j : Fin 4,
      (if i.val = 2 then c else if i.val = 3 then c⁻¹ else 1) * G i j =
        G i j * φ (if j.val = 2 then c else if j.val = 3 then c⁻¹ else 1) := by
    intro i j
    have h1 := hmat (blockEmb2 K p f 3 ⟨2, by omega⟩ (torusTwo σ₀ u))
    rw [hα2 (torusTwo σ₀ u), coe_coe_blockEmb2_torusTwo] at h1
    have h3 := diagonal_relation φ G Gi hGiG _ h1.symm i j
    simpa [hcinv] using h3
  have hoff : ∀ i j : Fin 4, G i j ≠ 0 → (i.val < 2 ∧ j.val < 2) ∨ (2 ≤ i.val ∧ 2 ≤ j.val) := by
    intro i j hne
    rcases hφ with h1 | h1
    · subst h1
      have h3 := hrel i j
      simp only [RingEquiv.refl_apply] at h3
      rcases torus_entry_cases_id (⟨2, by omega⟩ : Fin 3) c hu1 hu2' i j (G i j) hne h3 with
        heq | ⟨h4, h5, h6, h7⟩
      · subst heq
        omega
      · simp only at h4 h5 h6 h7
        omega
    · subst h1
      rcases torus_entry_cases σ₀ (⟨2, by omega⟩ : Fin 3) c hu1 hu2' hcσ i j (G i j) hne
        (hrel i j) with ⟨h4, h5⟩ | ⟨h4, h5⟩ | ⟨h4, h5, h6, h7⟩
      · simp only at h4 h5
        omega
      · simp only at h4 h5
        omega
      · simp only at h4 h5 h6 h7
        omega
  have hz : ∀ i j : Fin 4, ¬ ((i.val < 2 ∧ j.val < 2) ∨ (2 ≤ i.val ∧ 2 ≤ j.val)) → G i j = 0 :=
    fun i j hij => by
      by_contra hne
      exact hij (hoff i j hne)
  have z02 : G 0 2 = 0 := hz 0 2 (by decide)
  have z03 : G 0 3 = 0 := hz 0 3 (by decide)
  have z12 : G 1 2 = 0 := hz 1 2 (by decide)
  have z13 : G 1 3 = 0 := hz 1 3 (by decide)
  have z20 : G 2 0 = 0 := hz 2 0 (by decide)
  have z21 : G 2 1 = 0 := hz 2 1 (by decide)
  have z30 : G 3 0 = 0 := hz 3 0 (by decide)
  have z31 : G 3 1 = 0 := hz 3 1 (by decide)
  obtain ⟨U, hU⟩ : ∃ U : Matrix (Fin 2) (Fin 2) K, U = !![G 0 0, G 0 1; G 1 0, G 1 1] := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : Matrix (Fin 2) (Fin 2) K, S = !![G 2 2, G 2 3; G 3 2, G 3 3] := ⟨_, rfl⟩
  have hGbd : G = diagBlocks U S := by
    rw [hU, hS]
    exact eq_diagBlocks_of_zero G z02 z03 z12 z13 z20 z21 z30 z31
  have hφ0 : φ 0 = 0 := map_zero φ
  have hmap1 : (1 : Matrix (Fin 2) (Fin 2) K).map φ = 1 :=
    Matrix.map_one _ (map_zero φ) (map_one φ)
  have hfix_of_comm : ∀ y : Su K p f (3 + 1), suMat y * G = G * (suMat y).map φ → α y = y := by
    intro y hy
    apply suMat_injective
    have h1 := hmat y
    change suMat (α y) = G * φ.mapMatrix (suMat y) * Gi at h1
    rw [h1, RingEquiv.mapMatrix_apply, ← hy, Matrix.mul_assoc, hGGi, Matrix.mul_one]
  have hcomm_of_fix : ∀ y : Su K p f (3 + 1), α y = y → suMat y * G = G * (suMat y).map φ := by
    intro y hy
    have h1 := hmat y
    rw [hy] at h1
    change suMat y = G * φ.mapMatrix (suMat y) * Gi at h1
    rw [RingEquiv.mapMatrix_apply] at h1
    calc suMat y * G = (G * (suMat y).map φ * Gi) * G := by rw [← h1]
      _ = G * (suMat y).map φ := by rw [Matrix.mul_assoc, hGiG, Matrix.mul_one]
  have hSfix : ∀ A : Su K p f 2, suMat A * S = S * (suMat A).map φ := by
    intro A
    have h1 := hcomm_of_fix _ (hα2 A)
    rw [suMat_blockEmb2_two_eq_diagBlocks, hGbd, diagBlocks_map φ hφ0, hmap1, diagBlocks_mul,
      diagBlocks_mul] at h1
    exact (diagBlocks_inj h1).2
  have hno0 : (∀ A : Su K p f 2, suMat A * U = U * (suMat A).map φ) → False := by
    intro hall
    obtain ⟨A, hA⟩ := hmove
    apply hA
    have hα0 : α (blockEmb2 K p f 3 ⟨0, by omega⟩ A) = blockEmb2 K p f 3 ⟨0, by omega⟩ A := by
      apply hfix_of_comm
      rw [suMat_blockEmb2_zero_eq_diagBlocks, hGbd, diagBlocks_map φ hφ0, hmap1, diagBlocks_mul,
        diagBlocks_mul, hall A, one_mul, mul_one]
    rw [← hlift, hα0]
  have hiso' : (U.map σ₀)ᵀ * U = 1 ∧ (S.map σ₀)ᵀ * S = 1 := by
    have h1 : diagBlocks ((U.map σ₀)ᵀ * U) ((S.map σ₀)ᵀ * S) = diagBlocks 1 1 := by
      rw [diagBlocks_one, ← diagBlocks_mul, ← diagBlocks_transpose,
        ← diagBlocks_map σ₀ (map_zero σ₀), ← hGbd]
      exact hiso
    exact diagBlocks_inj h1
  obtain ⟨c₂, hc₂⟩ : ∃ c₂ : K, G * φ.mapMatrix G = c₂ • (1 : Matrix (Fin 4) (Fin 4) K) := by
    refine eq_smul_one_of_commute h hp2 (by omega : 3 ≤ 3 + 1) (G * φ.mapMatrix G) fun y hy => ?_
    have hy' : y ∈ SUid (unitaryInvolution K p f) (3 + 1) := by
      rw [SUid_eq_statedSU hK]
      exact hy
    have h1 := DFunLike.congr_fun hsq ⟨y, hy'⟩
    have h2' := congrArg (fun x : Su K p f (3 + 1) =>
      ((x : GL (Fin (3 + 1)) K) : Matrix (Fin (3 + 1)) (Fin (3 + 1)) K)) h1
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply] at h2'
    rw [hmat (α ⟨y, hy'⟩), hmat ⟨y, hy'⟩] at h2'
    exact commute_of_double_conj φ hφinv G Gi (y : Matrix (Fin (3 + 1)) (Fin (3 + 1)) K) hGiG
      h2'.symm
  have hsq' : U * U.map φ = c₂ • 1 ∧ S * S.map φ = c₂ • 1 := by
    have h1 : diagBlocks (U * U.map φ) (S * S.map φ) = diagBlocks (c₂ • 1) (c₂ • 1) := by
      rw [← diagBlocks_smul, diagBlocks_one, ← diagBlocks_mul, ← diagBlocks_map φ hφ0, ← hGbd]
      rw [RingEquiv.mapMatrix_apply] at hc₂
      exact hc₂
    exact diagBlocks_inj h1
  have hw00 : suMat (weylElt K p f) 0 0 = 0 := by
    simp [suMat, CFSG.ClassicalInvolution.Phan.weylElt]
  have hw01 : suMat (weylElt K p f) 0 1 = 1 := by
    simp [suMat, CFSG.ClassicalInvolution.Phan.weylElt]
  have hw10 : suMat (weylElt K p f) 1 0 = -1 := by
    simp [suMat, CFSG.ClassicalInvolution.Phan.weylElt]
  have hw11 : suMat (weylElt K p f) 1 1 = 0 := by
    simp [suMat, CFSG.ClassicalInvolution.Phan.weylElt]
  have hW0 : (suMat (weylElt K p f)).map φ = suMat (weylElt K p f) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hw00, hw01, hw10, hw11]
  have hSW := hSfix (weylElt K p f)
  rw [hW0] at hSW
  have hS10 : S 1 0 = -S 0 1 := by
    have e := congrFun (congrFun hSW 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two, hw00, hw01, hw10] at e
    linear_combination e
  have hS11 : S 1 1 = S 0 0 := by
    have e := congrFun (congrFun hSW 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two, hw00, hw01, hw11] at e
    linear_combination e
  rcases hφ with h1 | h1
  ·
    subst h1
    have hmapid : ∀ M : Matrix (Fin 2) (Fin 2) K, M.map (RingEquiv.refl K) = M := fun M => by
      ext i j
      rfl
    have hrefl : ∀ M : Matrix (Fin 4) (Fin 4) K, (RingEquiv.refl K).mapMatrix M = M :=
      fun M => by
        ext a b
        rfl
    have hG23 : G 2 3 = 0 := by
      by_contra hne
      have h3 := hrel 2 3
      simp only [RingEquiv.refl_apply] at h3
      rcases torus_entry_cases_id (⟨2, by omega⟩ : Fin 3) c hu1 hu2' 2 3 (G 2 3) hne h3 with
        heq | ⟨h4, -, -, -⟩
      · exact absurd (congrArg Fin.val heq) (by decide)
      · exact h4 rfl
    have hG32 : G 3 2 = 0 := by
      by_contra hne
      have h3 := hrel 3 2
      simp only [RingEquiv.refl_apply] at h3
      rcases torus_entry_cases_id (⟨2, by omega⟩ : Fin 3) c hu1 hu2' 3 2 (G 3 2) hne h3 with
        heq | ⟨-, h5, -, -⟩
      · exact absurd (congrArg Fin.val heq) (by decide)
      · exact h5 rfl
    have hS01 : S 0 1 = 0 := by rw [hS]; exact hG23
    have hS10' : S 1 0 = 0 := by rw [hS]; exact hG32
    obtain ⟨lam, hlam⟩ : ∃ lam : K, lam = S 0 0 := ⟨_, rfl⟩
    have hSlam : S = lam • (1 : Matrix (Fin 2) (Fin 2) K) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hlam, hS01, hS10', hS11]
    have hlam1 : σ₀ lam * lam = 1 := by
      have e := congrFun (congrFun hiso'.2 0) 0
      simpa [Matrix.mul_apply, Fin.sum_univ_two, hS10', ← hlam] using e
    have hlam0 : lam ≠ 0 := fun h0 => by
      rw [h0, mul_zero] at hlam1
      exact zero_ne_one hlam1
    have hc₂lam : c₂ = lam * lam := by
      have e := congrFun (congrFun hsq'.2 0) 0
      rw [hmapid] at e
      simp [Matrix.mul_apply, Fin.sum_univ_two, hS01, hS10', ← hlam] at e
      exact e.symm
    have hU2 : U * U = (lam * lam) • (1 : Matrix (Fin 2) (Fin 2) K) := by
      have e := hsq'.1
      rw [hmapid, hc₂lam] at e
      exact e
    have hne : ∀ μ : K, U ≠ μ • (1 : Matrix (Fin 2) (Fin 2) K) := fun μ hμ => by
      apply hno0
      intro A
      rw [hμ, hmapid, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
    obtain ⟨P, hP⟩ := exists_su_two_diagonalizer hK hp2 U lam hlam0 hlam1 hU2 hiso'.1
      (hne lam) (hne (-lam))
    set H : Su K p f (3 + 1) := blockEmb2 K p f 3 ⟨0, by omega⟩ P with hH
    have hHrange : H ∈ (blockEmb2 K p f 3 ⟨0, by omega⟩).range := ⟨P, rfl⟩
    have hrange : (blockEmb2 K p f 3 ⟨0, by omega⟩).range.map (MulAut.conj H).toMonoidHom =
        (blockEmb2 K p f 3 ⟨0, by omega⟩).range := by
      ext y
      simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hHrange hx) (Subgroup.inv_mem _ hHrange)
      · intro hy
        exact ⟨H⁻¹ * y * H, Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hHrange) hy)
          hHrange, by group⟩
    have hcomm2 : ∀ A : Su K p f 2, H * blockEmb2 K p f 3 ⟨2, by omega⟩ A * H⁻¹ =
        blockEmb2 K p f 3 ⟨2, by omega⟩ A := fun A =>
      mul_inv_eq_iff_eq_mul.mpr (blockEmb2_comm 3 ⟨0, by omega⟩ ⟨2, by omega⟩ (by simp) P A)
    set Dm : Matrix (Fin 4) (Fin 4) K := Matrix.diagonal ![-lam, lam, lam, lam] with hDm
    set Dmi : Matrix (Fin 4) (Fin 4) K :=
      Matrix.diagonal ![-lam⁻¹, lam⁻¹, lam⁻¹, lam⁻¹] with hDmi
    have hDDi : Dm * Dmi = 1 := by
      rw [hDm, hDmi, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      fin_cases i <;> simp [hlam0]
    have hDm_bd : Dm = diagBlocks (Matrix.diagonal ![-lam, lam]) (lam • 1) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hDm, diagBlocks]
    have hGH : G * suMat H = suMat H * Dm := by
      rw [hGbd, hH, suMat_blockEmb2_zero_eq_diagBlocks, hDm_bd, diagBlocks_mul, diagBlocks_mul, hP,
        hSlam, Matrix.mul_one, Matrix.one_mul]
    have hHHi : suMat H * suMat H⁻¹ = 1 := suMat_mul_suMat_inv H
    have hHiH : suMat H⁻¹ * suMat H = 1 := by rw [← suMat_mul, inv_mul_cancel, suMat_one]
    have hconjsign : ∀ x : Su K p f (3 + 1),
        suMat (conjSign hK (partnerSigns 3 0) x) = Dm * suMat x * Dmi := by
      intro x
      ext i j
      change (((conjSign hK (partnerSigns 3 0) x : Su K p f (3 + 1)) : GL (Fin (3 + 1)) K) :
        Matrix (Fin (3 + 1)) (Fin (3 + 1)) K) i j = _
      rw [coe_coe_conjSign_apply, hDm, hDmi, Matrix.mul_diagonal, Matrix.diagonal_mul]
      fin_cases i <;> fin_cases j <;> simp [signVal, partnerSigns, suMat] <;> field_simp
    have hαx : ∀ x : Su K p f (3 + 1),
        α (H * x * H⁻¹) = H * conjSign hK (partnerSigns 3 0) x * H⁻¹ := by
      intro x
      apply suMat_injective
      have h1 := hmat (H * x * H⁻¹)
      change suMat (α (H * x * H⁻¹)) =
        G * (RingEquiv.refl K).mapMatrix (suMat (H * x * H⁻¹)) * Gi at h1
      rw [h1, hrefl]
      simp only [suMat_mul]
      rw [hconjsign]
      exact conj_chart_eq_of_mul_eq G Gi (suMat H) (suMat H⁻¹) Dm Dmi hGiG hHHi hHiH hDDi hGH
        (suMat x)
    refine ⟨H, hrange, hcomm2, fun x => ?_⟩
    rw [← hlift (H * x * H⁻¹), hαx]
  ·
    exfalso
    have h1' : φ = σ₀ := h1
    subst h1'
    have hσ₀inv : ∀ a : K, σ₀ (σ₀ a) = a := hφinv
    have hG22 : G 2 2 = 0 := by
      by_contra hne
      rcases torus_entry_cases σ₀ (⟨2, by omega⟩ : Fin 3) c hu1 hu2' hcσ 2 2 (G 2 2) hne
        (hrel 2 2) with ⟨-, h5⟩ | ⟨h4, -⟩ | ⟨h4, -, -, -⟩
      · simp at h5
      · simp at h4
      · exact h4 rfl
    have hS00 : S 0 0 = 0 := by rw [hS]; exact hG22
    have hS11' : S 1 1 = 0 := by rw [hS11, hS00]
    have hss : σ₀ (S 0 1) * S 0 1 = 1 := by
      have e := congrFun (congrFun hiso'.2 0) 0
      simpa [Matrix.mul_apply, Fin.sum_univ_two, hS00, hS10] using e
    have hs0 : S 0 1 ≠ 0 := fun h0 => by
      rw [h0, mul_zero] at hss
      exact zero_ne_one hss
    have hc₂ : c₂ = -1 := by
      have e := congrFun (congrFun hsq'.2 0) 0
      simp [Matrix.mul_apply, Fin.sum_univ_two, hS00, hS10] at e
      linear_combination (-1 : K) * e - hss
    have hUa : U * U.map σ₀ = (-1 : K) • (1 : Matrix (Fin 2) (Fin 2) K) := by
      have e := hsq'.1
      rw [hc₂] at e
      exact e
    have hUb : (U.map σ₀)ᵀ * U = 1 := hiso'.1
    set V : Matrix (Fin 2) (Fin 2) K := U.map σ₀ with hV
    have hUV : U * (-V) = 1 := by
      rw [Matrix.mul_neg, hUa, neg_smul, one_smul, neg_neg]
    have hVt : Vᵀ = -V := by
      calc Vᵀ = Vᵀ * (U * (-V)) := by rw [hUV, Matrix.mul_one]
        _ = (Vᵀ * U) * (-V) := by rw [Matrix.mul_assoc]
        _ = -V := by rw [hUb, Matrix.one_mul]
    have hdiag0 : ∀ a : K, a = -a → a = 0 := fun a ha => by
      have : (2 : K) * a = 0 := by linear_combination ha
      exact (mul_eq_zero.mp this).resolve_left h2
    have hV00 : V 0 0 = 0 := hdiag0 _ (by simpa using congrFun (congrFun hVt 0) 0)
    have hV11 : V 1 1 = 0 := hdiag0 _ (by simpa using congrFun (congrFun hVt 1) 1)
    have hV10 : V 1 0 = -V 0 1 := by simpa using congrFun (congrFun hVt 0) 1
    have hUV' : ∀ i j, U i j = σ₀ (V i j) := fun i j => (hσ₀inv (U i j)).symm
    have hU00 : U 0 0 = 0 := by rw [hUV' 0 0, hV00, map_zero]
    have hU11 : U 1 1 = 0 := by rw [hUV' 1 1, hV11, map_zero]
    have hU10 : U 1 0 = -U 0 1 := by rw [hUV' 1 0, hV10, map_neg, ← hUV' 0 1]
    obtain ⟨μ, hμ⟩ : ∃ μ : K, U = μ • S := by
      refine ⟨U 0 1 / S 0 1, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [hU00, hU11, hU10, hS00, hS10, hS11', hs0]
    apply hno0
    intro A
    rw [hμ, Matrix.mul_smul, Matrix.smul_mul, hSfix A]

end Chart

end CFSG.ClassicalInvolution.RouteD
