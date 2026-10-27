module

public import CFSG.ClassicalInvolution.Asc77.SU4ThreeModel
public import CFSG.ClassicalInvolution.Asc77.SU4Lift

public section

namespace CFSG.ClassicalInvolution.RouteD.SU4Pattern

open Matrix CFSG.ClassicalGroups.Unitary CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalInvolution.Models CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.LieType.Universal
open scoped MatrixGroups

section FieldPart

theorem phi_apply_eq {K : Type} [Field K] (σ φ : K ≃+* K) (hσσ : ∀ c, σ (σ c) = c)
    (hfix : ∀ c, σ c = c → φ c = c) (y : K) : φ y = y ∨ φ y = σ y := by
  have ht : φ (y + σ y) = y + σ y := hfix _ (by rw [map_add, hσσ, add_comm])
  have hn : φ (σ y * y) = σ y * y := hfix _ (by rw [map_mul, hσσ, mul_comm])
  have h1 : φ y ^ 2 - (y + σ y) * φ y + σ y * y = 0 := by
    have := congrArg φ (show y ^ 2 - (y + σ y) * y + σ y * y = 0 by ring)
    rw [map_add, map_sub, map_pow, hn, map_mul, ht, map_zero] at this
    exact this
  have h2 : (φ y - y) * (φ y - σ y) = 0 := by linear_combination h1
  rcases mul_eq_zero.mp h2 with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp h)

theorem phi_eq_refl_or {K : Type} [Field K] (σ φ : K ≃+* K) (hσσ : ∀ c, σ (σ c) = c)
    (hfix : ∀ c, σ c = c → φ c = c) : φ = RingEquiv.refl K ∨ φ = σ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  obtain ⟨y₁, hy₁⟩ : ∃ y₁, φ y₁ ≠ y₁ := by
    by_contra h
    push Not at h
    exact h1 (RingEquiv.ext h)
  obtain ⟨y₂, hy₂⟩ : ∃ y₂, φ y₂ ≠ σ y₂ := by
    by_contra h
    push Not at h
    exact h2 (RingEquiv.ext h)
  have e1 : φ y₁ = σ y₁ := (phi_apply_eq σ φ hσσ hfix y₁).resolve_left hy₁
  have e2 : φ y₂ = y₂ := (phi_apply_eq σ φ hσσ hfix y₂).resolve_right hy₂
  rcases phi_apply_eq σ φ hσσ hfix (y₁ + y₂) with h | h
  · rw [map_add, e1, e2] at h
    exact hy₁ (by rw [e1]; exact add_right_cancel h)
  · rw [map_add, e1, e2, map_add] at h
    exact hy₂ (by rw [e2]; exact add_left_cancel h)

end FieldPart

section Torus

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

omit [Finite K] in
theorem conjTr_mapMatrix_mul {σ : K ≃+* K} (hσσ : ∀ c, σ (σ c) = c) {n : ℕ}
    {M : Matrix (Fin n) (Fin n) K} (hM : conjTr σ M * M = 1) :
    conjTr σ (σ.mapMatrix M) * σ.mapMatrix M = 1 := by
  have h1 : M * conjTr σ M = 1 := mul_eq_one_comm.mp hM
  have h2 : (σ.mapMatrix M) * Mᵀ = 1 := by
    have := congrArg Matrix.transpose h1
    rw [Matrix.transpose_mul] at this
    simpa [conjTr, Matrix.transpose_transpose] using this
  have h3 : conjTr σ (σ.mapMatrix M) = Mᵀ := by
    ext i j
    simp [conjTr, hσσ]
  rw [h3]
  exact mul_eq_one_comm.mp h2

omit [Finite K] in
theorem det_su4Torus (l : K) (hl : l ≠ 0) :
    (BD (l • (1 : Matrix (Fin 2) (Fin 2) K)) (l⁻¹ • 1)).det = 1 := by
  rw [det_BD, Matrix.det_smul, Matrix.det_smul, Matrix.det_one]
  simp only [Fintype.card_fin]
  field_simp

omit [Finite K] in
theorem conjTr_su4Torus {σ : K ≃+* K} {l : K} (hl : σ l * l = 1) :
    conjTr σ (BD (l • (1 : Matrix (Fin 2) (Fin 2) K)) (l⁻¹ • 1)) *
      BD (l • (1 : Matrix (Fin 2) (Fin 2) K)) (l⁻¹ • 1) = 1 := by
  have hl' : σ l⁻¹ * l⁻¹ = 1 := by rw [map_inv₀, ← mul_inv, hl, inv_one]
  rw [conjTr_BD, BD_mul]
  have e1 : conjTr σ (l • (1 : Matrix (Fin 2) (Fin 2) K)) = σ l • 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [conjTr]
  have e2 : conjTr σ (l⁻¹ • (1 : Matrix (Fin 2) (Fin 2) K)) = σ l⁻¹ • 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [conjTr]
  rw [e1, e2, smul_mul_smul_comm, smul_mul_smul_comm, hl, hl']
  simp [BD_one]

variable (K p f) in
@[expose] noncomputable def su4TorusElt (l : K) (hl : unitaryInvolution K p f l * l = 1) :
    Su K p f 4 :=
  mkSU K p f (BD (l • (1 : Matrix (Fin 2) (Fin 2) K)) (l⁻¹ • 1))
    (det_su4Torus l (right_ne_zero_of_mul_eq_one hl)) (conjTr_su4Torus hl)

theorem suMat_su4TorusElt (l : K) (hl : unitaryInvolution K p f l * l = 1) :
    suMat (su4TorusElt K p f l hl) = BD (l • (1 : Matrix (Fin 2) (Fin 2) K)) (l⁻¹ • 1) :=
  suMat_mkSU _ _

end Torus

section BlockDiag

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem blockDiag_of_normalizes_symm (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) {G : Matrix (Fin 4) (Fin 4) K} (hsymm : ∃ s : K, ∀ i j, G i j = s * G j i)
    (hnorm : ∀ A : Su K p f 2, ∃ A' : Matrix (Fin 2) (Fin 2) K,
      G * blockMat 4 0 (suMat A) = blockMat 4 0 A' * G) :
    G = BD !![G 0 0, G 0 1; G 1 0, G 1 1] !![G 2 2, G 2 3; G 3 2, G 3 3] := by
  obtain ⟨u, hu, hne⟩ := exists_norm_one_ne hK hp2 hq
  set σ := unitaryInvolution K p f with hσ
  have hσσ : ∀ c, σ (σ c) = c := unitaryInvolution_involutive hK
  have hu' : u * σ u = 1 := by rw [mul_comm]; exact hu
  have hu1 : u ≠ 1 := by
    rintro rfl
    apply hne
    simp
  have hu1' : σ u ≠ 1 := by
    intro h1
    apply hu1
    have := congrArg σ h1
    rwa [hσσ, map_one] at this
  have hdet1 : (!![u, 0; 0, σ u] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    rw [Matrix.det_fin_two_of]
    simp [hu']
  have hiso1 : conjTr σ (!![u, 0; 0, σ u] : Matrix (Fin 2) (Fin 2) K) *
      (!![u, 0; 0, σ u] : Matrix (Fin 2) (Fin 2) K) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [conjTr, Matrix.mul_apply, Fin.sum_univ_two, hσσ, hu, hu']
  obtain ⟨s, hT⟩ := hsymm
  obtain ⟨A', hA'⟩ := hnorm (mkSU K p f _ hdet1 hiso1)
  rw [suMat_mkSU] at hA'
  have e20 := congrFun (congrFun hA' 2) 0
  have e30 := congrFun (congrFun hA' 3) 0
  have e21 := congrFun (congrFun hA' 2) 1
  have e31 := congrFun (congrFun hA' 3) 1
  simp [Matrix.mul_apply, blockMat_apply, Fin.sum_univ_four] at e20 e30 e21 e31
  have z20 : G 2 0 = 0 := by
    have : G 2 0 * (u - 1) = 0 := by linear_combination e20
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hu1)
  have z30 : G 3 0 = 0 := by
    have : G 3 0 * (u - 1) = 0 := by linear_combination e30
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hu1)
  have z21 : G 2 1 = 0 := by
    have : G 2 1 * (σ u - 1) = 0 := by linear_combination e21
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hu1')
  have z31 : G 3 1 = 0 := by
    have : G 3 1 * (σ u - 1) = 0 := by linear_combination e31
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hu1')
  have z02 : G 0 2 = 0 := by rw [hT, z20, mul_zero]
  have z03 : G 0 3 = 0 := by rw [hT, z30, mul_zero]
  have z12 : G 1 2 = 0 := by rw [hT, z21, mul_zero]
  have z13 : G 1 3 = 0 := by rw [hT, z31, mul_zero]
  rw [BD_eq]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [z20, z30, z21, z31, z02, z03, z12, z13]

end BlockDiag

section MapBlock

variable {K : Type} [Field K]

theorem mapMatrix_blockMat (σ : K ≃+* K) {m i k : ℕ} (A : Matrix (Fin k) (Fin k) K) :
    σ.mapMatrix (blockMat m i A) = blockMat m i (σ.mapMatrix A) := by
  have hL : (blockSel K m k i).map σ = blockSel K m k i := by
    ext a j
    simp only [Matrix.map_apply, blockSel_apply]
    split_ifs <;> simp
  have hLt : ((blockSel K m k i)ᵀ).map σ = (blockSel K m k i)ᵀ := by
    rw [Matrix.transpose_map, hL]
  have hN : (A - 1).map σ = A.map σ - 1 := by
    rw [Matrix.map_sub _ (map_sub σ), Matrix.map_one _ (map_zero σ) (map_one σ)]
  unfold blockMat
  show (1 + blockSel K m k i * (A - 1) * (blockSel K m k i)ᵀ).map σ =
    1 + blockSel K m k i * (A.map σ - 1) * (blockSel K m k i)ᵀ
  rw [Matrix.map_add _ (map_add σ), Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.map_mul,
    Matrix.map_mul, hL, hLt, hN]

end MapBlock


section Main

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

omit [Finite K] in
theorem conjTr_smul_one (σ : K ≃+* K) (c : K) :
    conjTr σ (c • (1 : Matrix (Fin 2) (Fin 2) K)) = σ c • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [conjTr]

omit [Finite K] in
theorem mapMatrix_smul_one (σ : K ≃+* K) (c : K) :
    σ.mapMatrix (c • (1 : Matrix (Fin 2) (Fin 2) K)) = σ c • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

omit [Finite K] in
theorem mapMatrix_BD (σ : K ≃+* K) (X Y : Matrix (Fin 2) (Fin 2) K) :
    σ.mapMatrix (BD X Y) = BD (σ.mapMatrix X) (σ.mapMatrix Y) := by
  unfold BD
  rw [map_mul, mapMatrix_blockMat, mapMatrix_blockMat]

theorem linearLift_of_torus_fixed (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) {F : Type} [Field F] [Finite F] (ε : F ≃+* fixedSubfield K p f)
    {X : Type} [Group X] (ψ : Su K p f 4 →* X) (hker : ψ.ker ≤ Subgroup.center (Su K p f 4))
    (τ : X ≃* X) (hτ : ∀ x, τ (τ x) = x) (hstab : ∀ x, τ (ψ x) ∈ ψ.range)
    (θ : SL(2, F) →* X) (hθ : θ.range = (rootSU2 K p f (by norm_num : 2 ≤ 4)).map ψ)
    (d : Fˣ) (hθτ : ∀ s, τ (θ s) = θ (diagConj2 d 1 s)) (l : K)
    (hl : unitaryInvolution K p f l * l = 1) (hl4 : l ^ 4 ≠ 1)
    (hT : τ (ψ (su4TorusElt K p f l hl)) = ψ (su4TorusElt K p f l hl)) :
    LinearLift ψ τ := by
  classical
  set σ := unitaryInvolution K p f with hσ
  have hσσ : ∀ c, σ (σ c) = c := unitaryInvolution_involutive hK
  have hn : (2 : ℕ) ≤ 4 := by norm_num
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  obtain ⟨α, g, φ, hα, hmat, hiso⟩ :=
    exists_lift_of_stab hK hp2 hq ψ hker τ (fun x => by rw [hτ, hτ]) hstab
  obtain ⟨θ', hθ'inj, hθ'range, -, hequiv, hfix⟩ :=
    exists_chart_lift hK hp2 hq ε ψ hker θ hθ τ d hθτ α g φ hα hmat
  have hfix' : ∀ c, σ c = c → φ c = c := fun c hc =>
    hfix c ((mem_fixedSubfield (F := K) (p := p) (f := f)).2 hc)
  rcases phi_eq_refl_or σ φ hσσ hfix' with hφ | hφ
  · exact LinearLift.of_lift α g φ (fun y => by rw [hφ]; rfl) hα hmat hiso
  · exfalso
    subst hφ
    have hperf : Group.IsPerfect (Su K p f 4) :=
      ⟨(CFSG.ClassicalInvolution.ModelFacts.open_isQuasisimple_su hK hq (k := 4)
        (by norm_num)).1⟩
    have hα2 : ∀ x, α (α x) = x := by
      have := hom_eq_of_central_ker_perfect (G := Su K p f 4) (θ := ψ) hker
        (α.comp α) (MonoidHom.id _) (fun x => by
          simp only [MonoidHom.comp_apply, MonoidHom.id_apply]
          rw [hα, hα, hτ])
      exact fun x => DFunLike.congr_fun this x
    set G : Matrix (Fin 4) (Fin 4) K := (g : Matrix (Fin 4) (Fin 4) K) with hG
    set Gi : Matrix (Fin 4) (Fin 4) K := ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
      with hGi
    have hGGi : G * Gi = 1 := by rw [hG, hGi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hGiG : Gi * G = 1 := by rw [hG, hGi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hαmat : ∀ y : Su K p f 4, suMat (α y) = G * σ.mapMatrix (suMat y) * Gi := fun y => hmat y
    set H : Matrix (Fin 4) (Fin 4) K := G * σ.mapMatrix G with hH
    set Hi : Matrix (Fin 4) (Fin 4) K := σ.mapMatrix Gi * Gi with hHi
    have hHiH : Hi * H = 1 := by
      rw [hH, hHi]
      calc σ.mapMatrix Gi * Gi * (G * σ.mapMatrix G)
          = σ.mapMatrix Gi * (Gi * G) * σ.mapMatrix G := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hGiG, Matrix.mul_one, ← map_mul, hGiG, map_one]
    have hUF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
      ⟨Fact.out, hf, by rw [hK, ← pow_mul, mul_comm]⟩
    have hHsc : ∃ s : K, H = s • (1 : Matrix (Fin 4) (Fin 4) K) := by
      refine eq_smul_one_of_commute hUF hp2 (by norm_num : 3 ≤ 4) H fun y hy => ?_
      have hy' : y ∈ SUid σ 4 := by rw [SUid_eq_statedSU hK]; exact hy
      have hσm : ∀ M : Matrix (Fin 4) (Fin 4) K, σ.mapMatrix (σ.mapMatrix M) = M := fun M => by
        ext i j
        simp [hσσ]
      have h5 : suMat (α (α ⟨y, hy'⟩)) = H * (y : Matrix (Fin 4) (Fin 4) K) * Hi := by
        rw [hαmat (α ⟨y, hy'⟩), hαmat ⟨y, hy'⟩, hH, hHi]
        simp only [map_mul, hσm, Matrix.mul_assoc]
        try rfl
      rw [hα2 ⟨y, hy'⟩] at h5
      calc H * (y : Matrix (Fin 4) (Fin 4) K)
          = (H * (y : Matrix (Fin 4) (Fin 4) K) * Hi) * H := by
            rw [Matrix.mul_assoc (H * (y : Matrix (Fin 4) (Fin 4) K)), hHiH, Matrix.mul_one]
        _ = (y : Matrix (Fin 4) (Fin 4) K) * H := by rw [← h5]; rfl
    obtain ⟨s, hs⟩ := hHsc
    have hGs : G * σ.mapMatrix G = s • (1 : Matrix (Fin 4) (Fin 4) K) := hs
    have hsymm : ∃ s' : K, ∀ i j, G i j = s' * G j i := by
      refine ⟨σ s, fun i j => ?_⟩
      have h1 : (σ.mapMatrix G)ᵀ * G = 1 := hiso
      have h2 : σ.mapMatrix G = s • (σ.mapMatrix G)ᵀ := by
        calc σ.mapMatrix G = ((σ.mapMatrix G)ᵀ * G) * σ.mapMatrix G := by
              rw [h1, Matrix.one_mul]
          _ = (σ.mapMatrix G)ᵀ * (G * σ.mapMatrix G) := by rw [Matrix.mul_assoc]
          _ = s • (σ.mapMatrix G)ᵀ := by rw [hGs, Matrix.mul_smul, Matrix.mul_one]
      have h3 := congrFun (congrFun h2 i) j
      simp only [Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul] at h3
      have h4 := congrArg σ h3
      simpa [hσσ] using h4
    have hRθ : ∀ A : Su K p f 2, ∃ s : SL(2, F), θ' s = blockEmb K p f 4 2 0 (by omega) A := by
      intro A
      have : blockEmb K p f 4 2 0 (by omega) A ∈ rootSU2 K p f hn := ⟨A, rfl⟩
      rw [← hθ'range] at this
      exact this
    have hbar : ∀ A : Su K p f 2, ∃ B : Su K p f 2, suMat B = σ.mapMatrix (suMat A) := by
      intro A
      have hdet : (σ.mapMatrix (suMat A)).det = 1 := by
        have : (σ.mapMatrix (suMat A)).det = σ (suMat A).det :=
          (RingHom.map_det (σ : K →+* K) (suMat A)).symm
        have hA1 : (suMat A).det = 1 := A.2.1
        rw [this, hA1, map_one]
      exact ⟨mkSU K p f (σ.mapMatrix (suMat A)) hdet (conjTr_mapMatrix_mul hσσ A.2.2), rfl⟩
    have hσm : ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) K), σ.mapMatrix (σ.mapMatrix M) = M :=
      fun M => by
        ext i j
        simp [hσσ]
    have hnorm : ∀ A : Su K p f 2, ∃ A' : Matrix (Fin 2) (Fin 2) K,
        G * blockMat 4 0 (suMat A) = blockMat 4 0 A' * G := by
      intro A
      obtain ⟨B, hB⟩ := hbar A
      obtain ⟨s₀, hs₀⟩ := hRθ B
      have h1 : α (blockEmb K p f 4 2 0 (by omega) B) ∈ rootSU2 K p f hn := by
        rw [← hs₀, hequiv, ← hθ'range]
        exact ⟨_, rfl⟩
      obtain ⟨A'', hA''⟩ := h1
      refine ⟨suMat A'', ?_⟩
      have h2 := congrArg suMat hA''
      have e1 : suMat (blockEmb K p f 4 2 0 (by omega) A'') = blockMat 4 0 (suMat A'') := rfl
      have e2 : suMat (blockEmb K p f 4 2 0 (by omega) B) = blockMat 4 0 (suMat B) := rfl
      rw [e1, hαmat, e2, mapMatrix_blockMat, hB, hσm] at h2
      calc G * blockMat 4 0 (suMat A) = G * blockMat 4 0 (suMat A) * (Gi * G) := by
            rw [hGiG, Matrix.mul_one]
        _ = (G * blockMat 4 0 (suMat A) * Gi) * G := by simp only [Matrix.mul_assoc]
        _ = blockMat 4 0 (suMat A'') * G := by rw [h2]
    have hGform := blockDiag_of_normalizes_symm hK hp2 hq hsymm hnorm
    have hcomm : ∀ a b : K, G * BD (a • (1 : Matrix (Fin 2) (Fin 2) K)) (b • 1) =
        BD (a • (1 : Matrix (Fin 2) (Fin 2) K)) (b • 1) * G := by
      intro a b
      rw [hGform, BD_mul, BD_mul]
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
    have hαt : α (su4TorusElt K p f l hl) = (su4TorusElt K p f l hl)⁻¹ := by
      apply suMat_injective
      rw [hαmat, suMat_su4TorusElt, mapMatrix_BD, mapMatrix_smul_one, mapMatrix_smul_one,
        ← conjTr_suMat_eq_inv, suMat_su4TorusElt, conjTr_BD, conjTr_smul_one, conjTr_smul_one,
        hcomm, Matrix.mul_assoc, hGGi, Matrix.mul_one]
    have hψt : ψ ((su4TorusElt K p f l hl)⁻¹) = ψ (su4TorusElt K p f l hl) := by
      rw [← hαt, hα, hT]
    have hker2 : su4TorusElt K p f l hl * su4TorusElt K p f l hl ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul]
      rw [map_inv] at hψt
      exact mul_eq_one_iff_eq_inv.mpr hψt.symm
    have hc := hker hker2
    obtain ⟨c, hcc⟩ : ∃ c : K, suMat (su4TorusElt K p f l hl * su4TorusElt K p f l hl) =
        c • (1 : Matrix (Fin 4) (Fin 4) K) := by
      refine eq_smul_one_of_commute hUF hp2 (by norm_num : 3 ≤ 4) _ fun y hy => ?_
      have hy' : y ∈ SUid σ 4 := by rw [SUid_eq_statedSU hK]; exact hy
      have h6 := congrArg suMat (Subgroup.mem_center_iff.mp hc ⟨y, hy'⟩)
      rw [suMat_mul, suMat_mul] at h6
      exact h6.symm
    rw [suMat_mul, suMat_su4TorusElt, BD_mul, BD_eq] at hcc
    have e00 := congrFun (congrFun hcc 0) 0
    have e22 := congrFun (congrFun hcc 2) 2
    simp at e00 e22
    have hl0 : l ≠ 0 := right_ne_zero_of_mul_eq_one hl
    apply hl4
    have h7 : (l * l) * (l * l) = 1 := by
      calc (l * l) * (l * l) = (l * l) * (l⁻¹ * l⁻¹) := by rw [e00, e22]
        _ = 1 := by field_simp
    calc l ^ 4 = (l * l) * (l * l) := by ring
      _ = 1 := h7

end Main

end CFSG.ClassicalInvolution.RouteD.SU4Pattern
