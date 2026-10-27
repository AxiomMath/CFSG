module

public import CFSG.ClassicalInvolution.Asc77.AscT8W16
public import CFSG.ClassicalInvolution.Asc77.AscT8W13
public import CFSG.ClassicalInvolution.Asc77.AscT8W15

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T8W

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU
  CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4 CFSG.ClassicalGroups.Unitary

section Generic

variable {K : Type} [Field K]

theorem unitary_inner_entries {σ : K ≃+* K} {a h22 h23 h32 h33 : K}
    (hiso : ((!![a, 0, 0, 0; 0, a, 0, 0; 0, 0, h22, h23; 0, 0, h32, h33] :
        Matrix (Fin 4) (Fin 4) K).map σ)ᵀ * !![a, 0, 0, 0; 0, a, 0, 0; 0, 0, h22, h23;
          0, 0, h32, h33] = 1) :
    σ a * a = 1 ∧ ((!![h22, h23; h32, h33] : Matrix (Fin 2) (Fin 2) K).map σ)ᵀ *
      !![h22, h23; h32, h33] = 1 := by
  have e00 := congrFun (congrFun hiso 0) 0
  have e22 := congrFun (congrFun hiso 2) 2
  have e23 := congrFun (congrFun hiso 2) 3
  have e32 := congrFun (congrFun hiso 3) 2
  have e33 := congrFun (congrFun hiso 3) 3
  simp [Matrix.mul_apply, Fin.sum_univ_four] at e00 e22 e23 e32 e33
  refine ⟨e00, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · exact e22
  · exact e23
  · exact e32
  · exact e33

theorem sq_of_commute_inner {a h22 h23 h32 h33 : K}
    (hmix : ((!![a, 0, 0, 0; 0, a, 0, 0; 0, 0, h22, h23; 0, 0, h32, h33] :
        Matrix (Fin 4) (Fin 4) K) * !![a, 0, 0, 0; 0, a, 0, 0; 0, 0, h22, h23; 0, 0, h32, h33]) *
        !![0, 0, 1, 0; 0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1] =
      !![0, 0, 1, 0; 0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1] *
        ((!![a, 0, 0, 0; 0, a, 0, 0; 0, 0, h22, h23; 0, 0, h32, h33] : Matrix (Fin 4) (Fin 4) K) *
          !![a, 0, 0, 0; 0, a, 0, 0; 0, 0, h22, h23; 0, 0, h32, h33]))
    (hJ : ((!![a, 0, 0, 0; 0, a, 0, 0; 0, 0, h22, h23; 0, 0, h32, h33] :
        Matrix (Fin 4) (Fin 4) K) * !![a, 0, 0, 0; 0, a, 0, 0; 0, 0, h22, h23; 0, 0, h32, h33]) *
        !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0] =
      !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0] *
        ((!![a, 0, 0, 0; 0, a, 0, 0; 0, 0, h22, h23; 0, 0, h32, h33] : Matrix (Fin 4) (Fin 4) K) *
          !![a, 0, 0, 0; 0, a, 0, 0; 0, 0, h22, h23; 0, 0, h32, h33])) :
    (!![h22, h23; h32, h33] : Matrix (Fin 2) (Fin 2) K) * !![h22, h23; h32, h33] =
      (a * a) • (1 : Matrix (Fin 2) (Fin 2) K) := by
  have hGG : (!![a, 0, 0, 0; 0, a, 0, 0; 0, 0, h22, h23; 0, 0, h32, h33] :
      Matrix (Fin 4) (Fin 4) K) * !![a, 0, 0, 0; 0, a, 0, 0; 0, 0, h22, h23; 0, 0, h32, h33] =
      !![a * a, 0, 0, 0; 0, a * a, 0, 0; 0, 0, h22 * h22 + h23 * h32, h22 * h23 + h23 * h33;
        0, 0, h32 * h22 + h33 * h32, h32 * h23 + h33 * h33] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
  rw [hGG] at hmix hJ
  obtain ⟨c00, c01, c10, c11⟩ := scalar_of_commute_mix hmix hJ
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · exact c00
  · exact c01
  · exact c10
  · exact c11

theorem comm_of_sq_conj {σ : K ≃+* K} (hσσ : ∀ c, σ (σ c) = c)
    {G Gi : Matrix (Fin 4) (Fin 4) K} (hGGi : G * Gi = 1) (hGiG : Gi * G = 1)
    {X : Matrix (Fin 4) (Fin 4) K} (h : X = G * ((G * X.map σ * Gi).map σ) * Gi) :
    (G * G.map σ) * X = X * (G * G.map σ) := by
  have hXX : (X.map σ).map σ = X := by
    ext i j
    simp [hσσ]
  rw [Matrix.map_mul, Matrix.map_mul, hXX] at h
  have h1 : G.map σ * Gi.map σ = 1 := by
    rw [← Matrix.map_mul, hGGi, Matrix.map_one _ (map_zero σ) (map_one σ)]
  have h2 : Gi.map σ * G.map σ = 1 := by
    rw [← Matrix.map_mul, hGiG, Matrix.map_one _ (map_zero σ) (map_one σ)]
  have hΛΛ : (Gi.map σ * Gi) * (G * G.map σ) = 1 := by
    calc (Gi.map σ * Gi) * (G * G.map σ) = Gi.map σ * (Gi * G) * G.map σ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hGiG, Matrix.mul_one, h2]
  have hX' : X = (G * G.map σ) * X * (Gi.map σ * Gi) := by
    calc X = G * (G.map σ * X * Gi.map σ) * Gi := h
      _ = (G * G.map σ) * X * (Gi.map σ * Gi) := by simp only [Matrix.mul_assoc]
  calc (G * G.map σ) * X = (G * G.map σ) * X * ((Gi.map σ * Gi) * (G * G.map σ)) := by
        rw [hΛΛ, Matrix.mul_one]
    _ = ((G * G.map σ) * X * (Gi.map σ * Gi)) * (G * G.map σ) := by
        simp only [Matrix.mul_assoc]
    _ = X * (G * G.map σ) := by rw [← hX']

theorem lambda_scalar_graph {σ : K ≃+* K} {m h22 h23 h32 h33 : K}
    (hmix : ((!![0, m, 0, 0; -m, 0, 0, 0; 0, 0, h22, h23; 0, 0, h32, h33] :
        Matrix (Fin 4) (Fin 4) K) * (!![0, m, 0, 0; -m, 0, 0, 0; 0, 0, h22, h23; 0, 0, h32, h33] :
          Matrix (Fin 4) (Fin 4) K).map σ) * !![0, 0, 1, 0; 0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1] =
      !![0, 0, 1, 0; 0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1] *
        ((!![0, m, 0, 0; -m, 0, 0, 0; 0, 0, h22, h23; 0, 0, h32, h33] :
          Matrix (Fin 4) (Fin 4) K) * (!![0, m, 0, 0; -m, 0, 0, 0; 0, 0, h22, h23;
            0, 0, h32, h33] : Matrix (Fin 4) (Fin 4) K).map σ))
    (hJ : ((!![0, m, 0, 0; -m, 0, 0, 0; 0, 0, h22, h23; 0, 0, h32, h33] :
        Matrix (Fin 4) (Fin 4) K) * (!![0, m, 0, 0; -m, 0, 0, 0; 0, 0, h22, h23; 0, 0, h32, h33] :
          Matrix (Fin 4) (Fin 4) K).map σ) * !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0] =
      !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0] *
        ((!![0, m, 0, 0; -m, 0, 0, 0; 0, 0, h22, h23; 0, 0, h32, h33] :
          Matrix (Fin 4) (Fin 4) K) * (!![0, m, 0, 0; -m, 0, 0, 0; 0, 0, h22, h23;
            0, 0, h32, h33] : Matrix (Fin 4) (Fin 4) K).map σ)) :
    (!![0, m, 0, 0; -m, 0, 0, 0; 0, 0, h22, h23; 0, 0, h32, h33] : Matrix (Fin 4) (Fin 4) K) *
      (!![0, m, 0, 0; -m, 0, 0, 0; 0, 0, h22, h23; 0, 0, h32, h33] :
        Matrix (Fin 4) (Fin 4) K).map σ = (-(m * σ m)) • (1 : Matrix (Fin 4) (Fin 4) K) := by
  have hΛ : (!![0, m, 0, 0; -m, 0, 0, 0; 0, 0, h22, h23; 0, 0, h32, h33] :
      Matrix (Fin 4) (Fin 4) K) * (!![0, m, 0, 0; -m, 0, 0, 0; 0, 0, h22, h23; 0, 0, h32, h33] :
        Matrix (Fin 4) (Fin 4) K).map σ =
      !![-(m * σ m), 0, 0, 0; 0, -(m * σ m), 0, 0; 0, 0, h22 * σ h22 + h23 * σ h32,
        h22 * σ h23 + h23 * σ h33; 0, 0, h32 * σ h22 + h33 * σ h32,
        h32 * σ h23 + h33 * σ h33] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
  rw [hΛ] at hmix hJ ⊢
  obtain ⟨c00, c01, c10, c11⟩ := scalar_of_commute_mix hmix hJ
  ext i j
  fin_cases i <;> fin_cases j <;> simp [c00, c01, c10, c11]

theorem eq_smul_transpose {σ : K ≃+* K} {G : Matrix (Fin 4) (Fin 4) K}
    (hiso : (G.map σ)ᵀ * G = 1) {c : K} (hΛ : G * G.map σ = c • (1 : Matrix (Fin 4) (Fin 4) K)) :
    G = c • Gᵀ := by
  have h1 : G * (G.map σ)ᵀ = 1 := mul_eq_one_comm.mp hiso
  have h2 : G.map σ * Gᵀ = 1 := by
    have := congrArg Matrix.transpose h1
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this
  calc G = G * (G.map σ * Gᵀ) := by rw [h2, Matrix.mul_one]
    _ = (G * G.map σ) * Gᵀ := by rw [Matrix.mul_assoc]
    _ = c • Gᵀ := by rw [hΛ, Matrix.smul_mul, Matrix.one_mul]

theorem su2_entries {σ : K ≃+* K} {A : Matrix (Fin 2) (Fin 2) K} (hdet : A.det = 1)
    (hU : (A.map σ)ᵀ * A = 1) :
    σ (A 0 0) = A 1 1 ∧ σ (A 0 1) = -(A 1 0) ∧ σ (A 1 0) = -(A 0 1) ∧ σ (A 1 1) = A 0 0 := by
  have e00 := congrFun (congrFun hU 0) 0
  have e01 := congrFun (congrFun hU 0) 1
  have e10 := congrFun (congrFun hU 1) 0
  have e11 := congrFun (congrFun hU 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  rw [Matrix.det_fin_two] at hdet
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination A 1 1 * e00 - A 1 0 * e01 - σ (A 0 0) * hdet
  · linear_combination A 1 1 * e10 - A 1 0 * e11 - σ (A 0 1) * hdet
  · linear_combination A 0 0 * e01 - A 0 1 * e00 - σ (A 1 0) * hdet
  · linear_combination A 0 0 * e11 - A 0 1 * e10 - σ (A 1 1) * hdet

theorem graph_iso_norm {σ : K ≃+* K} {m h22 h23 h32 h33 : K}
    (hiso : ((!![0, m, 0, 0; -m, 0, 0, 0; 0, 0, h22, h23; 0, 0, h32, h33] :
        Matrix (Fin 4) (Fin 4) K).map σ)ᵀ * !![0, m, 0, 0; -m, 0, 0, 0; 0, 0, h22, h23;
          0, 0, h32, h33] = 1) : σ m * m = 1 := by
  have e00 := congrFun (congrFun hiso 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_four] at e00
  exact e00

theorem graph_block2_commute {σ : K ≃+* K} {m n : K} {A : Matrix (Fin 2) (Fin 2) K}
    (hdet : A.det = 1) (hU : (A.map σ)ᵀ * A = 1) :
    (!![0, m, 0, 0; -m, 0, 0, 0; 0, 0, 0, n; 0, 0, -n, 0] : Matrix (Fin 4) (Fin 4) K) *
      (!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, A 0 0, A 0 1; 0, 0, A 1 0, A 1 1] :
        Matrix (Fin 4) (Fin 4) K).map σ =
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, A 0 0, A 0 1; 0, 0, A 1 0, A 1 1] *
      !![0, m, 0, 0; -m, 0, 0, 0; 0, 0, 0, n; 0, 0, -n, 0] := by
  obtain ⟨b00, b01, b10, b11⟩ := su2_entries hdet hU
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, b00, b01, b10, b11] <;>
    ring

end Generic

section Main

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem suMat_blockEmb_two_jSU :
    suMat (blockEmb K p f 4 2 2 (by norm_num) (jSU K p f)) =
      !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0] := by
  rw [suMat_blockEmb_two, suMat_jSU]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem suMat_blockEmb2_three (i : Fin 3) (A : Su K p f 2) :
    suMat (blockEmb2 K p f 3 i A) = blockMat 4 i (suMat A) :=
  suMat_blockEmb _ A

theorem su4_gen_std (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {X : Type}
    [Group X] (θ : Su K p f 4 →* X) (hθ : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center (Su K p f 4)) (σ : MulAut X) (hσ2 : ∀ x, σ (σ x) = x)
    (h0 : ∀ A : Su K p f 2, σ (θ (blockEmb K p f 4 2 0 (by norm_num) A)) =
      θ (blockEmb K p f 4 2 0 (by norm_num) A))
    (hnt : ∃ A : Su K p f 2, σ (θ (blockEmb K p f 4 2 2 (by norm_num) A)) ≠
      θ (blockEmb K p f 4 2 2 (by norm_num) A)) :
    Subgroup.closure ({g | σ g = g} ∪
      {g | σ (θ (negTwoSU K p f) * g * (θ (negTwoSU K p f))⁻¹) = g}) = ⊤ := by
  classical
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two (K := K) hp
  have hσ : IsUnitaryInvolution (unitaryInvolution K p f) :=
    isUnitaryInvolution_unitaryInvolution hK
  have hσσ : ∀ c, unitaryInvolution K p f (unitaryInvolution K p f c) = c :=
    unitaryInvolution_involutive hK
  have hq2 : p ^ f ≠ 2 := by omega
  obtain ⟨α, g, φ, hlift, hmat, hiso, hinv⟩ :=
    unitaryAutClassification_isometry_of_card hK hp hq (d := 4) (by norm_num) X θ hθ hker σ
  obtain ⟨hφ, hαα⟩ := hinv hσ2
  have hperf2 : Group.IsPerfect (Su K p f 2) := isPerfect_suTwo_of_card hK hq
  have hfix0 : ∀ A : Su K p f 2, α (blockEmb K p f 4 2 0 (by norm_num) A) =
      blockEmb K p f 4 2 0 (by norm_num) A := fun A =>
    DFunLike.congr_fun (lift_comp_eq_of_fixed hker hlift (blockEmb K p f 4 2 0 (by norm_num))
      h0) A
  have hα2 : ∀ x, α (α x) = x := fun x => DFunLike.congr_fun hαα x
  have hblock2 : (∀ A : Su K p f 2, α (blockEmb K p f 4 2 2 (by norm_num) A) =
      blockEmb K p f 4 2 2 (by norm_num) A) → False := by
    intro h
    obtain ⟨A, hA⟩ := hnt
    exact hA (by rw [← hlift, h A])
  set G : Matrix (Fin 4) (Fin 4) K := (g : Matrix (Fin 4) (Fin 4) K) with hG
  set Gi : Matrix (Fin 4) (Fin 4) K := ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
    with hGi
  have hGGi : G * Gi = 1 := by rw [hG, hGi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hGiG : Gi * G = 1 := by rw [hG, hGi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  rcases su4_shape_one hK hp α g φ hmat hfix0 with ⟨hφ1, a, ha, hGa⟩ | ⟨hφ1, m, hm, hGm⟩
  ·
    subst hφ1
    have hα' : ∀ x : Su K p f 4, suMat (α x) = G * suMat x * Gi := fun x => by
      have := hmat x
      rw [mapMatrix_refl'] at this
      exact this
    obtain ⟨h22, h23, h32, h33, hGeq⟩ : ∃ h22 h23 h32 h33 : K,
        G = !![a, 0, 0, 0; 0, a, 0, 0; 0, 0, h22, h23; 0, 0, h32, h33] := ⟨_, _, _, _, hGa⟩
    have hiso' := hiso
    rw [hGeq] at hiso'
    obtain ⟨haa, hU⟩ := unitary_inner_entries hiso'
    have hsq : ∀ x : Su K p f 4, (G * G) * suMat x = suMat x * (G * G) := by
      intro x
      have h3 : suMat (α (α x)) = G * (G * suMat x * Gi) * Gi := by rw [hα' (α x), hα' x]
      rw [hα2 x] at h3
      calc (G * G) * suMat x
          = (G * (G * suMat x * Gi) * Gi) * (G * G) := by
            calc (G * G) * suMat x = (G * G) * suMat x * (Gi * (Gi * G) * G) := by
                  rw [hGiG, Matrix.mul_one, hGiG, Matrix.mul_one]
              _ = _ := by simp only [Matrix.mul_assoc]
        _ = suMat x * (G * G) := by rw [← h3]
    have hmixc := hsq (mixSU K p f)
    have hJc := hsq (blockEmb K p f 4 2 2 (by norm_num) (jSU K p f))
    rw [suMat_mixSU, hGeq] at hmixc
    rw [suMat_blockEmb_two_jSU, hGeq] at hJc
    have hH2 := sq_of_commute_inner hmixc hJc
    by_cases hscal : ∃ c' : K, (!![h22, h23; h32, h33] : Matrix (Fin 2) (Fin 2) K) =
        c' • (1 : Matrix (Fin 2) (Fin 2) K)
    ·
      exfalso
      obtain ⟨c', hc'⟩ := hscal
      have e22 := congrFun (congrFun hc' 0) 0
      have e23 := congrFun (congrFun hc' 0) 1
      have e32 := congrFun (congrFun hc' 1) 0
      have e33 := congrFun (congrFun hc' 1) 1
      simp at e22 e23 e32 e33
      apply hblock2
      intro A
      apply suMat_injective
      rw [hα', suMat_blockEmb_two]
      apply alpha_fix_of_comm hGGi
      rw [hGeq]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_four, e22, e23, e32, e33] <;> ring
    ·
      obtain ⟨c₁, d₁, c₂, d₂, hN1, hN2, hX, e1, e2, e3, e4⟩ :=
        exists_orthonormal_eigenbasis (unitaryInvolution K p f) hσ h2 ha haa _ hH2 hscal hU
      simp at e1 e2 e3 e4
      set Mm : Matrix (Fin 4) (Fin 4) K := !![0, 1, 0, 0; 0, 0, 1, 0; c₁, 0, 0, c₂; d₁, 0, 0, d₂]
        with hMm
      have hMiso : conjTr (unitaryInvolution K p f) Mm * Mm = 1 :=
        conjTr_adapted_mul_self (unitaryInvolution K p f) hσσ hN1 hN2 hX
      have hMdet : Mm.det ≠ 0 := by
        have hMMc : Mm * conjTr (unitaryInvolution K p f) Mm = 1 :=
          mul_eq_one_comm.mp hMiso
        have := congrArg Matrix.det hMMc
        rw [Matrix.det_mul, Matrix.det_one] at this
        exact left_ne_zero_of_mul_eq_one this
      let Mgl : GL (Fin 4) K := Matrix.GeneralLinearGroup.mkOfDetNeZero Mm hMdet
      have hMgl : (Mgl : Matrix (Fin 4) (Fin 4) K) = Mm := rfl
      have hMiso' : conjTr (unitaryInvolution K p f) (Mgl : Matrix (Fin 4) (Fin 4) K) *
          (Mgl : Matrix (Fin 4) (Fin 4) K) = 1 := hMiso
      have hMMi : Mm * ((Mgl⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 := by
        rw [← hMgl, ← Units.val_mul, mul_inv_cancel, Units.val_one]
      have hMiM : ((Mgl⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * Mm = 1 := by
        rw [← hMgl, ← Units.val_mul, inv_mul_cancel, Units.val_one]
      have hGM : G * Mm = Mm * !![a, 0, 0, 0; 0, a, 0, 0; 0, 0, a, 0; 0, 0, 0, -a] := by
        rw [hGeq, hMm]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
        · linear_combination e1
        · linear_combination e3
        · linear_combination e2
        · linear_combination e4
      have hGYM : (G * suMat (negTwoSU K p f)) * Mm =
          Mm * !![-a, 0, 0, 0; 0, a, 0, 0; 0, 0, a, 0; 0, 0, 0, a] := by
        rw [suMat_negTwoSU, hGeq, hMm]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
        · linear_combination -e1
        · linear_combination -e3
        · linear_combination -e2
        · linear_combination -e4
      have hYinv : (negTwoSU K p f)⁻¹ = negTwoSU K p f :=
        inv_eq_of_mul_eq_one_right negTwoSU_mul_self
      refine su_closure_fix_eq_top hK hq2 θ hθ σ α hlift (negTwoSU K p f)
        (suConjHom hK Mgl hMiso') (suConjHom_surjective hK Mgl hMiso') ?_ ?_
      · intro i hi s hs
        obtain ⟨A, rfl⟩ := hs
        apply suMat_injective
        rw [hα', suMat_suConjHom, suMat_blockEmb2_three, hMgl]
        apply alpha_fix_of_comm hGGi
        refine conj_comm_of_eigen hGM hMMi hMiM ?_
        fin_cases i
        · exact (delta1_comm_block a (suMat A)).1
        · exact (delta1_comm_block a (suMat A)).2
        · exact absurd rfl hi
      · intro i hi s hs
        obtain ⟨A, rfl⟩ := hs
        apply suMat_injective
        rw [hα', suMat_mul, suMat_mul, suMat_suConjHom, suMat_blockEmb2_three, hMgl, hYinv,
          suMat_negTwoSU]
        have hcomm : (G * !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1]) *
            (Mm * blockMat 4 i (suMat A) * ((Mgl⁻¹ : GL (Fin 4) K) :
              Matrix (Fin 4) (Fin 4) K)) = (Mm * blockMat 4 i (suMat A) *
                ((Mgl⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) *
                  (G * !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1]) := by
          refine conj_comm_of_eigen (by rw [← suMat_negTwoSU]; exact hGYM) hMMi hMiM ?_
          fin_cases i
          · exact absurd rfl hi
          · exact (delta2_comm_block a (suMat A)).1
          · exact (delta2_comm_block a (suMat A)).2
        have hYY : !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1] *
            !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1] =
              (1 : Matrix (Fin 4) (Fin 4) K) := by
          ext i j
          fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
        calc G * (!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1] *
              (Mm * blockMat 4 i (suMat A) * ((Mgl⁻¹ : GL (Fin 4) K) :
                Matrix (Fin 4) (Fin 4) K)) *
                !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1]) * Gi
            = (G * !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1]) *
                (Mm * blockMat 4 i (suMat A) * ((Mgl⁻¹ : GL (Fin 4) K) :
                  Matrix (Fin 4) (Fin 4) K)) *
                (!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1] * Gi) := by
              simp only [Matrix.mul_assoc]
          _ = (Mm * blockMat 4 i (suMat A) * ((Mgl⁻¹ : GL (Fin 4) K) :
                Matrix (Fin 4) (Fin 4) K)) *
                (G * !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1]) *
                (!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1] * Gi) := by rw [hcomm]
          _ = Mm * blockMat 4 i (suMat A) *
                ((Mgl⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
              calc (Mm * blockMat 4 i (suMat A) * ((Mgl⁻¹ : GL (Fin 4) K) :
                    Matrix (Fin 4) (Fin 4) K)) *
                    (G * !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1]) *
                    (!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1] * Gi)
                  = (Mm * blockMat 4 i (suMat A) * ((Mgl⁻¹ : GL (Fin 4) K) :
                    Matrix (Fin 4) (Fin 4) K)) *
                    (G * (!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1] *
                      !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1]) * Gi) := by
                    simp only [Matrix.mul_assoc]
                _ = _ := by rw [hYY, Matrix.mul_one, hGGi, Matrix.mul_one]
  ·
    exfalso
    apply hblock2
    subst hφ1
    have hα' : ∀ x : Su K p f 4, suMat (α x) =
        G * (suMat x).map (unitaryInvolution K p f) * Gi := fun x => by
      have := hmat x
      rwa [RingEquiv.mapMatrix_apply] at this
    obtain ⟨h22, h23, h32, h33, hGeq⟩ : ∃ h22 h23 h32 h33 : K,
        G = !![0, m, 0, 0; -m, 0, 0, 0; 0, 0, h22, h23; 0, 0, h32, h33] := ⟨_, _, _, _, hGm⟩
    have hcomm : ∀ x : Su K p f 4, (G * G.map (unitaryInvolution K p f)) * suMat x =
        suMat x * (G * G.map (unitaryInvolution K p f)) := by
      intro x
      refine comm_of_sq_conj hσσ hGGi hGiG ?_
      have h3 : suMat (α (α x)) = G * ((G * (suMat x).map (unitaryInvolution K p f) * Gi).map
          (unitaryInvolution K p f)) * Gi := by rw [hα' (α x), hα' x]
      rw [hα2 x] at h3
      exact h3
    have hmixc := hcomm (mixSU K p f)
    have hJc := hcomm (blockEmb K p f 4 2 2 (by norm_num) (jSU K p f))
    rw [suMat_mixSU, hGeq] at hmixc
    rw [suMat_blockEmb_two_jSU, hGeq] at hJc
    have hΛ := lambda_scalar_graph hmixc hJc
    have hiso' := hiso
    rw [hGeq] at hiso'
    have hmm := graph_iso_norm hiso'
    rw [← hGeq] at hΛ
    have hGc : G = (-1 : K) • Gᵀ := by
      have := eq_smul_transpose hiso hΛ
      rwa [show -(m * unitaryInvolution K p f m) = -1 by rw [mul_comm, hmm]] at this
    have e22 := congrFun (congrFun hGc 2) 2
    have e33 := congrFun (congrFun hGc 3) 3
    have e23 := congrFun (congrFun hGc 2) 3
    rw [hGeq] at e22 e33 e23
    simp at e22 e33 e23
    have h22z : h22 = 0 := by
      have : (2 : K) * h22 = 0 := by linear_combination e22
      exact (mul_eq_zero.mp this).resolve_left h2
    have h33z : h33 = 0 := by
      have : (2 : K) * h33 = 0 := by linear_combination e33
      exact (mul_eq_zero.mp this).resolve_left h2
    have h32v : h32 = -h23 := by linear_combination e23
    intro A
    apply suMat_injective
    rw [hα', suMat_blockEmb_two]
    apply alpha_fix_of_rel hGGi
    rw [hGeq, h22z, h33z, h32v]
    exact graph_block2_commute (det_suMat A) A.2.2

end Main

end CFSG.ClassicalInvolution.Asc77.T8W
