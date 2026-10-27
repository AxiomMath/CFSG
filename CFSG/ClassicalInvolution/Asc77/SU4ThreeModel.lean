module

public import CFSG.ClassicalInvolution.Asc77.SU4ThreeStruct
public import CFSG.ClassicalInvolution.Asc77.SU4Bridge
public import CFSG.ClassicalInvolution.Asc77.SU4Hyp
public import CFSG.ClassicalInvolution.Asc77.SU4Trace
public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutMain
public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutSimilitude

public section

namespace CFSG.ClassicalInvolution.RouteD.SU4Pattern

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Models.TwistedPairs CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.BorelTits CFSG.LieType.Steinberg
  CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.ModelFacts.UnitaryAut
open scoped MatrixGroups

section Linear

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

@[expose] def LinearLift {X : Type} [Group X] (ψ : Su K p f 4 →* X) (τ : X → X) : Prop :=
  ∃ G Gi : Matrix (Fin 4) (Fin 4) K, G * Gi = 1 ∧ Gi * G = 1 ∧
    conjTr (unitaryInvolution K p f) G * G = 1 ∧
    ∀ y : Su K p f 4, ∃ y' : Su K p f 4, suMat y' = G * suMat y * Gi ∧ τ (ψ y) = ψ y'

theorem LinearLift.of_lift {X : Type} [Group X] {ψ : Su K p f 4 →* X} {τ : X ≃* X}
    (α : Su K p f 4 →* Su K p f 4) (g : GL (Fin 4) K) (φ : K ≃+* K) (hφ : ∀ y, φ y = y)
    (hα : ∀ x, ψ (α x) = τ (ψ x))
    (hmat : ∀ x, ((α x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (g : Matrix (Fin 4) (Fin 4) K) *
        φ.mapMatrix ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))
    (hiso : conjTr (unitaryInvolution K p f) (g : Matrix (Fin 4) (Fin 4) K) *
      (g : Matrix (Fin 4) (Fin 4) K) = 1) : LinearLift ψ τ := by
  refine ⟨(g : Matrix (Fin 4) (Fin 4) K), ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K),
    ?_, ?_, hiso, fun y => ⟨α y, ?_, (hα y).symm⟩⟩
  · rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  · rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  · have h1 := hmat y
    have h2 : φ.mapMatrix ((y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        ((y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
      ext i j
      exact hφ _
    rw [h2] at h1
    exact h1

theorem conjTr_suMat_eq_inv {n : ℕ} (y : Su K p f n) :
    conjTr (unitaryInvolution K p f) (suMat y) = suMat y⁻¹ := by
  have h1 : conjTr (unitaryInvolution K p f) (suMat y) * suMat y = 1 := y.2.2
  calc conjTr (unitaryInvolution K p f) (suMat y)
      = conjTr (unitaryInvolution K p f) (suMat y) * (suMat y * suMat y⁻¹) := by
        rw [suMat_mul_suMat_inv, Matrix.mul_one]
    _ = suMat y⁻¹ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem LinearLift.comp_conj {X : Type} [Group X] {ψ : Su K p f 4 →* X} {τ : X → X}
    (h : LinearLift ψ τ) (g₁ : Su K p f 4) :
    LinearLift (ψ.comp (MulAut.conj g₁).toMonoidHom) τ := by
  obtain ⟨G, Gi, hGGi, hGiG, hiso, hy⟩ := h
  set σ := unitaryInvolution K p f with hσ
  set C : Matrix (Fin 4) (Fin 4) K := suMat g₁ with hC
  set Ci : Matrix (Fin 4) (Fin 4) K := suMat g₁⁻¹ with hCi
  have hCCi : C * Ci = 1 := suMat_mul_suMat_inv g₁
  have hCiC : Ci * C = 1 := suMat_inv_mul_suMat g₁
  have hCtr : conjTr σ C = Ci := conjTr_suMat_eq_inv g₁
  have hCitr : conjTr σ Ci = C := by
    rw [hCi, conjTr_suMat_eq_inv, inv_inv]
  refine ⟨Ci * G * C, Ci * Gi * C, ?_, ?_, ?_, ?_⟩
  · calc Ci * G * C * (Ci * Gi * C) = Ci * G * (C * Ci) * Gi * C := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hCCi, Matrix.mul_one, Matrix.mul_assoc Ci, hGGi, Matrix.mul_one, hCiC]
  · calc Ci * Gi * C * (Ci * G * C) = Ci * Gi * (C * Ci) * G * C := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hCCi, Matrix.mul_one, Matrix.mul_assoc Ci, hGiG, Matrix.mul_one, hCiC]
  · rw [conjTr_mul, conjTr_mul, hCtr, hCitr]
    calc Ci * (conjTr σ G * C) * (Ci * G * C) = Ci * conjTr σ G * (C * Ci) * G * C := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hCCi, Matrix.mul_one, Matrix.mul_assoc Ci, hiso, Matrix.mul_one, hCiC]
  · intro y
    obtain ⟨y'', hy'', hτ⟩ := hy (g₁ * y * g₁⁻¹)
    refine ⟨g₁⁻¹ * y'' * g₁, ?_, ?_⟩
    · rw [suMat_mul, suMat_mul, hy'', suMat_mul, suMat_mul]
      simp only [Matrix.mul_assoc]
      rfl
    · have e : g₁ * (g₁⁻¹ * y'' * g₁) * g₁⁻¹ = y'' := by group
      show τ (ψ (g₁ * y * g₁⁻¹)) = ψ (g₁ * (g₁⁻¹ * y'' * g₁) * g₁⁻¹)
      rw [e]
      exact hτ

theorem exists_hom_of_linear {X : Type} [Group X] {ψ : Su K p f 4 →* X} {τ : X ≃* X}
    {G Gi : Matrix (Fin 4) (Fin 4) K} (hGiG : Gi * G = 1)
    (hy : ∀ y : Su K p f 4, ∃ y' : Su K p f 4, suMat y' = G * suMat y * Gi ∧ τ (ψ y) = ψ y') :
    ∃ α : Su K p f 4 →* Su K p f 4, (∀ y, suMat (α y) = G * suMat y * Gi) ∧
      ∀ y, ψ (α y) = τ (ψ y) := by
  classical
  choose c hc hcτ using hy
  refine ⟨MonoidHom.mk' c fun y₁ y₂ => ?_, hc, fun y => (hcτ y).symm⟩
  apply suMat_injective
  rw [suMat_mul, hc, hc, hc, suMat_mul]
  calc G * (suMat y₁ * suMat y₂) * Gi
      = G * suMat y₁ * (Gi * G) * suMat y₂ * Gi := by
        rw [hGiG, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
    _ = G * suMat y₁ * Gi * (G * suMat y₂ * Gi) := by simp only [Matrix.mul_assoc]

end Linear

section NotInner

variable {F : Type} [Field F] [Finite F]

theorem not_inner_diagConj2 (hF : Nat.card F % 4 = 3) :
    ¬ ∃ s₀ : SL(2, F), ∀ s : SL(2, F), diagConj2 (-1) 1 s = s₀ * s * s₀⁻¹ := by
  classical
  rintro ⟨s₀, h⟩
  let U : SL(2, F) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩
  let L : SL(2, F) := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two_of]⟩
  have hU : diagConj2 (-1) 1 U * s₀ = s₀ * U := by rw [h U]; group
  have hL : diagConj2 (-1) 1 L * s₀ = s₀ * L := by rw [h L]; group
  have hU' := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F)) hU
  have hL' := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F)) hL
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_diagConj2] at hU' hL'
  have u00 := congrFun (congrFun hU' 0) 0
  have u01 := congrFun (congrFun hU' 0) 1
  have l00 := congrFun (congrFun hL' 0) 0
  have l01 := congrFun (congrFun hL' 0) 1
  simp [U, L, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply] at u00 u01 l00 l01
  have hc : (s₀ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by linear_combination u00
  have hd : (s₀ : Matrix (Fin 2) (Fin 2) F) 1 1 = -(s₀ : Matrix (Fin 2) (Fin 2) F) 0 0 := by
    linear_combination -u01
  have hb : (s₀ : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by linear_combination l00
  have hdet := s₀.2
  rw [Matrix.det_fin_two, hc, hd, hb] at hdet
  have := Fintype.ofFinite F
  have hsq : IsSquare (-1 : F) := ⟨(s₀ : Matrix (Fin 2) (Fin 2) F) 0 0, by linear_combination hdet⟩
  rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card] at hsq
  exact hsq hF

end NotInner

section Core

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem core_fixed_short_linear (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hq3 : p ^ f % 4 = 3) {F : Type} [Field F] [Finite F] (ε : F ≃+* fixedSubfield K p f)
    {X : Type} [Group X] (ψ : Su K p f 4 →* X)
    (hker : ψ.ker ≤ Subgroup.center (Su K p f 4)) (τ : X ≃* X) (hτ : ∀ x, τ (τ x) = x)
    (θ : SL(2, F) →* X) (hθ : θ.range = (rootSU2 K p f (by norm_num : 2 ≤ 4)).map ψ)
    (hθτ : ∀ s, τ (θ s) = θ (diagConj2 (-1) 1 s)) (hlin : LinearLift ψ τ) :
    ∃ (Q : GL (Fin 4) K) (hQ : conjTr (unitaryInvolution K p f) (Q : Matrix (Fin 4) (Fin 4) K) *
        (Q : Matrix (Fin 4) (Fin 4) K) = antidiag 4),
      (∀ r : Fin 4, r = 0 ∨ r = 1 → (Q : Matrix (Fin 4) (Fin 4) K) r 0 = 0 ∧
        (Q : Matrix (Fin 4) (Fin 4) K) r 3 = 0) ∧
      ∀ (y : Su K p f 4) (M : Matrix (Fin 4) (Fin 4) K), M * levi4 = levi4 * M →
        suMat y = (Q : Matrix (Fin 4) (Fin 4) K) * M *
          ((Q⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) → τ (ψ y) = ψ y := by
  classical
  set σ := unitaryInvolution K p f with hσ
  have hσσ : ∀ c, σ (σ c) = c := unitaryInvolution_involutive hK
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two hp2
  have hn : (2 : ℕ) ≤ 4 := by norm_num
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hcardF : Nat.card F = p ^ f := by
    rw [Nat.card_congr ε.toEquiv, card_fixedSubfield hK]
  have hF3 : Nat.card F % 4 = 3 := by rw [hcardF]; exact hq3
  obtain ⟨G, Gi, hGGi, hGiG, hGiso, hy⟩ := hlin
  obtain ⟨α, hαmat, hα⟩ := exists_hom_of_linear (ψ := ψ) (τ := τ) hGiG hy
  set g : GL (Fin 4) K := ⟨G, Gi, hGGi, hGiG⟩ with hg
  have hmat : ∀ x, ((α x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (g : Matrix (Fin 4) (Fin 4) K) *
        (RingEquiv.refl K).mapMatrix ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := fun x => by
    have : (RingEquiv.refl K).mapMatrix ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
      ext i j
      rfl
    rw [this]
    exact hαmat x
  obtain ⟨θ', hθ'inj, hθ'range, -, hequiv, -⟩ :=
    exists_chart_lift hK hp2 hq ε ψ hker θ hθ τ (-1) hθτ α g (RingEquiv.refl K) hα hmat
  have hperf : Group.IsPerfect (Su K p f 4) :=
    ⟨(CFSG.ClassicalInvolution.ModelFacts.open_isQuasisimple_su hK hq (k := 4) (by norm_num)).1⟩
  have hα2 : ∀ x, α (α x) = x := by
    have := hom_eq_of_central_ker_perfect (G := Su K p f 4) (θ := ψ) hker
      (α.comp α) (MonoidHom.id _) (fun x => by
        simp only [MonoidHom.comp_apply, MonoidHom.id_apply]
        rw [hα, hα, hτ])
    exact fun x => DFunLike.congr_fun this x
  have hUF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
    ⟨Fact.out, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hGsq : ∃ s : K, G * G = s • (1 : Matrix (Fin 4) (Fin 4) K) := by
    refine eq_smul_one_of_commute hUF hp2 (by norm_num : 3 ≤ 4) (G * G) fun y hy => ?_
    have hy' : y ∈ SUid σ 4 := by rw [SUid_eq_statedSU hK]; exact hy
    have h4 := hα2 ⟨y, hy'⟩
    have h5 : suMat (α (α ⟨y, hy'⟩)) = (G * G) * (y : Matrix (Fin 4) (Fin 4) K) * (Gi * Gi) := by
      rw [hαmat (α ⟨y, hy'⟩), hαmat ⟨y, hy'⟩]
      simp only [Matrix.mul_assoc]
      rfl
    rw [h4] at h5
    have h6 : (Gi * Gi) * (G * G) = 1 := by
      calc Gi * Gi * (G * G) = Gi * (Gi * G) * G := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hGiG, Matrix.mul_one, hGiG]
    calc G * G * (y : Matrix (Fin 4) (Fin 4) K)
        = (G * G * (y : Matrix (Fin 4) (Fin 4) K) * (Gi * Gi)) * (G * G) := by
          rw [Matrix.mul_assoc (G * G * (y : Matrix (Fin 4) (Fin 4) K)), h6, Matrix.mul_one]
      _ = (y : Matrix (Fin 4) (Fin 4) K) * (G * G) := by rw [← h5]; rfl
  have hRθ : ∀ A : Su K p f 2, ∃ s : SL(2, F), θ' s = blockEmb K p f 4 2 0 (by omega) A := by
    intro A
    have : blockEmb K p f 4 2 0 (by omega) A ∈ rootSU2 K p f hn := ⟨A, rfl⟩
    rw [← hθ'range] at this
    exact this
  have hRθ' : ∀ s : SL(2, F), ∃ A : Su K p f 2, blockEmb K p f 4 2 0 (by omega) A = θ' s := by
    intro s
    have : θ' s ∈ rootSU2 K p f hn := by rw [← hθ'range]; exact ⟨s, rfl⟩
    exact this
  have hnorm : ∀ A : Su K p f 2, ∃ A' : Matrix (Fin 2) (Fin 2) K,
      G * blockMat 4 0 (suMat A) = blockMat 4 0 A' * G := by
    intro A
    obtain ⟨s, hs⟩ := hRθ A
    have h1 : α (blockEmb K p f 4 2 0 (by omega) A) ∈ rootSU2 K p f hn := by
      rw [← hs, hequiv, ← hθ'range]
      exact ⟨_, rfl⟩
    obtain ⟨A'', hA''⟩ := h1
    refine ⟨suMat A'', ?_⟩
    have h2' := congrArg suMat hA''
    rw [hαmat] at h2'
    have e1 : suMat (blockEmb K p f 4 2 0 (by omega) A'') = blockMat 4 0 (suMat A'') := rfl
    have e2 : suMat (blockEmb K p f 4 2 0 (by omega) A) = blockMat 4 0 (suMat A) := rfl
    rw [e1, e2] at h2'
    calc G * blockMat 4 0 (suMat A) = G * blockMat 4 0 (suMat A) * (Gi * G) := by
          rw [hGiG, Matrix.mul_one]
      _ = (G * blockMat 4 0 (suMat A) * Gi) * G := by simp only [Matrix.mul_assoc]
      _ = blockMat 4 0 (suMat A'') * G := by rw [← h2']
  have hnon : ∀ r : Su K p f 2, ∃ A : Su K p f 2,
      G * blockMat 4 0 (suMat A) ≠ blockMat 4 0 (suMat r * suMat A * suMat r⁻¹) * G := by
    intro r
    by_contra hcon
    push Not at hcon
    have hαr : ∀ A : Su K p f 2, α (blockEmb K p f 4 2 0 (by omega) A) =
        blockEmb K p f 4 2 0 (by omega) (r * A * r⁻¹) := by
      intro A
      apply suMat_injective
      rw [hαmat]
      show G * blockMat 4 0 (suMat A) * Gi = blockMat 4 0 (suMat (r * A * r⁻¹))
      rw [suMat_mul, suMat_mul, hcon A, Matrix.mul_assoc, hGGi, Matrix.mul_one]
    obtain ⟨s₀, hs₀⟩ := hRθ r
    refine not_inner_diagConj2 (F := F) hF3 ⟨s₀, fun s => ?_⟩
    apply hθ'inj
    obtain ⟨A, hA⟩ := hRθ' s
    rw [← hequiv, map_mul, map_mul, map_inv, hs₀, ← hA, hαr, map_mul, map_mul, map_inv]
  obtain ⟨a, H₁, H₂, hGform, ha, hiso₁, hsq₁, hn₁, hn₁', hiso₂, hsq₂, hn₂, hn₂'⟩ :=
    block_data_three hK hp2 hq hq3 hGiso hGsq hnorm hnon
  obtain ⟨Q, hQ, hsupp, heig⟩ :=
    exists_witt_eigenbasis σ hσσ h2 ha hiso₁ hsq₁ hn₁ hn₁' hiso₂ hsq₂ hn₂ hn₂'
  refine ⟨Q, hQ, hsupp, ?_⟩
  intro y M hM hy
  set Qm : Matrix (Fin 4) (Fin 4) K := (Q : Matrix (Fin 4) (Fin 4) K) with hQm
  set Qi : Matrix (Fin 4) (Fin 4) K := ((Q⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hQi
  have hQQi : Qm * Qi = 1 := by rw [hQm, hQi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hQiQ : Qi * Qm = 1 := by rw [hQm, hQi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hD : Matrix.diagonal ![a, a, -a, -a] = a • (levi4 : Matrix (Fin 4) (Fin 4) K) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [levi4]
  have hHeq : G = blockMat 4 0 H₁ * blockMat 4 2 H₂ := hGform
  have hGQ : G * Qm = Qm * (a • levi4) := by
    rw [hHeq, ← hD]
    exact heig
  have hQiG : Qi * G = (a • levi4) * Qi := by
    calc Qi * G = Qi * G * (Qm * Qi) := by rw [hQQi, Matrix.mul_one]
      _ = Qi * (G * Qm) * Qi := by simp only [Matrix.mul_assoc]
      _ = Qi * (Qm * (a • levi4)) * Qi := by rw [hGQ]
      _ = (a • levi4) * Qi := by simp only [← Matrix.mul_assoc, hQiQ, Matrix.one_mul]
  have hcm : (a • (levi4 : Matrix (Fin 4) (Fin 4) K)) * M = M * (a • levi4) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hM]
  have hcommy : G * suMat y = suMat y * G := by
    have hy' : suMat y = Qm * M * Qi := hy
    rw [hy']
    calc G * (Qm * M * Qi) = (G * Qm) * M * Qi := by simp only [Matrix.mul_assoc]
      _ = Qm * ((a • levi4) * M) * Qi := by rw [hGQ]; simp only [Matrix.mul_assoc]
      _ = Qm * (M * (a • levi4)) * Qi := by rw [hcm]
      _ = Qm * M * ((a • levi4) * Qi) := by simp only [Matrix.mul_assoc]
      _ = Qm * M * (Qi * G) := by rw [hQiG]
      _ = Qm * M * Qi * G := by simp only [Matrix.mul_assoc]
  have hαy : α y = y := by
    apply suMat_injective
    rw [hαmat y, hcommy, Matrix.mul_assoc, hGGi, Matrix.mul_one]
  calc τ (ψ y) = ψ (α y) := (hα y).symm
    _ = ψ y := by rw [hαy]

end Core

section Outer

variable {p f : ℕ} [Fact p.Prime]

theorem exists_fixed_shortPair_linear (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hq3 : p ^ f % 4 = 3)
    {b c : GaloisField p f} [Fact (∀ r : GaloisField p f, r ^ 2 ≠ -c + b * r)]
    {hirr : ∀ s : GaloisField p f, s ^ 2 + b * s + c ≠ 0} (hg6 : SpinMinus6Generated hirr)
    {X : Type} [Group X] (ψ : Su (GaloisField p (2 * f)) p f 4 →* X)
    (hker : ψ.ker ≤ Subgroup.center (Su (GaloisField p (2 * f)) p f 4))
    (τ : X ≃* X) (hτ : ∀ x, τ (τ x) = x)
    {R : Subgroup (Su (GaloisField p (2 * f)) p f 4)}
    (hR : R ∈ longRootSetU (K := GaloisField p (2 * f)) (p := p) (f := f) (by norm_num : 2 ≤ 4))
    (θ : SL(2, GaloisField p f) →* X) (hθ : θ.range = R.map ψ)
    (hθτ : ∀ s, τ (θ s) = θ (diagConj2 (-1) 1 s)) (hlin : LinearLift ψ τ) :
    ∃ (S : Subgroup (Su (GaloisField p (2 * f)) p f 4)) (W : Subgroup X),
      TwistedB2BlockPair hirr W (R.map ψ) (S.map ψ) ∧ R ⊔ S = ⊤ ∧
        ∀ y ∈ S, τ (ψ y) = ψ y := by
  classical
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hK := card_galoisField_two_mul_eq (p := p) hq
  obtain ⟨g₁, hg₁⟩ := (mem_longRootSetU_iff (K := GaloisField p (2 * f)) (p := p) (f := f)
    (by norm_num : 2 ≤ 4)).mp hR
  set ψ₁ : Su (GaloisField p (2 * f)) p f 4 →* X := ψ.comp (MulAut.conj g₁).toMonoidHom with hψ₁
  have hψ₁ker : ψ₁.ker ≤ Subgroup.center (Su (GaloisField p (2 * f)) p f 4) := by
    intro y hy
    have h1 : (MulAut.conj g₁).toMonoidHom y ∈ ψ.ker := hy
    have h2 := hker h1
    exact (MulEquivClass.apply_mem_center_iff (MulAut.conj g₁)).1 h2
  have hθ₁ : θ.range = (rootSU2 (GaloisField p (2 * f)) p f (by norm_num : 2 ≤ 4)).map ψ₁ := by
    rw [hθ, hg₁, Subgroup.map_map]
  have hlin₁ : LinearLift ψ₁ τ := hlin.comp_conj g₁
  have hcardF : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  have hcardk : Nat.card (fixedSubfield (GaloisField p (2 * f)) p f) = p ^ f :=
    card_fixedSubfield hK
  obtain ⟨ε⟩ : Nonempty (GaloisField p f ≃+* fixedSubfield (GaloisField p (2 * f)) p f) := by
    have := Fintype.ofFinite (GaloisField p f)
    have := Fintype.ofFinite (fixedSubfield (GaloisField p (2 * f)) p f)
    exact ⟨FiniteField.ringEquivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcardF, hcardk])⟩
  have hcore := core_fixed_short_linear hK hp2 hq hq3 ε ψ₁ hψ₁ker τ hτ θ hθ₁ hθτ hlin₁
  obtain ⟨Q, hQ, hsupp, hfix⟩ := hcore
  obtain ⟨Φ, hΦlevi, hΦlb⟩ := exists_phiSU_bridge hp2 hf hirr
  set e' : spinGroup (Spin.quadMinus 3 (GaloisField p f) b c) ≃*
      Su (GaloisField p (2 * f)) p f 4 := Φ.trans (conjEquiv Q hQ) with he'
  have hlb : (spinMinusModel hirr).lb.range.map e'.toMonoidHom =
      rootSU2 (GaloisField p (2 * f)) p f (by norm_num : 2 ≤ 4) := hΦlb Q hQ hsupp
  have hR₀ : rootSU2 (GaloisField p (2 * f)) p f (by norm_num : 2 ≤ 4) ∈
      longRootSetU (K := GaloisField p (2 * f)) (p := p) (f := f) (by norm_num : 2 ≤ 4) :=
    ⟨_, isLongRootSU2_standard (by norm_num : 2 ≤ 4)⟩
  obtain ⟨hpair, hsup⟩ := twistedPair_of_equiv hp2 hq hg6 e' hR₀ hlb ψ₁ hψ₁ker
  set S₀ : Subgroup (Su (GaloisField p (2 * f)) p f 4) :=
    (spinMinusModel hirr).sb.range.map e'.toMonoidHom with hS₀
  refine ⟨S₀.map (MulAut.conj g₁).toMonoidHom, (ψ₁.comp e'.toMonoidHom).range, ?_, ?_, ?_⟩
  · have h1 : R.map ψ = (rootSU2 (GaloisField p (2 * f)) p f (by norm_num : 2 ≤ 4)).map ψ₁ := by
      rw [hg₁, Subgroup.map_map]
    have h2 : (S₀.map (MulAut.conj g₁).toMonoidHom).map ψ = S₀.map ψ₁ := by
      rw [Subgroup.map_map]
    rw [h1, h2]
    exact hpair
  · rw [hg₁, ← Subgroup.map_sup, hsup, Subgroup.map_top]
    exact MonoidHom.range_eq_top.mpr (MulAut.conj g₁).surjective
  · rintro _ ⟨y₀, hy₀, rfl⟩
    obtain ⟨x₀, hx₀, rfl⟩ := hy₀
    have hψy : ψ ((MulAut.conj g₁).toMonoidHom (e'.toMonoidHom x₀)) =
        ψ₁ (e'.toMonoidHom x₀) := rfl
    rw [hψy]
    refine hfix (e'.toMonoidHom x₀)
      (((Φ x₀ : SU (unitaryInvolution (GaloisField p (2 * f)) p f) 4) :
        GL (Fin 4) (GaloisField p (2 * f))) : Matrix (Fin 4) (Fin 4) (GaloisField p (2 * f)))
      (hΦlevi x₀ hx₀) ?_
    show (((conjEquiv Q hQ (Φ x₀) : Su (GaloisField p (2 * f)) p f 4) :
      GL (Fin 4) (GaloisField p (2 * f))) : Matrix (Fin 4) (Fin 4) (GaloisField p (2 * f))) = _
    rw [coe_conjEquiv, Units.val_mul, Units.val_mul]

end Outer

end CFSG.ClassicalInvolution.RouteD.SU4Pattern
