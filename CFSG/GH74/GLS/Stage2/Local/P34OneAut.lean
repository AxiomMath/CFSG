module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4LayerE
public import CFSG.RankThree.PartTwo.KFacts.AutPSp4Odd
public import CFSG.RankThree.PartOne.KC.SymplecticSemi
public import CFSG.GH74.GLS.Stage2.Final.ModelLayer

public section

namespace CFSG.GH74.GLS.Stage2.Local.P34

open Matrix Subgroup CFSG.GH74.L5U5 CFSG.GH74.GLS.Stage2.Final.ModelSp
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.Assembly.LowTwoRank
open CFSG.GH74.GLS.Stage2.Final.ModelBlock (PG mkP yP K1 K2 iota1 iota2 sc2 scalar4_eq iota1_apply
  iota2_apply)

section Model

variable {F : Type} [Field F]

@[expose] noncomputable def g0 (ν : Fˣ) : GL (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; -(ν : F), 0] (by simp [det_fin_two])

theorem coe_g0 (ν : Fˣ) :
    ((g0 ν : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; -(ν : F), 0] := rfl

theorem det_g0 (ν : Fˣ) : ((g0 ν : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = ν := by
  rw [coe_g0]; simp [det_fin_two]

theorem g0_mul_g0 (ν : Fˣ) : g0 ν * g0 ν = sc2 (-ν) := by
  apply Units.ext
  rw [Units.val_mul, coe_g0, sc2, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[expose] noncomputable def B0 (ν : Fˣ) : GL (Fin 4) F := diagGL (g0 ν) (g0 ν)

theorem B0_mul_B0 (ν : Fˣ) :
    B0 ν * B0 ν = (Matrix.GeneralLinearGroup.scalar (Fin 4) (-ν) : GL (Fin 4) F) := by
  rw [B0, diagGL_mul, g0_mul_g0, scalar4_eq]

theorem blk4_smul (c : F) (X Y : Matrix (Fin 2) (Fin 2) F) :
    blk4 (c • X) (c • Y) = c • blk4 X Y := by
  rw [blk4_eq_reindex, blk4_eq_reindex, ← map_smul, fromBlocks_smul, smul_zero]

theorem B0_similitude (ν : Fˣ) :
    ((B0 ν : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ * blk4 (J2m F) (J2m F) *
        ((B0 ν : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = (ν : F) • blk4 (J2m F) (J2m F) := by
  rw [B0, coe_diagGL, blk4_transpose, blk4_mul, blk4_mul, transpose_mul_J2m_mul, det_g0,
    blk4_smul]

theorem glSigma_symm_mem_gsp {B : GL (Fin 4) F} {μ : Fˣ}
    (hB : (B : Matrix (Fin 4) (Fin 4) F)ᵀ * blk4 (J2m F) (J2m F) * (B : Matrix (Fin 4) (Fin 4) F) =
      (μ : F) • blk4 (J2m F) (J2m F)) :
    ∃ h : (glSigma F).symm B ∈ gsp 2 F, multiplierUnit (⟨(glSigma F).symm B, h⟩ : gsp 2 F) = μ := by
  set g : GL (Fin 2 ⊕ Fin 2) F := (glSigma F).symm B with hg
  have hBg : glSigma F g = B := (glSigma F).apply_symm_apply B
  have key : (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ * formJ 2 F *
      (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = (μ : F) • formJ 2 F := by
    have e : ∀ X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F,
        Matrix.reindex sigma sigma X = Matrix.reindexAlgEquiv F F sigma X := fun X =>
      (congrFun (Matrix.coe_reindexAlgEquiv F F sigma) X).symm
    have hBm : (B : Matrix (Fin 4) (Fin 4) F) =
        Matrix.reindexAlgEquiv F F sigma (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
      rw [← e, ← coe_glSigma, hBg]
    have hJ : blk4 (J2m F) (J2m F) = Matrix.reindexAlgEquiv F F sigma (formJ 2 F) := by
      rw [← e]; exact reindex_gram.symm
    apply (Matrix.reindexAlgEquiv F F sigma).injective
    rw [hBm, hJ, ← e, Matrix.transpose_reindex, e, e] at hB
    rw [map_smul, map_mul, map_mul, ← hB]
  have hmem : g ∈ gsp 2 F := ⟨μ, key⟩
  exact ⟨hmem, multiplierUnit_eq _ key⟩

end Model

section Outer

variable {F : Type} [Field F]

@[expose] noncomputable def A0g (ν : Fˣ) : gsp 2 F :=
  ⟨(glSigma F).symm (B0 ν), (glSigma_symm_mem_gsp (B0_similitude ν)).1⟩

theorem glSigma_A0g (ν : Fˣ) :
    glSigma F ((A0g ν : gsp 2 F) : GL (Fin 2 ⊕ Fin 2) F) = B0 ν :=
  (glSigma F).apply_symm_apply _

theorem multiplierUnit_A0g (ν : Fˣ) : multiplierUnit (A0g ν : gsp 2 F) = ν :=
  (glSigma_symm_mem_gsp (B0_similitude ν)).2

theorem conjAut_A0g_sq (ν : Fˣ) [Finite F] : conjAut 2 F (A0g ν * A0g ν) = 1 := by
  rw [CFSG.RankThree.PartOne.KCSpComm.conjAut_eq_one_iff (by norm_num)]
  refine ⟨-ν, ?_⟩
  apply (glSigma F).injective
  rw [Subgroup.coe_mul, map_mul, glSigma_A0g, B0_mul_B0, glSigma_scalar]

@[expose] noncomputable def cN (A : gsp 2 F) : MulAut (PG (ModelData.sp F)) :=
  MulAut.congr (spEquiv F) (conjAut 2 F A)

theorem cN_spEquiv (A : gsp 2 F) (x : StatedProj (StatedSp 2 F)) :
    cN A (spEquiv F x) = spEquiv F (conjAut 2 F A x) := by
  simp [cN]

theorem cN_mkP (A : gsp 2 F) (k : ↥(ModelData.sp F).K4) :
    ∃ k' : ↥(ModelData.sp F).K4,
      (k' : GL (Fin 4) F) = glSigma F (A : GL (Fin 2 ⊕ Fin 2) F) * k *
        (glSigma F (A : GL (Fin 2 ⊕ Fin 2) F))⁻¹ ∧
      cN A (mkP (ModelData.sp F) k) = mkP (ModelData.sp F) k' := by
  obtain ⟨g, rfl⟩ := (spMulEquiv (F := F)).surjective k
  refine ⟨spMulEquiv (conjSp 2 F A g), ?_, ?_⟩
  · rw [coe_spMulEquiv, coe_spMulEquiv, coe_conjSp, map_mul, map_mul, map_inv]
  · have h1 : mkP (ModelData.sp F) (spMulEquiv g) = spEquiv F (QuotientGroup.mk g) :=
      (spEquiv_mk g).symm
    have h2 : mkP (ModelData.sp F) (spMulEquiv (conjSp 2 F A g)) =
        spEquiv F (QuotientGroup.mk (conjSp 2 F A g)) := (spEquiv_mk _).symm
    rw [h1, h2, cN_spEquiv]
    rfl

theorem cN_yP (ν : Fˣ) : cN (A0g ν : gsp 2 F) (yP (ModelData.sp F)) = yP (ModelData.sp F) := by
  obtain ⟨k', hk', hk⟩ := cN_mkP (A0g ν : gsp 2 F) (ModelData.sp F).yK
  show cN (A0g ν : gsp 2 F) (mkP (ModelData.sp F) (ModelData.sp F).yK) = _
  rw [hk]
  congr 1
  apply Subtype.ext
  rw [hk', glSigma_A0g]
  show B0 ν * yGL F * (B0 ν)⁻¹ = yGL F
  rw [B0, mul_inv_eq_iff_eq_mul]
  exact CFSG.GH74.GLS.Stage2.Final.ModelSp.diagGL_comm_yGL _ _

theorem g0_conj_mem_H2 (ν : Fˣ) {a : GL (Fin 2) F} (ha : a ∈ (ModelData.sp F).H2) :
    g0 ν * a * (g0 ν)⁻¹ ∈ (ModelData.sp F).H2 := by
  rw [ModelData.mem_H2] at ha ⊢
  obtain ⟨-, hdet⟩ := ha
  have hd : ((g0 ν * a * (g0 ν)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    rw [Units.val_mul, Units.val_mul, Matrix.det_units_conj, hdet]
  exact ⟨mem_U2_sp.2 hd, hd⟩

theorem cN_K1 (ν : Fˣ) {x : PG (ModelData.sp F)} (hx : x ∈ K1 (ModelData.sp F)) :
    cN (A0g ν : gsp 2 F) x ∈ K1 (ModelData.sp F) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨k', hk', hk⟩ := cN_mkP (A0g ν : gsp 2 F)
    ⟨blkL F a, (ModelData.sp F).blkL_mem_K4 a.2⟩
  rw [iota1_apply, hk]
  refine ⟨⟨g0 ν * a * (g0 ν)⁻¹, g0_conj_mem_H2 ν a.2⟩, ?_⟩
  rw [iota1_apply]
  congr 1
  apply Subtype.ext
  rw [hk', glSigma_A0g]
  show blkL F (g0 ν * a * (g0 ν)⁻¹) = B0 ν * blkL F a * (B0 ν)⁻¹
  rw [B0, blkL_apply, blkL_apply, diagGL_inv, diagGL_mul, diagGL_mul]
  simp

theorem cN_K2 (ν : Fˣ) {x : PG (ModelData.sp F)} (hx : x ∈ K2 (ModelData.sp F)) :
    cN (A0g ν : gsp 2 F) x ∈ K2 (ModelData.sp F) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨k', hk', hk⟩ := cN_mkP (A0g ν : gsp 2 F)
    ⟨blkR F a, (ModelData.sp F).blkR_mem_K4 a.2⟩
  rw [iota2_apply, hk]
  refine ⟨⟨g0 ν * a * (g0 ν)⁻¹, g0_conj_mem_H2 ν a.2⟩, ?_⟩
  rw [iota2_apply]
  congr 1
  apply Subtype.ext
  rw [hk', glSigma_A0g]
  show blkR F (g0 ν * a * (g0 ν)⁻¹) = B0 ν * blkR F a * (B0 ν)⁻¹
  rw [B0, blkR_apply, blkR_apply, diagGL_inv, diagGL_mul, diagGL_mul]
  simp

theorem cN_mul_self [Finite F] (ν : Fˣ) : cN (A0g ν : gsp 2 F) * cN (A0g ν : gsp 2 F) = 1 := by
  rw [cN, ← map_mul, ← map_mul, conjAut_A0g_sq, map_one]

theorem congr_conj_eq (x : StatedProj (StatedSp 2 F)) :
    MulAut.congr (spEquiv F) (MulAut.conj x) = MulAut.conj (spEquiv F x) := by
  ext y
  simp [MulAut.congr_apply]

theorem conjAut_not_inner [Finite F] (A : gsp 2 F) (hA : ∀ l : F, l ^ 2 ≠ (multiplierUnit A : F)) :
    conjAut 2 F A ∉ (MulAut.conj : StatedProj (StatedSp 2 F) →* MulAut (StatedProj (StatedSp 2 F))).range := by
  rintro ⟨x, hx⟩
  obtain ⟨g, rfl⟩ := proj_surjective (r := 2) (K := F) x
  have h1 : conjAut 2 F A = conjAut 2 F ⟨g, statedSp_le_gsp g.2⟩ := by
    rw [conjAut_statedSp]; exact hx.symm
  have h2 : conjAut 2 F (⟨g, statedSp_le_gsp g.2⟩⁻¹ * A) = 1 := by
    rw [map_mul, map_inv, h1, inv_mul_cancel]
  obtain ⟨c, hc⟩ := (CFSG.RankThree.PartOne.KCSpComm.conjAut_eq_one_iff (by norm_num) _).1 h2
  have hAeq : (A : GL (Fin 2 ⊕ Fin 2) F) =
      (g : GL (Fin 2 ⊕ Fin 2) F) * Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c := by
    have : ((⟨g, statedSp_le_gsp g.2⟩⁻¹ * A : gsp 2 F) : GL (Fin 2 ⊕ Fin 2) F) =
        (g : GL (Fin 2 ⊕ Fin 2) F)⁻¹ * A := rfl
    rw [this] at hc
    rw [← hc]
    group
  have hspec := multiplier_spec A
  have hgJ := CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff.1 g.2
  have hsc : ((Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = (c : F) • 1 := by
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hmat : ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ * formJ 2 F *
      ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      ((c : F) * c) • formJ 2 F := by
    rw [hAeq, Units.val_mul, mul_transpose_formJ_mul (μ := 1) (by rw [hgJ, one_smul]), hsc,
      transpose_smul, transpose_one, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
      Matrix.mul_one, smul_smul, one_mul, smul_smul]
  have hmul : (multiplier 2 F A : F) = (c : F) * c := by
    have := hspec.symm.trans hmat
    exact smul_formJ_injective 2 this
  exact hA c (by rw [sq]; exact hmul.symm)

theorem cN_not_inner [Finite F] (ν : Fˣ) (hν : ¬ IsSquare (ν : F)) :
    cN (A0g ν : gsp 2 F) ∉
      (MulAut.conj : PG (ModelData.sp F) →* MulAut (PG (ModelData.sp F))).range := by
  rintro ⟨n, hn⟩
  obtain ⟨x, rfl⟩ := (spEquiv F).surjective n
  apply conjAut_not_inner (A0g ν : gsp 2 F)
  · intro l hl
    apply hν
    rw [multiplierUnit_A0g] at hl
    exact ⟨l, by rw [← hl, sq]⟩
  · refine ⟨x, ?_⟩
    apply (MulAut.congr (spEquiv F)).injective
    rw [congr_conj_eq]
    exact hn

end Outer

section NormalForm

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem pow_conjAut_mul_fieldAut (A : gsp 2 K) (σ : K ≃+* K) (n : ℕ) :
    ∃ B : gsp 2 K, (conjAut 2 K A * fieldAut 2 K σ) ^ n = conjAut 2 K B * (fieldAut 2 K σ) ^ n := by
  induction n with
  | zero => exact ⟨1, by simp⟩
  | succ n ih =>
    obtain ⟨B, hB⟩ := ih
    refine ⟨B * gspFieldMap (σ ^ n) A, ?_⟩
    rw [pow_succ, hB, map_mul, ← fieldAut_mul_conjAut_mul_inv (σ ^ n) A, map_pow, pow_succ]
    group

theorem eq_one_of_pow_two_pow (hodd : Odd (Nat.card (K ≃+* K))) {A : gsp 2 K} {σ : K ≃+* K}
    {m : ℕ} (h : (conjAut 2 K A * fieldAut 2 K σ) ^ (2 ^ m) = 1) : σ = 1 := by
  obtain ⟨B, hB⟩ := pow_conjAut_mul_fieldAut A σ (2 ^ m)
  rw [hB] at h
  have h1 : fieldAut 2 K (σ ^ 2 ^ m) = conjAut 2 K B⁻¹ := by
    rw [map_pow, map_inv]
    exact (mul_eq_one_iff_eq_inv.1 h).symm ▸ rfl
  have h2 : σ ^ 2 ^ m = 1 :=
    (CFSG.RankThree.PartTwo.KFacts.fieldAut_mem_range_conjAut_iff (r := 2) (K := K) (by norm_num)).1
      ⟨B⁻¹, h1.symm⟩
  have h3 : orderOf σ ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one h2
  have h4 : orderOf σ ∣ Nat.card (K ≃+* K) := orderOf_dvd_natCard σ
  have h5 : Nat.Coprime (2 ^ m) (Nat.card (K ≃+* K)) :=
    (Nat.coprime_two_left.2 hodd).pow_left m
  have h6 : orderOf σ ∣ Nat.gcd (2 ^ m) (Nat.card (K ≃+* K)) := Nat.dvd_gcd h3 h4
  rw [h5, Nat.dvd_one] at h6
  exact orderOf_eq_one_iff.1 h6

theorem odd_of_pow_mod_eight {p n : ℕ} (h : p ^ n % 8 = 3 ∨ p ^ n % 8 = 5) : Odd n := by
  by_contra hn
  rw [Nat.not_odd_iff_even] at hn
  obtain ⟨k, rfl⟩ := hn
  have hsq : p ^ (k + k) = (p ^ k) ^ 2 := by rw [← pow_mul]; ring_nf
  rw [hsq, Nat.pow_mod] at h
  have : (p ^ k % 8) < 8 := Nat.mod_lt _ (by norm_num)
  interval_cases (p ^ k % 8) <;> simp at h

end NormalForm

section Outer2

variable {F : Type} [Field F] [Finite F]

theorem exists_outer_involution_aut (hq8 : Nat.card F % 8 = 3 ∨ Nat.card F % 8 = 5)
    (Γ : Subgroup (MulAut (PG (ModelData.sp F))))
    (hinn : (MulAut.conj : PG (ModelData.sp F) →* MulAut (PG (ModelData.sp F))).range ≤ Γ)
    {τ : MulAut (PG (ModelData.sp F))} (hτΓ : τ ∈ Γ) {m : ℕ} (hτ : τ ^ 2 ^ m = 1)
    (hτn : τ ∉ (MulAut.conj : PG (ModelData.sp F) →* MulAut (PG (ModelData.sp F))).range) :
    ∃ τ₀ ∈ Γ, τ₀ ∉ (MulAut.conj : PG (ModelData.sp F) →* MulAut (PG (ModelData.sp F))).range ∧
      τ₀ * τ₀ = 1 ∧ τ₀ (yP (ModelData.sp F)) = yP (ModelData.sp F) ∧
      (∀ x ∈ K1 (ModelData.sp F), τ₀ x ∈ K1 (ModelData.sp F)) ∧
      (∀ x ∈ K2 (ModelData.sp F), τ₀ x ∈ K2 (ModelData.sp F)) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hodd : Odd (Nat.card F) := by
    rcases hq8 with h | h <;> exact Nat.odd_iff.2 (by omega)
  have hchar : ringChar F ≠ 2 := by
    intro h2
    have h3 := FiniteField.even_card_iff_char_two.1 h2
    rw [← Nat.card_eq_fintype_card] at h3
    rcases hq8 with h | h <;> omega
  obtain ⟨n, hp, hn⟩ := FiniteField.card F (ringChar F)
  have hK : Nat.card F = ringChar F ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  have hAut := (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hp F hK).1
  have hAodd : Odd (Nat.card (F ≃+* F)) := by
    have : Nat.card (F ≃+* F) = n := hAut
    rw [this]
    exact odd_of_pow_mod_eight (hK ▸ hq8)
  set ψ := spEquiv F with hψ
  set α : MulAut (StatedProj (StatedSp 2 F)) := (MulAut.congr ψ).symm τ with hα
  have hατ : MulAut.congr ψ α = τ := (MulAut.congr ψ).apply_symm_apply τ
  have hα2 : α ^ 2 ^ m = 1 := by
    apply (MulAut.congr ψ).injective
    rw [map_pow, hατ, hτ, map_one]
  have hαn : α ∉ (MulAut.conj : StatedProj (StatedSp 2 F) →*
      MulAut (StatedProj (StatedSp 2 F))).range := by
    rintro ⟨x, hx⟩
    apply hτn
    refine ⟨ψ x, ?_⟩
    rw [← hατ, ← hx, congr_conj_eq]
  obtain ⟨A, σ, hAσ⟩ := CFSG.RankThree.PartTwo.KFacts.psp4_odd_automorphism_normal_form hchar α
  have hσ : σ = 1 := by
    apply eq_one_of_pow_two_pow hAodd (A := A) (m := m)
    rw [← hAσ]; exact hα2
  have hαA : α = conjAut 2 F A := by rw [hAσ, hσ, map_one, mul_one]
  have hmult : ∀ l : F, l ^ 2 ≠ (multiplierUnit A : F) := by
    intro l hl
    exact hαn (hαA ▸ CFSG.ComponentClassification.CatFactsSp4.conjAut_mem_range_of_sq A hl)
  set Γ' : Subgroup (MulAut (StatedProj (StatedSp 2 F))) := Γ.comap (MulAut.congr ψ).toMonoidHom
    with hΓ'
  have hinn' : (MulAut.conj : StatedProj (StatedSp 2 F) →* MulAut (StatedProj (StatedSp 2 F))).range
      ≤ Γ' := by
    rintro _ ⟨x, rfl⟩
    show MulAut.congr ψ (MulAut.conj x) ∈ Γ
    rw [congr_conj_eq]
    exact hinn ⟨_, rfl⟩
  have hAΓ' : conjAut 2 F A ∈ Γ' := by
    show MulAut.congr ψ (conjAut 2 F A) ∈ Γ
    rw [← hαA, hατ]; exact hτΓ
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare hchar
  have ha0 : a ≠ 0 := fun h => ha ⟨0, by rw [h, mul_zero]⟩
  set ν : Fˣ := Units.mk0 a ha0 with hν
  have hνs : ¬ IsSquare (ν : F) := ha
  have hmem := CFSG.ComponentClassification.CatFactsSp4.conjAut_mem_inn_sup A hmult (A0g ν)
  have hmem' : conjAut 2 F (A0g ν) ∈ Γ' := by
    refine (sup_le hinn' ?_) hmem
    exact (Subgroup.zpowers_le).2 hAΓ'
  refine ⟨cN (A0g ν), hmem', cN_not_inner ν hνs, cN_mul_self ν, cN_yP ν, fun x hx => cN_K1 ν hx,
    fun x hx => cN_K2 ν hx⟩

end Outer2

end CFSG.GH74.GLS.Stage2.Local.P34
