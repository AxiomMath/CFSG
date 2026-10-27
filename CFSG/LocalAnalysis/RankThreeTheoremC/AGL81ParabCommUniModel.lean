module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommUniModelRes
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommLinModelMat
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormTransport
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommUniModelCut
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommUniModelFlag

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Uni

open Matrix Module CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.AGLEmbedding.LeviBlock
open scoped commutatorElement Pointwise

section Parity

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem eq_one_of_fixes_traceZero (σ : K ≃+* K) {o : ℕ} (ho : Odd o) (hσo : σ ^ o = 1)
    (hfix : ∀ a : K, a + h.bar a = 0 → σ a = a) : σ = 1 := by
  haveI : CharP K 2 := h.charP
  have hsq : σ * σ = 1 := by
    ext x
    have e1 : σ (x + h.bar x) = x + h.bar x := by
      refine hfix _ ?_
      rw [map_add, h.bar_bar, add_comm (h.bar x) x]
      exact CharTwo.add_self_eq_zero _
    have e2 : σ x + h.bar (σ x) = x + h.bar x := by
      rw [← map_bar_comm h σ x, ← map_add]
      exact e1
    have e3 : σ x + x + h.bar (σ x + x) = 0 := by
      calc σ x + x + h.bar (σ x + x) = (σ x + h.bar (σ x)) + (x + h.bar x) := by
            rw [map_add]
            ring
        _ = (x + h.bar x) + (x + h.bar x) := by rw [e2]
        _ = 0 := CharTwo.add_self_eq_zero _
    have e4 := hfix _ e3
    rw [map_add] at e4
    have : σ (σ x) = x := by linear_combination e4
    simpa using this
  obtain ⟨k, rfl⟩ := ho
  rw [pow_succ, pow_mul, sq, hsq, one_pow, one_mul] at hσo
  exact hσo

end Parity

section Scalar

variable {K : Type} [Field K]

theorem exists_smul_one_of_subsingleton {ι : Type} [Fintype ι] [DecidableEq ι] [Subsingleton ι]
    (B : Matrix ι ι K) : ∃ c : K, B = c • 1 := by
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · exact ⟨0, Subsingleton.elim _ _⟩
  · refine ⟨B i₀ i₀, ?_⟩
    ext i j
    obtain rfl : i = i₀ := Subsingleton.elim _ _
    obtain rfl : j = i := Subsingleton.elim _ _
    simp

theorem subsingleton_hypIndex {s ε : ℕ} (h : 2 * s + ε ≤ 1) : Subsingleton (HypIndex s ε) := by
  rw [← Fintype.card_le_one_iff_subsingleton]
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

end Scalar

section Block

variable {f : ℕ} {K : Type} [Field K] {t s ε : ℕ} (h : UnitaryFieldData 2 f K) (hε : ε ≤ 1)
  {I : Finset ℕ}

theorem four_le_of_isBigBlock (hI : IsTopCut I t) {j : Option ↥I} (hj : IsBigBlock s ε I j) :
    4 ≤ 2 * (t + s) + ε := by
  have ht1 : 1 ≤ t := (hI.le t hI.mem).1
  rcases j with _ | b
  · simp only [IsBigBlock] at hj
    omega
  · simp only [IsBigBlock] at hj
    have := (hI.le b.1 b.2).2
    omega

abbrev blkE (hI : IsTopCut I t) (b : ↥I)
    (M : Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K) :
    Matrix (Fin (b.1 - predCut I b.1)) (Fin (b.1 - predCut I b.1)) K :=
  M.submatrix (eIdx (t + s) ε (a := predCut I b.1) ((hI.le b.1 b.2).2.trans (Nat.le_add_right t s)))
    (eIdx (t + s) ε (a := predCut I b.1) ((hI.le b.1 b.2).2.trans (Nat.le_add_right t s)))

variable {h}

theorem eBlock_scalar [CharP K 2] (hr : 1 ≤ t + s) (hε : ε ≤ 1) {I : Finset ℕ}
    (hI : IsTopCut I t) (γ : semilinearSimilitudes h (t + s) ε)
    (hNF : UniNormFix h hε hI (semilinearAutHom h hr hε γ))
    (hM : FlagCuts I t ((γ : SemiGL (HypIndex (t + s) ε) K).left : Matrix (HypIndex (t + s) ε)
      (HypIndex (t + s) ε) K))
    (hM' : FlagCuts I t (((γ : SemiGL (HypIndex (t + s) ε) K).left⁻¹ : GL (HypIndex (t + s) ε) K) :
      Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K))
    (b : ↥I) (hb2 : 2 ≤ b.1 - predCut I b.1) :
    (∀ x : K, (γ : SemiGL (HypIndex (t + s) ε) K).right x = x) ∧
      ∃ c : K, blkE hI b ((γ : SemiGL (HypIndex (t + s) ε) K).left : Matrix (HypIndex (t + s) ε)
        (HypIndex (t + s) ε) K) = c • 1 := by
  have hbr : b.1 ≤ t + s := (hI.le b.1 b.2).2.trans (Nat.le_add_right t s)
  have hMM' : blkE hI b (((γ : SemiGL (HypIndex (t + s) ε) K).left⁻¹ :
        GL (HypIndex (t + s) ε) K) : Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K) *
      blkE hI b ((γ : SemiGL (HypIndex (t + s) ε) K).left : Matrix (HypIndex (t + s) ε)
        (HypIndex (t + s) ε) K) = 1 := by
    have := submatrix_mul_of_cutPat (eIdx_injective hbr) (mem_range_eIdx hbr)
      (hM'.cut_predCut b.1) (hM.1 b.1 b.2)
    rw [blkE, blkE, ← this, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.submatrix_one _ (eIdx_injective hbr)]
  obtain ⟨hσ, r, -, hr'⟩ := Lin.eq_scalar_of_transvection_rel hb2
    ((γ : SemiGL (HypIndex (t + s) ε) K).right : K →+* K) hMM' (fun i j hij u => by
      obtain ⟨c, hc⟩ := eBlock_relation h hr hε hI γ hNF hM hM' b hb2
        (Matrix.SpecialLinearGroup.transvection hij u)
      refine ⟨c, ?_⟩
      rw [Matrix.SpecialLinearGroup.transvection_coe, map_one_add_single_hyp] at hc
      exact hc)
  exact ⟨hσ, r, hr'⟩

abbrev blkRes (t : ℕ) (M : Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K) :
    Matrix (HypIndex s ε) (HypIndex s ε) K :=
  M.submatrix (resIdx t) (resIdx t)

theorem exists_block_scalar (hr : 1 ≤ t + s) (hε : ε ≤ 1) {I : Finset ℕ} (hI : IsTopCut I t)
    (hbig : ∃ j, IsBigBlock s ε I j) {α : MulAut (hypPSU h (t + s) ε)}
    (hodd : Odd (orderOf α)) (hNF : UniNormFix h hε hI α) :
    ∃ γ : semilinearSimilitudes h (t + s) ε, semilinearAutHom h hr hε γ = α ∧
      (γ : SemiGL (HypIndex (t + s) ε) K).right = 1 ∧
      (∃ μ : K, μ ≠ 0 ∧ h.bar μ = μ ∧
        (((γ : SemiGL (HypIndex (t + s) ε) K).left : Matrix (HypIndex (t + s) ε)
          (HypIndex (t + s) ε) K).map h.bar)ᵀ * hypGram (t + s) ε K *
            ((γ : SemiGL (HypIndex (t + s) ε) K).left : Matrix (HypIndex (t + s) ε)
              (HypIndex (t + s) ε) K) = μ • hypGram (t + s) ε K) ∧
      (∀ c ∈ I, ((γ : SemiGL (HypIndex (t + s) ε) K).left : GL (HypIndex (t + s) ε) K) •
        hypFlag h (t + s) ε c = hypFlag h (t + s) ε c) ∧
      (∀ b : ↥I, ∃ c : K, blkE hI b ((γ : SemiGL (HypIndex (t + s) ε) K).left :
        Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K) = c • 1) ∧
      ∃ c : K, blkRes t ((γ : SemiGL (HypIndex (t + s) ε) K).left :
        Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K) = c • 1 := by
  haveI : CharP K 2 := h.charP
  obtain ⟨j, hj⟩ := hbig
  have h4 := four_le_of_isBigBlock hI hj
  have hn3 : 3 ≤ 2 * (t + s) + ε := by omega
  have hq : ¬(2 * (t + s) + ε = 3 ∧ 2 ^ f = 2) := fun hc => absurd hc.1 (by omega)
  obtain ⟨γ, hγ⟩ := semilinearAutHom_surjective_of_admissible h hr hε hn3 hq α
  have hIr : ∀ c ∈ I, 1 ≤ c ∧ c ≤ t + s := fun c hc =>
    ⟨(hI.le c hc).1, (hI.le c hc).2.trans (Nat.le_add_right t s)⟩
  have hflag := smul_hypFlag_eq_of_map_projFlag h hr hε hIr γ (by rw [hγ]; exact hNF.1)
  have hsim := γ.2
  obtain ⟨μ, hμ0, hμbar, hsim'⟩ := hsim
  obtain ⟨hcM, hcM'⟩ := flagCuts_of_smul_hypFlag hε hI _ hμ0 hsim' hflag
  have hNF' : UniNormFix h hε hI (semilinearAutHom h hr hε γ) := by rw [hγ]; exact hNF
  have hσo : (γ : SemiGL (HypIndex (t + s) ε) K).right ^ (orderOf α) = 1 := by
    have h1 : semilinearAutHom h hr hε (γ ^ orderOf α) = 1 := by
      rw [map_pow, hγ, pow_orderOf_eq_one]
    have h2 := ((semilinearAutHom_eq_one_iff h hr hε hn3 (γ ^ orderOf α)).mp h1).1
    have h3 : ((γ ^ orderOf α : semilinearSimilitudes h (t + s) ε) :
        SemiGL (HypIndex (t + s) ε) K).right =
        (γ : SemiGL (HypIndex (t + s) ε) K).right ^ orderOf α := by
      change SemidirectProduct.rightHom ((γ ^ orderOf α : semilinearSimilitudes h (t + s) ε) :
        SemiGL (HypIndex (t + s) ε) K) = _
      rw [Subgroup.coe_pow, map_pow]
      rfl
    rw [h3] at h2
    exact h2
  have hres_rel : 2 ≤ 2 * s + ε → ∀ B : hypSU h s ε, ∃ c : K,
      blkRes t ((γ : SemiGL (HypIndex (t + s) ε) K).left : Matrix (HypIndex (t + s) ε)
        (HypIndex (t + s) ε) K) *
        ((B : GL (HypIndex s ε) K) : Matrix (HypIndex s ε) (HypIndex s ε) K).map
          (γ : SemiGL (HypIndex (t + s) ε) K).right =
      c • (((B : GL (HypIndex s ε) K) : Matrix (HypIndex s ε) (HypIndex s ε) K) *
        blkRes t ((γ : SemiGL (HypIndex (t + s) ε) K).left : Matrix (HypIndex (t + s) ε)
          (HypIndex (t + s) ε) K)) := fun hres B =>
    resBlock_relation h hr hε hI γ hNF' hcM hcM' hres B
  have hresMM' : 2 ≤ 2 * s + ε →
      blkRes t (((γ : SemiGL (HypIndex (t + s) ε) K).left⁻¹ : GL (HypIndex (t + s) ε) K) :
        Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K) *
      blkRes t ((γ : SemiGL (HypIndex (t + s) ε) K).left : Matrix (HypIndex (t + s) ε)
        (HypIndex (t + s) ε) K) = 1 := fun _ => by
    have := submatrix_mul_of_cutPat (resIdx_injective (s := s) (ε := ε) t) (mem_range_resIdx t)
      (hcM'.1 t hI.mem) hcM.2
    rw [blkRes, blkRes, ← this, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.submatrix_one _ (resIdx_injective t)]
  have hσ1 : ∀ x : K, (γ : SemiGL (HypIndex (t + s) ε) K).right x = x := by
    rcases j with _ | b
    · have hres : 2 ≤ 2 * s + ε := hj
      have hs : 1 ≤ s := by omega
      have hfix := sigma_fixes_traceZero hs (hresMM' hres) _ (hres_rel hres)
      have := eq_one_of_fixes_traceZero h _ hodd hσo hfix
      exact fun x => by rw [this]; rfl
    · exact (eBlock_scalar hr hε hI γ hNF' hcM hcM' b hj).1
  refine ⟨γ, hγ, RingEquiv.ext hσ1, ⟨μ, hμ0, hμbar, hsim'⟩, hflag, fun b => ?_, ?_⟩
  · by_cases hb2 : 2 ≤ b.1 - predCut I b.1
    · exact (eBlock_scalar hr hε hI γ hNF' hcM hcM' b hb2).2
    · haveI : Subsingleton (Fin (b.1 - predCut I b.1)) :=
        Fin.subsingleton_iff_le_one.mpr (by omega)
      exact exists_smul_one_of_subsingleton _
  · by_cases hres : 2 ≤ 2 * s + ε
    · have hs : 1 ≤ s := by omega
      exact eq_smul_one_of_res_rel hs (hresMM' hres) _ hσ1 (hres_rel hres)
    · haveI := subsingleton_hypIndex (s := s) (ε := ε) (by omega)
      exact exists_smul_one_of_subsingleton _

end Block

section Comm

variable {f : ℕ} {K : Type} [Field K] {t s ε : ℕ} {h : UnitaryFieldData 2 f K} {I : Finset ℕ}

theorem submatrix_commutator_eq_one {ι : Type} [Fintype ι] [DecidableEq ι] {r : ℕ}
    {φ : ι → HypIndex r ε} (hφ : Function.Injective φ) {a b : ℕ}
    (hrange : ∀ x, x ∈ Set.range φ ↔ a ≤ fullPos x ∧ fullPos x < b)
    {M₁ M₂ M₁' M₂' : Matrix (HypIndex r ε) (HypIndex r ε) K}
    (h₁a : CutPat a M₁) (h₁b : CutPat b M₁) (h₂a : CutPat a M₂) (h₂b : CutPat b M₂)
    (h₁'a : CutPat a M₁') (h₁'b : CutPat b M₁') (h₂'a : CutPat a M₂') (h₂'b : CutPat b M₂')
    (e₁ : M₁ * M₁' = 1) (e₂ : M₂ * M₂' = 1)
    (hs₁ : ∃ c : K, M₁.submatrix φ φ = c • 1) (hs₂ : ∃ c : K, M₂.submatrix φ φ = c • 1) :
    (M₁ * M₂ * M₁' * M₂').submatrix φ φ = 1 := by
  have mb : ∀ {A B : Matrix (HypIndex r ε) (HypIndex r ε) K}, CutPat a A → CutPat b B →
      (A * B).submatrix φ φ = A.submatrix φ φ * B.submatrix φ φ :=
    fun hA hB => submatrix_mul_of_cutPat hφ hrange hA hB
  rw [mb ((h₁a.mul h₂a).mul h₁'a) h₂'b, mb (h₁a.mul h₂a) h₁'b, mb h₁a h₂b]
  have i₁ : M₁.submatrix φ φ * M₁'.submatrix φ φ = 1 := by
    rw [← mb h₁a h₁'b, e₁, Matrix.submatrix_one _ hφ]
  have i₂ : M₂.submatrix φ φ * M₂'.submatrix φ φ = 1 := by
    rw [← mb h₂a h₂'b, e₂, Matrix.submatrix_one _ hφ]
  obtain ⟨c₁, hc₁⟩ := hs₁
  obtain ⟨c₂, hc₂⟩ := hs₂
  have hcomm : M₁.submatrix φ φ * M₂.submatrix φ φ = M₂.submatrix φ φ * M₁.submatrix φ φ := by
    rw [hc₁, hc₂]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_one, mul_comm]
  calc M₁.submatrix φ φ * M₂.submatrix φ φ * M₁'.submatrix φ φ * M₂'.submatrix φ φ
      = M₂.submatrix φ φ * M₁.submatrix φ φ * M₁'.submatrix φ φ * M₂'.submatrix φ φ := by
        rw [hcomm]
    _ = M₂.submatrix φ φ * (M₁.submatrix φ φ * M₁'.submatrix φ φ) * M₂'.submatrix φ φ := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [i₁, Matrix.mul_one, i₂]

theorem sim_mul {r : ℕ} {A B : Matrix (HypIndex r ε) (HypIndex r ε) K} {a b : K}
    (hA : (A.map h.bar)ᵀ * hypGram r ε K * A = a • hypGram r ε K)
    (hB : (B.map h.bar)ᵀ * hypGram r ε K * B = b • hypGram r ε K) :
    ((A * B).map h.bar)ᵀ * hypGram r ε K * (A * B) = (a * b) • hypGram r ε K := by
  rw [conjTranspose_mul_mul h, hA, Matrix.mul_smul, Matrix.smul_mul, hB, smul_smul, mul_comm]

theorem exists_pow_two_eq_one_commutator (hε : ε ≤ 1) (hI : IsTopCut I t)
    {M₁ M₂ : GL (HypIndex (t + s) ε) K} {μ₁ μ₂ : K} (hμ₁ : μ₁ ≠ 0) (hμ₂ : μ₂ ≠ 0)
    (hs₁ : ((M₁ : Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K).map h.bar)ᵀ *
      hypGram (t + s) ε K * M₁ = μ₁ • hypGram (t + s) ε K)
    (hs₂ : ((M₂ : Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K).map h.bar)ᵀ *
      hypGram (t + s) ε K * M₂ = μ₂ • hypGram (t + s) ε K)
    (hf₁ : ∀ c ∈ I, M₁ • hypFlag h (t + s) ε c = hypFlag h (t + s) ε c)
    (hf₂ : ∀ c ∈ I, M₂ • hypFlag h (t + s) ε c = hypFlag h (t + s) ε c)
    (hb₁ : ∀ b : ↥I, ∃ c : K, blkE hI b (M₁ : Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K) =
      c • 1)
    (hr₁ : ∃ c : K, blkRes t (M₁ : Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K) = c • 1)
    (hb₂ : ∀ b : ↥I, ∃ c : K, blkE hI b (M₂ : Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K) =
      c • 1)
    (hr₂ : ∃ c : K, blkRes t (M₂ : Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K) = c • 1) :
    ∃ k : ℕ, (⁅M₁, M₂⁆ : GL (HypIndex (t + s) ε) K) ^ 2 ^ k = 1 := by
  obtain ⟨hc₁, hc₁'⟩ := flagCuts_of_smul_hypFlag hε hI M₁ hμ₁ hs₁ hf₁
  obtain ⟨hc₂, hc₂'⟩ := flagCuts_of_smul_hypFlag hε hI M₂ hμ₂ hs₂ hf₂
  set C : GL (HypIndex (t + s) ε) K := ⁅M₁, M₂⁆ with hC
  have hCmat : (C : Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K) =
      (M₁ : Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K) *
        (M₂ : Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K) *
        ((M₁⁻¹ : GL (HypIndex (t + s) ε) K) : Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K) *
        ((M₂⁻¹ : GL (HypIndex (t + s) ε) K) :
          Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K) := by
    rw [hC, commutatorElement_def]
    simp only [Units.val_mul]
  have e₁ : (M₁ : Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K) *
      ((M₁⁻¹ : GL (HypIndex (t + s) ε) K) :
        Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e₂ : (M₂ : Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K) *
      ((M₂⁻¹ : GL (HypIndex (t + s) ε) K) :
        Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hs₁' := inv_similitude h hμ₁ hs₁ e₁
  have hs₂' := inv_similitude h hμ₂ hs₂ e₂
  have hCsim : ((C : Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K).map h.bar)ᵀ *
      hypGram (t + s) ε K * C = hypGram (t + s) ε K := by
    rw [hCmat, sim_mul (sim_mul (sim_mul hs₁ hs₂) hs₁') hs₂']
    have : μ₁ * μ₂ * μ₁⁻¹ * μ₂⁻¹ = 1 := by field_simp
    rw [this, one_smul]
  have hCdet : (C : Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hC, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _), Units.val_one]
  have hCS : C ∈ hypSU h (t + s) ε := mem_hypSU.mpr ⟨hCsim, hCdet⟩
  have hinv : ∀ (M : GL (HypIndex (t + s) ε) K) (c : ℕ),
      M • hypFlag h (t + s) ε c = hypFlag h (t + s) ε c →
      M⁻¹ • hypFlag h (t + s) ε c = hypFlag h (t + s) ε c := fun M c hM => by
    have h1 : M⁻¹ • (M • hypFlag h (t + s) ε c) = hypFlag h (t + s) ε c :=
      inv_smul_smul M (hypFlag h (t + s) ε c)
    have h2 := congrArg (fun W => M⁻¹ • W) hM
    exact h2.symm.trans h1
  have hCfl : ∀ c ∈ I, C • hypFlag h (t + s) ε c = hypFlag h (t + s) ε c := fun c hc => by
    rw [hC, commutatorElement_def, gl_mul_smul, gl_mul_smul, gl_mul_smul, hinv _ _ (hf₂ c hc),
      hinv _ _ (hf₁ c hc), hf₂ c hc, hf₁ c hc]
  let x : ↥(flagStabilizer h (t + s) ε ↑I) :=
    ⟨⟨C, hCS⟩, mem_flagStabilizer.mpr fun c hc => hCfl c hc⟩
  have hker : x ∈ (uniLeviHom (s := s) h hε hI).ker := by
    rw [MonoidHom.mem_ker]
    funext j
    rcases j with _ | b
    · show resBlockHom h hε (Finset.mem_coe.mpr hI.mem) x = 1
      refine Units.ext ?_
      rw [coe_resBlockHom, Units.val_one]
      change (C : Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K).submatrix (resIdx t)
        (resIdx t) = 1
      rw [hCmat]
      exact submatrix_commutator_eq_one (resIdx_injective t) (mem_range_resIdx t)
        (hc₁.1 t hI.mem) hc₁.2 (hc₂.1 t hI.mem) hc₂.2 (hc₁'.1 t hI.mem) hc₁'.2
        (hc₂'.1 t hI.mem) hc₂'.2 e₁ e₂ hr₁ hr₂
    · have hbr : b.1 ≤ t + s := (hI.le b.1 b.2).2.trans (Nat.le_add_right t s)
      have hb1 : 1 ≤ b.1 := (hI.le b.1 b.2).1
      show eBlockHom h hε b.2 hb1 hbr x = 1
      refine Units.ext ?_
      rw [coe_eBlockHom, Units.val_one]
      change (C : Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K).submatrix
        (eIdx (t + s) ε hbr) (eIdx (t + s) ε hbr) = 1
      rw [hCmat]
      exact submatrix_commutator_eq_one (eIdx_injective hbr) (mem_range_eIdx hbr)
        (hc₁.cut_predCut b.1) (hc₁.1 b.1 b.2) (hc₂.cut_predCut b.1) (hc₂.1 b.1 b.2)
        (hc₁'.cut_predCut b.1) (hc₁'.1 b.1 b.2) (hc₂'.cut_predCut b.1) (hc₂'.1 b.1 b.2)
        e₁ e₂ (hb₁ b) (hb₂ b)
  obtain ⟨k, hk⟩ := isPGroup_ker_uniLeviHom (s := s) h hε hI ⟨x, hker⟩
  refine ⟨k, ?_⟩
  have h1 : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h2 := congrArg (fun y : ↥(flagStabilizer h (t + s) ε ↑I) =>
    ((y : hypSU h (t + s) ε) : GL (HypIndex (t + s) ε) K)) h1
  have hxC : ((x : hypSU h (t + s) ε) : GL (HypIndex (t + s) ε) K) = C := rfl
  simpa [hxC] using h2

end Comm

theorem uniModelComm_holds :
    ∀ (K : Type) [Field K] (f : ℕ) (h : UnitaryFieldData 2 f K) (t s ε : ℕ) (hε : ε ≤ 1)
      (I : Finset ℕ) (hI : IsTopCut I t), (∃ j, IsBigBlock s ε I j) →
      ∀ α₁ α₂ : MulAut (hypPSU h (t + s) ε), Odd (orderOf α₁) → Odd (orderOf α₂) →
        Odd (orderOf ⁅α₁, α₂⁆) → UniNormFix h hε hI α₁ → UniNormFix h hε hI α₂ → ⁅α₁, α₂⁆ = 1 := by
  intro K _ f h t s ε hε I hI hbig α₁ α₂ ho₁ ho₂ hoc hN₁ hN₂
  have hr : 1 ≤ t + s := (hI.le t hI.mem).1.trans (Nat.le_add_right t s)
  obtain ⟨γ₁, hγ₁, hσ₁, ⟨μ₁, hμ₁0, -, hs₁⟩, hf₁, hb₁, hr₁⟩ :=
    exists_block_scalar hr hε hI hbig ho₁ hN₁
  obtain ⟨γ₂, hγ₂, hσ₂, ⟨μ₂, hμ₂0, -, hs₂⟩, hf₂, hb₂, hr₂⟩ :=
    exists_block_scalar hr hε hI hbig ho₂ hN₂
  obtain ⟨k, hk⟩ := exists_pow_two_eq_one_commutator hε hI hμ₁0 hμ₂0 hs₁ hs₂ hf₁ hf₂ hb₁ hr₁
    hb₂ hr₂
  have hcomm : ⁅α₁, α₂⁆ = semilinearAutHom h hr hε ⁅γ₁, γ₂⁆ := by
    rw [map_commutatorElement, hγ₁, hγ₂]
  have hinl : ∀ γ : semilinearSimilitudes h (t + s) ε,
      (γ : SemiGL (HypIndex (t + s) ε) K).right = 1 →
      (γ : SemiGL (HypIndex (t + s) ε) K) =
        SemidirectProduct.inl (γ : SemiGL (HypIndex (t + s) ε) K).left :=
    fun γ hγ => SemidirectProduct.ext rfl hγ
  have hpow : (⁅γ₁, γ₂⁆ : semilinearSimilitudes h (t + s) ε) ^ 2 ^ k = 1 := by
    apply Subtype.ext
    have h1 : ((⁅γ₁, γ₂⁆ ^ 2 ^ k : semilinearSimilitudes h (t + s) ε) :
        SemiGL (HypIndex (t + s) ε) K) =
        ⁅(γ₁ : SemiGL (HypIndex (t + s) ε) K), (γ₂ : SemiGL (HypIndex (t + s) ε) K)⁆ ^ 2 ^ k := by
      simp only [commutatorElement_def, Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [h1, hinl γ₁ hσ₁, hinl γ₂ hσ₂, ← map_commutatorElement, ← map_pow, hk, map_one]
    rfl
  have h1 : ⁅α₁, α₂⁆ ^ 2 ^ k = 1 := by rw [hcomm, ← map_pow, hpow, map_one]
  have hdvd : orderOf ⁅α₁, α₂⁆ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hj0 : j = 0 := by
    by_contra hne
    rw [hj] at hoc
    exact (Nat.not_even_iff_odd.mpr hoc) (Nat.even_pow.mpr ⟨even_two, hne⟩)
  rw [hj0, pow_zero] at hj
  exact orderOf_eq_one_iff.mp hj

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Uni
