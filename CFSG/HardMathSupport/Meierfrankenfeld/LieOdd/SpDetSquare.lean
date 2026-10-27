module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.SpOuter

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

variable {K : Type} [Field K] {r : ℕ}

theorem det_fromBlocks_J (m : ℕ) :
    (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) K) (1 : Matrix (Fin m) (Fin m) K)
      (-1 : Matrix (Fin m) (Fin m) K) (0 : Matrix (Fin m) (Fin m) K)).det = 1 := by
  have h : Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) K) (1 : Matrix (Fin m) (Fin m) K)
      (-1 : Matrix (Fin m) (Fin m) K) (0 : Matrix (Fin m) (Fin m) K) =
      Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) K) 1 0 1 *
        Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) K) (0 : Matrix (Fin m) (Fin m) K)
          (-1 : Matrix (Fin m) (Fin m) K) (1 : Matrix (Fin m) (Fin m) K) *
        Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) K) 1 0 1 := by
    simp [Matrix.fromBlocks_multiply]
  rw [h, Matrix.det_mul, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_fromBlocks_zero₁₂]
  simp

theorem isSquare_det_of_alt {m : ℕ} (G : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)
    (hG : ∀ v, v ⬝ᵥ (G *ᵥ v) = 0) (hdet : G.det ≠ 0) : IsSquare G.det := by
  classical
  let B : LinearMap.BilinForm K (Fin m ⊕ Fin m → K) := Matrix.toBilin' G
  have hB : B.IsAlt := fun v => by simpa [B, Matrix.toBilin'_apply'] using hG v
  have hnd : B.Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.2 hdet
  obtain ⟨m', b, hfin, hb⟩ :=
    CFSG.ComponentClassification.CatalogueBAlternatingIsometry.exists_symplectic_basis B hB hnd
  have hm : m' = m := by
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin] at hfin
    omega
  subst hm
  have h := LinearMap.BilinForm.toMatrix_mul_basis_toMatrix (Pi.basisFun K (Fin m' ⊕ Fin m')) b B
  rw [hb, LinearMap.BilinForm.toMatrix_basisFun] at h
  have hG' : LinearMap.BilinForm.toMatrix' B = G := by
    simp [B]
  rw [hG'] at h
  have hd := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hd
  have hJ : (Matrix.J (Fin m') K).det = 1 := by
    rw [Matrix.J, ← Matrix.det_transpose, Matrix.fromBlocks_transpose]
    simpa using det_fromBlocks_J (K := K) m'
  rw [hJ] at hd
  have hP : ((Pi.basisFun K (Fin m' ⊕ Fin m')).toMatrix b).det ≠ 0 := by
    intro h0
    rw [h0] at hd
    simp at hd
  refine ⟨((Pi.basisFun K (Fin m' ⊕ Fin m')).toMatrix b).det⁻¹, ?_⟩
  field_simp
  linear_combination hd

theorem det_statedSp_eq_one [NeZero r] (hsimple : IsSimpleGroup (StatedProj (StatedSp r K)))
    (hcent : Subgroup.center (StatedProj (StatedSp r K)) = ⊥) (g : StatedSp r K) :
    ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).det = 1 := by
  have hperf : commutator (StatedProj (StatedSp r K)) = ⊤ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (commutator (StatedProj (StatedSp r K))) with h | h
    · exfalso
      have hcomm : ∀ x y : StatedProj (StatedSp r K), x * y = y * x := fun x y => by
        have h1 := Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
        rw [← commutator_def, h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
        exact h1
      have : Subgroup.center (StatedProj (StatedSp r K)) = ⊤ :=
        top_unique fun x _ => Subgroup.mem_center_iff.2 fun y => hcomm y x
      rw [hcent] at this
      obtain ⟨x, hx⟩ := exists_ne (1 : StatedProj (StatedSp r K))
      exact hx ((Subgroup.mem_bot).1 (this ▸ Subgroup.mem_top x))
    · exact h
  let δ : StatedSp r K →* Kˣ :=
    (Matrix.GeneralLinearGroup.det).comp (StatedSp r K).subtype
  have hker : commutator (StatedSp r K) ≤ δ.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_inv, map_inv]
    simp
  have hmap : (commutator (StatedSp r K)).map (proj r K) = ⊤ := by
    have htop : (⊤ : Subgroup (StatedSp r K)).map (proj r K) = ⊤ := by
      rw [← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 (proj_surjective (r := r) (K := K))]
    rw [commutator_def, Subgroup.map_commutator, htop, ← commutator_def]
    exact hperf
  obtain ⟨c, hc, hcg⟩ : ∃ c ∈ commutator (StatedSp r K), proj r K c = proj r K g := by
    have : proj r K g ∈ (commutator (StatedSp r K)).map (proj r K) := hmap ▸ Subgroup.mem_top _
    obtain ⟨c, hc, hcg⟩ := this
    exact ⟨c, hc, hcg⟩
  have h3 := QuotientGroup.eq.1 hcg
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at h3
  obtain ⟨d, hd⟩ := h3
  have hdsp : Matrix.GeneralLinearGroup.scalar (Fin r ⊕ Fin r) d ∈ StatedSp r K := by
    rw [hd]
    exact (c⁻¹ * g).2
  have hd2 : d * d = 1 := scalar_sq_eq_one_of_mem_statedSp d hdsp
  have hδd : δ (c⁻¹ * g) = 1 := by
    apply Units.ext
    change ((((c⁻¹ * g : StatedSp r K)) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).det = 1
    rw [← hd]
    have hs : ((Matrix.GeneralLinearGroup.scalar (Fin r ⊕ Fin r) d : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = (d : K) • 1 := by
      ext i j
      by_cases hij : i = j <;>
        simp [Matrix.GeneralLinearGroup.scalar, Matrix.diagonal_apply, Matrix.one_apply, hij]
    rw [hs, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_sum, Fintype.card_fin,
      ← two_mul, pow_mul]
    have : (d : K) ^ 2 = 1 := by
      have := congrArg Units.val hd2
      simpa [sq] using this
    rw [this, one_pow]
  have hδc : δ c = 1 := hker hc
  have : δ g = 1 := by
    have h4 : g = c * (c⁻¹ * g) := by group
    rw [h4, map_mul, hδc, hδd, one_mul]
  exact congrArg Units.val this

theorem det_gsp [NeZero r] (hsimple : IsSimpleGroup (StatedProj (StatedSp r K)))
    (hcent : Subgroup.center (StatedProj (StatedSp r K)) = ⊥) (A : gsp r K) :
    ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).det =
      ((multiplier r K A : Kˣ) : K) ^ r := by
  set μ : Kˣ := multiplier r K A with hμ
  set a : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
    ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with ha
  have hA : aᵀ * formJ r K * a = (μ : K) • formJ r K := multiplier_spec A
  let Dm : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
    Matrix.fromBlocks 1 0 0 (((μ⁻¹ : Kˣ) : K) • 1)
  let Dm' : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
    Matrix.fromBlocks 1 0 0 ((μ : K) • 1)
  have h1 : Dm * Dm' = 1 := by
    simp only [Dm, Dm', Matrix.fromBlocks_multiply]
    rw [← Matrix.fromBlocks_one]
    congr 1 <;> simp [smul_smul]
  have h2 : Dm' * Dm = 1 := by
    simp only [Dm, Dm', Matrix.fromBlocks_multiply]
    rw [← Matrix.fromBlocks_one]
    congr 1 <;> simp [smul_smul]
  let D : GL (Fin r ⊕ Fin r) K := ⟨Dm, Dm', h1, h2⟩
  have hDJ : Dmᵀ * formJ r K * Dm = (((μ⁻¹ : Kˣ) : K)) • formJ r K := by
    simp only [Dm, formJ, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
      Matrix.transpose_zero, Matrix.transpose_one, Matrix.transpose_smul]
    rw [Matrix.fromBlocks_smul]
    congr 1 <;> simp
  have hAD : (A : GL (Fin r ⊕ Fin r) K) * D ∈ StatedSp r K := by
    rw [CFSG.LargeExtraspecial.A2Mod.FrC.mem_statedSp_iff, Units.val_mul]
    change (a * Dm)ᵀ * formJ r K * (a * Dm) = formJ r K
    have hDt : Dmᵀ = Dm := by
      simp only [Dm, Matrix.fromBlocks_transpose, Matrix.transpose_zero, Matrix.transpose_one,
        Matrix.transpose_smul]
    calc (a * Dm)ᵀ * formJ r K * (a * Dm)
        = Dmᵀ * (aᵀ * formJ r K * a) * Dm := by
          rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = (μ : K) • (Dmᵀ * formJ r K * Dm) := by
          rw [hA, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = formJ r K := by
          rw [hDJ, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]
  have hdet := det_statedSp_eq_one hsimple hcent ⟨_, hAD⟩
  change ((A : GL (Fin r ⊕ Fin r) K) * D : GL (Fin r ⊕ Fin r) K).val.det = 1 at hdet
  rw [Units.val_mul, Matrix.det_mul] at hdet
  have hdD : Dm.det = (((μ⁻¹ : Kˣ) : K)) ^ r := by
    simp only [Dm]
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, Matrix.det_smul, Matrix.det_one,
      Fintype.card_fin, one_mul, mul_one]
  have hD : (D : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = Dm := rfl
  rw [hD, hdD] at hdet
  have hμ0 : (μ : K) ≠ 0 := Units.ne_zero μ
  have : (((μ⁻¹ : Kˣ) : K)) = (μ : K)⁻¹ := by simp
  rw [this, inv_pow] at hdet
  field_simp at hdet
  exact hdet

theorem no_similitude_sq_eq_mul_of_odd [NeZero r] (h2 : (2 : K) ≠ 0) (hr : Odd r)
    (hsimple : IsSimpleGroup (StatedProj (StatedSp r K)))
    (hcent : Subgroup.center (StatedProj (StatedSp r K)) = ⊥) (A : gsp r K)
    (hA2 : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
        ((multiplier r K A : Kˣ) : K) • 1)
    (hnsq : ¬ IsSquare ((multiplier r K A : Kˣ) : K)) : False := by
  set μ : K := ((multiplier r K A : Kˣ) : K) with hμdef
  set a : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
    ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with ha
  have hA : aᵀ * formJ r K * a = μ • formJ r K := multiplier_spec A
  have hμ0 : μ ≠ 0 := Units.ne_zero _
  have haa : ∀ x, a *ᵥ (a *ᵥ x) = μ • x := by
    intro x
    rw [Matrix.mulVec_mulVec, hA2, Matrix.smul_mulVec, Matrix.one_mulVec]
  have sa : ∀ x y, symB (a *ᵥ x) y = symB x (a *ᵥ y) := by
    intro x y
    have h := symB_similitude hA (a *ᵥ x) y
    rw [haa, symB_smul_left] at h
    exact mul_left_cancel₀ hμ0 h.symm
  have hdetA : a.det = μ ^ r := det_gsp hsimple hcent A
  have hG : ∀ v, v ⬝ᵥ ((formJ r K * a) *ᵥ v) = 0 := by
    intro v
    have h1 : v ⬝ᵥ ((formJ r K * a) *ᵥ v) = symB v (a *ᵥ v) := by
      simp only [symB, Matrix.mulVec_mulVec]
    rw [h1]
    have h3 := sa v v
    have h4 := symB_swap v (a *ᵥ v)
    have h5 : (2 : K) * symB v (a *ᵥ v) = 0 := by linear_combination h4 - h3
    exact (mul_eq_zero.1 h5).resolve_left h2
  have hdetG : (formJ r K * a).det = μ ^ r := by
    rw [Matrix.det_mul, hdetA]
    have : (formJ r K).det = 1 := by
      rw [formJ]
      exact det_fromBlocks_J r
    rw [this, one_mul]
  have hsq := isSquare_det_of_alt (formJ r K * a) hG (by rw [hdetG]; exact pow_ne_zero _ hμ0)
  rw [hdetG] at hsq
  obtain ⟨k, hk⟩ := hr
  obtain ⟨s, hs⟩ := hsq
  apply hnsq
  refine ⟨s / μ ^ k, ?_⟩
  have hμk : μ ^ k ≠ 0 := pow_ne_zero _ hμ0
  field_simp
  rw [hk, pow_succ, pow_mul] at hs
  linear_combination hs

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
