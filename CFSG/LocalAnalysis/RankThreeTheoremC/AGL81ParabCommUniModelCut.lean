module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearAut
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommUniDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Uni

open Matrix Module CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.AGLEmbedding.LeviBlock
open scoped Pointwise

section CutPat

variable {K : Type} [Field K] {r ε : ℕ}

@[expose] def CutPat (c : ℕ) (N : Matrix (HypIndex r ε) (HypIndex r ε) K) : Prop :=
  ∀ u w : HypIndex r ε, fullPos w < c → c ≤ fullPos u → N u w = 0

theorem CutPat.one (c : ℕ) : CutPat c (1 : Matrix (HypIndex r ε) (HypIndex r ε) K) := by
  intro u w hw hu
  rw [Matrix.one_apply_ne]
  rintro rfl
  omega

theorem CutPat.mul {c : ℕ} {M N : Matrix (HypIndex r ε) (HypIndex r ε) K} (hM : CutPat c M)
    (hN : CutPat c N) : CutPat c (M * N) := by
  intro u w hw hu
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun v _ => ?_
  by_cases hv : fullPos v < c
  · rw [hM u v hv hu, zero_mul]
  · rw [hN v w hw (not_lt.mp hv), mul_zero]

theorem CutPat.map {c : ℕ} {N : Matrix (HypIndex r ε) (HypIndex r ε) K} (hN : CutPat c N)
    (σ : K →+* K) : CutPat c (N.map σ) := by
  intro u w hw hu
  rw [Matrix.map_apply, hN u w hw hu, map_zero]

theorem cutPat_zero (N : Matrix (HypIndex r ε) (HypIndex r ε) K) : CutPat 0 N :=
  fun _ _ hw => absurd hw (Nat.not_lt_zero _)

theorem cutPat_of_mulVec_mem {c : ℕ} {N : Matrix (HypIndex r ε) (HypIndex r ε) K}
    (hN : ∀ v ∈ posFlag r ε K c, N *ᵥ v ∈ posFlag r ε K c) : CutPat c N :=
  fun _ _ hw hu => apply_eq_zero_of_mulVec_mem_posFlag hN hw hu

theorem submatrix_mul_of_cutPat {ι : Type} [Fintype ι] [DecidableEq ι]
    {φ : ι → HypIndex r ε} (hφ : Function.Injective φ) {a b : ℕ}
    (hrange : ∀ x, x ∈ Set.range φ ↔ a ≤ fullPos x ∧ fullPos x < b)
    {M N : Matrix (HypIndex r ε) (HypIndex r ε) K} (hMa : CutPat a M) (hNb : CutPat b N) :
    (M * N).submatrix φ φ = M.submatrix φ φ * N.submatrix φ φ :=
  submatrix_mul_of_cuts hφ hrange hMa hNb

theorem block_rel_aux {ι : Type} [Fintype ι] [DecidableEq ι] {φ : ι → HypIndex r ε}
    (hφ : Function.Injective φ) {a b : ℕ}
    (hrange : ∀ x, x ∈ Set.range φ ↔ a ≤ fullPos x ∧ fullPos x < b)
    {M M' X U : Matrix (HypIndex r ε) (HypIndex r ε) K} (σ : K ≃+* K) (c : K)
    (hMa : CutPat a M) (hMb : CutPat b M) (hM'a : CutPat a M') (hM'b : CutPat b M')
    (hXa : CutPat a X) (hXb : CutPat b X) (hUa : CutPat a U)
    (hMM' : M' * M = 1) (hU1 : U.submatrix φ φ = 1)
    (hrel : M * X.map σ * M' = c • (U * X)) :
    M.submatrix φ φ * (X.submatrix φ φ).map σ = c • (X.submatrix φ φ * M.submatrix φ φ) := by
  have hXaσ : CutPat a (X.map σ) := hXa.map σ.toRingHom
  have hXbσ : CutPat b (X.map σ) := hXb.map σ.toRingHom
  have e1 : (M * X.map σ * M').submatrix φ φ =
      M.submatrix φ φ * (X.submatrix φ φ).map σ * M'.submatrix φ φ := by
    rw [submatrix_mul_of_cutPat hφ hrange (hMa.mul hXaσ) hM'b,
      submatrix_mul_of_cutPat hφ hrange hMa hXbσ]
    rfl
  have e2 : (c • (U * X)).submatrix φ φ = c • X.submatrix φ φ := by
    have : (c • (U * X)).submatrix φ φ = c • (U * X).submatrix φ φ := rfl
    rw [this, submatrix_mul_of_cutPat hφ hrange hUa hXb, hU1, one_mul]
  have e3 : M'.submatrix φ φ * M.submatrix φ φ = 1 := by
    have := submatrix_mul_of_cutPat hφ hrange hM'a hMb
    rw [hMM', Matrix.submatrix_one _ hφ] at this
    exact this.symm
  have e4 := congrArg (fun N : Matrix (HypIndex r ε) (HypIndex r ε) K => N.submatrix φ φ) hrel
  rw [e1, e2] at e4
  calc M.submatrix φ φ * (X.submatrix φ φ).map σ
      = M.submatrix φ φ * (X.submatrix φ φ).map σ * (M'.submatrix φ φ * M.submatrix φ φ) := by
        rw [e3, mul_one]
    _ = (M.submatrix φ φ * (X.submatrix φ φ).map σ * M'.submatrix φ φ) * M.submatrix φ φ := by
        simp only [Matrix.mul_assoc]
    _ = c • (X.submatrix φ φ * M.submatrix φ φ) := by rw [e4, smul_mul_assoc]

@[expose] def FlagCuts (I : Finset ℕ) (t : ℕ) (N : Matrix (HypIndex r ε) (HypIndex r ε) K) :
    Prop :=
  (∀ c ∈ I, CutPat c N) ∧ CutPat (2 * r + ε - t) N

theorem FlagCuts.cut_predCut {I : Finset ℕ} {t : ℕ} {N : Matrix (HypIndex r ε) (HypIndex r ε) K}
    (hN : FlagCuts I t N) (b : ℕ) : CutPat (predCut I b) N := by
  rcases predCut_eq_zero_or_mem I b with h0 | hmem
  · rw [h0]
    exact cutPat_zero N
  · exact hN.1 _ hmem

end CutPat

section Stab

variable {p f : ℕ} {K : Type} [Field K] {t s ε : ℕ} {h : UnitaryFieldData p f K}

theorem flagCuts_of_mem_flagStabilizer (hε : ε ≤ 1) {I : Finset ℕ} (hI : IsTopCut I t)
    {g : hypSU h (t + s) ε} (hg : g ∈ flagStabilizer h (t + s) ε ↑I) :
    FlagCuts I t (((g : GL (HypIndex (t + s) ε) K) : Matrix (HypIndex (t + s) ε)
      (HypIndex (t + s) ε) K)) :=
  ⟨fun c hc u w hw hu => isHypCut_flagStabilizer h hε (Finset.mem_coe.mpr hc)
      ((hI.le c hc).2.trans (Nat.le_add_right t s)) g hg u w hw hu,
    fun u w hw hu => isHypCut_flagStabilizer_orth h hε (Finset.mem_coe.mpr hI.mem)
      (Nat.le_add_right t s) g hg u w hw hu⟩

theorem cutPat_orth_of_smul (hε : ε ≤ 1) {r : ℕ} {t : ℕ} (ht : t ≤ r)
    (N : GL (HypIndex r ε) K) {ν : K}
    (hν : ((N : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar)ᵀ * hypGram r ε K * N =
      ν • hypGram r ε K)
    (hN : N • posFlag r ε K t = posFlag r ε K t) :
    CutPat (2 * r + ε - t) (N : Matrix (HypIndex r ε) (HypIndex r ε) K) := by
  refine cutPat_of_mulVec_mem fun x hx => ?_
  rw [← orthogonal_isoFlag h hε ht, isoFlag_eq_posFlag ht, Submodule.mem_orthogonalBilin_iff]
    at hx ⊢
  intro y hy
  have hy' : y ∈ N • posFlag r ε K t := by
    rw [hN]
    exact hy
  obtain ⟨y₀, hy₀, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists y N _).mp hy'
  change gramForm h (hypGram r ε K) ((N : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ y₀)
    ((N : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ x) = 0
  rw [gramForm_mulVec, hν, gramForm_smul_gram]
  have := hx y₀ hy₀
  change gramForm h (hypGram r ε K) y₀ x = 0 at this
  rw [this, mul_zero]

theorem cutPat_of_smul_posFlag {r : ℕ} {c : ℕ} (N : GL (HypIndex r ε) K)
    (hN : N • posFlag r ε K c = posFlag r ε K c) :
    CutPat c (N : Matrix (HypIndex r ε) (HypIndex r ε) K) := by
  refine cutPat_of_mulVec_mem fun v hv => ?_
  have h1 : N • v ∈ N • posFlag r ε K c := Submodule.smul_mem_pointwise_smul v N _ hv
  rw [hN] at h1
  exact h1

theorem flagCuts_of_smul_hypFlag (hε : ε ≤ 1) {I : Finset ℕ} (hI : IsTopCut I t)
    (M : GL (HypIndex (t + s) ε) K) {μ : K} (hμ0 : μ ≠ 0)
    (hsim : ((M : Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K).map h.bar)ᵀ *
      hypGram (t + s) ε K * M = μ • hypGram (t + s) ε K)
    (hM : ∀ c ∈ I, M • hypFlag h (t + s) ε c = hypFlag h (t + s) ε c) :
    FlagCuts I t (M : Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K) ∧
      FlagCuts I t ((M⁻¹ : GL (HypIndex (t + s) ε) K) :
        Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K) := by
  have hcn : ∀ c ∈ I, c ≤ 2 * (t + s) + ε := fun c hc => by
    have := (hI.le c hc).2
    omega
  have hMF : ∀ c ∈ I, M • posFlag (t + s) ε K c = posFlag (t + s) ε K c := fun c hc => by
    have := hM c hc
    rwa [hypFlag_eq_posFlag h hε (hcn c hc)] at this
  have hMiF : ∀ c ∈ I, M⁻¹ • posFlag (t + s) ε K c = posFlag (t + s) ε K c := fun c hc => by
    have h1 : M⁻¹ • (M • posFlag (t + s) ε K c) = posFlag (t + s) ε K c :=
      inv_smul_smul M (posFlag (t + s) ε K c)
    have h2 := congrArg (fun W => M⁻¹ • W) (hMF c hc)
    exact h2.symm.trans h1
  have hAB : (M : Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K) *
      ((M⁻¹ : GL (HypIndex (t + s) ε) K) : Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K) =
      1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hsim' := inv_similitude h hμ0 hsim hAB
  exact ⟨⟨fun c hc => cutPat_of_smul_posFlag M (hMF c hc),
      cutPat_orth_of_smul hε (Nat.le_add_right t s) M hsim (hMF t hI.mem)⟩,
    ⟨fun c hc => cutPat_of_smul_posFlag M⁻¹ (hMiF c hc),
      cutPat_orth_of_smul hε (Nat.le_add_right t s) M⁻¹ hsim' (hMiF t hI.mem)⟩⟩

theorem coe_scalar_eq_smul_one {ι : Type} [Fintype ι] [DecidableEq ι] (c : Kˣ) :
    ((GeneralLinearGroup.scalar ι c : GL ι K) : Matrix ι ι K) = (c : K) • 1 := by
  rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

variable (h) in
theorem rel_of_normFix (hr : 1 ≤ t + s) (hε : ε ≤ 1) {I : Finset ℕ} (hI : IsTopCut I t)
    (γ : semilinearSimilitudes h (t + s) ε) (x : ↥(flagStabilizer h (t + s) ε ↑I))
    (hx : semilinearAutHom h hr hε γ (hypProj h (t + s) ε x) *
      (hypProj h (t + s) ε x)⁻¹ ∈ projUni h hε hI) :
    ∃ (u : ↥(flagStabilizer h (t + s) ε ↑I)) (c : K),
      u ∈ (uniLeviHom (s := s) h hε hI).ker ∧
      ((γ : SemiGL (HypIndex (t + s) ε) K).left : Matrix (HypIndex (t + s) ε)
          (HypIndex (t + s) ε) K) *
        (((x : hypSU h (t + s) ε) : GL (HypIndex (t + s) ε) K) :
          Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K).map
            (γ : SemiGL (HypIndex (t + s) ε) K).right *
        (((γ : SemiGL (HypIndex (t + s) ε) K).left⁻¹ : GL (HypIndex (t + s) ε) K) :
          Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K) =
      c • ((((u : hypSU h (t + s) ε) : GL (HypIndex (t + s) ε) K) :
          Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K) *
        (((x : hypSU h (t + s) ε) : GL (HypIndex (t + s) ε) K) :
          Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K)) := by
  rw [semilinearAutHom_apply h hr hε γ (x : hypSU h (t + s) ε)] at hx
  set g' : hypSU h (t + s) ε := ⟨_, conj_mem_hypSU γ.2 (x : hypSU h (t + s) ε)⟩ with hg'
  rw [← map_inv, ← map_mul] at hx
  obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp hx
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hy
  have hz : (u : hypSU h (t + s) ε)⁻¹ * (g' * (x : hypSU h (t + s) ε)⁻¹) ∈
      hypScalars h (t + s) ε := by
    rw [← ker_hypProj, MonoidHom.mem_ker, map_mul, map_inv, ← hyeq]
    simp
  obtain ⟨c, -, -, hcz⟩ := mem_normOneScalars.mp hz
  refine ⟨u, c, hu, ?_⟩
  have h1 : g' = (u : hypSU h (t + s) ε) * ((u : hypSU h (t + s) ε)⁻¹ *
      (g' * (x : hypSU h (t + s) ε)⁻¹)) * (x : hypSU h (t + s) ε) := by group
  have h2 : ((g' : hypSU h (t + s) ε) : GL (HypIndex (t + s) ε) K) =
      ((u : hypSU h (t + s) ε) : GL (HypIndex (t + s) ε) K) *
        GeneralLinearGroup.scalar (HypIndex (t + s) ε) c *
        ((x : hypSU h (t + s) ε) : GL (HypIndex (t + s) ε) K) := by
    conv_lhs => rw [h1]
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hcz]
  have h3 := congrArg (fun g : GL (HypIndex (t + s) ε) K =>
    (g : Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K)) h2
  simp only [Units.val_mul, coe_scalar_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one] at h3
  rw [hg'] at h3
  simpa [coe_glAut, Units.val_mul, Matrix.mul_assoc] using h3

section Blocks

variable (h) in
theorem eBlock_relation (hr : 1 ≤ t + s) (hε : ε ≤ 1) {I : Finset ℕ} (hI : IsTopCut I t)
    (γ : semilinearSimilitudes h (t + s) ε)
    (hNF : UniNormFix h hε hI (semilinearAutHom h hr hε γ))
    (hM : FlagCuts I t ((γ : SemiGL (HypIndex (t + s) ε) K).left : Matrix (HypIndex (t + s) ε)
      (HypIndex (t + s) ε) K))
    (hM' : FlagCuts I t (((γ : SemiGL (HypIndex (t + s) ε) K).left⁻¹ : GL (HypIndex (t + s) ε) K) :
      Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K))
    (b : ↥I) (hb2 : 2 ≤ b.1 - predCut I b.1)
    (B : Matrix.SpecialLinearGroup (Fin (b.1 - predCut I b.1)) K) :
    ∃ c : K, ((γ : SemiGL (HypIndex (t + s) ε) K).left : Matrix (HypIndex (t + s) ε)
        (HypIndex (t + s) ε) K).submatrix
          (eIdx (t + s) ε ((hI.le b.1 b.2).2.trans (Nat.le_add_right t s)))
          (eIdx (t + s) ε ((hI.le b.1 b.2).2.trans (Nat.le_add_right t s))) *
        (B : Matrix (Fin (b.1 - predCut I b.1)) (Fin (b.1 - predCut I b.1)) K).map
          (γ : SemiGL (HypIndex (t + s) ε) K).right =
      c • ((B : Matrix (Fin (b.1 - predCut I b.1)) (Fin (b.1 - predCut I b.1)) K) *
        ((γ : SemiGL (HypIndex (t + s) ε) K).left : Matrix (HypIndex (t + s) ε)
          (HypIndex (t + s) ε) K).submatrix
            (eIdx (t + s) ε ((hI.le b.1 b.2).2.trans (Nat.le_add_right t s)))
            (eIdx (t + s) ε ((hI.le b.1 b.2).2.trans (Nat.le_add_right t s)))) := by
  have hbr : b.1 ≤ t + s := (hI.le b.1 b.2).2.trans (Nat.le_add_right t s)
  have hb1 : 1 ≤ b.1 := (hI.le b.1 b.2).1
  have hA : leviEHom h ε hbr B ∈ flagStabilizer h (t + s) ε ↑I :=
    leviEHom_mem_flagStabilizer h hε (a := predCut I b.1) hbr (I := ↑I)
      (fun c hc => (hI.le c hc).2.trans (Nat.le_add_right t s))
      (fun c hc => by
        by_cases hcb : c < b.1
        · exact Or.inl (le_predCut hc hcb)
        · exact Or.inr (not_lt.mp hcb)) B
  set x : ↥(flagStabilizer h (t + s) ε ↑I) := ⟨leviEHom h ε hbr B, hA⟩ with hxdef
  have hlev := uniLeviHom_leviEHom (s := s) h hε hI b B hA
  have hx := hNF.2 (some b) hb2 x
    (fun k hk => by
      rw [hxdef, hlev, Pi.mulSingle_eq_of_ne hk])
    (by
      rw [hxdef, hlev, Pi.mulSingle_eq_same]
      exact ⟨B, rfl⟩)
  obtain ⟨u, c, hu, hrel⟩ := rel_of_normFix h hr hε hI γ x hx
  refine ⟨c, ?_⟩
  have hXblk : (((x : hypSU h (t + s) ε) : GL (HypIndex (t + s) ε) K) :
      Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K).submatrix (eIdx (t + s) ε hbr)
        (eIdx (t + s) ε hbr) =
      (B : Matrix (Fin (b.1 - predCut I b.1)) (Fin (b.1 - predCut I b.1)) K) := by
    have := congrArg (fun g : GL (Fin (b.1 - predCut I b.1)) K =>
      (g : Matrix (Fin (b.1 - predCut I b.1)) (Fin (b.1 - predCut I b.1)) K))
      (eBlockHom_leviEHom_self h hε b.2 hb1 hbr B hA)
    simpa [coe_eBlockHom] using this
  have hUblk : (((u : hypSU h (t + s) ε) : GL (HypIndex (t + s) ε) K) :
      Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K).submatrix
        (eIdx (t + s) ε (a := predCut I b.1) hbr) (eIdx (t + s) ε (a := predCut I b.1) hbr) =
      (1 : Matrix (Fin (b.1 - predCut I b.1)) (Fin (b.1 - predCut I b.1)) K) := by
    have h1 : uniLeviHom (s := s) h hε hI u (some b) = 1 := congrFun (MonoidHom.mem_ker.mp hu) _
    have h2 : eBlockHom h hε b.2 hb1 hbr u = 1 := h1
    have := congrArg (fun g : GL (Fin (b.1 - predCut I b.1)) K =>
      (g : Matrix (Fin (b.1 - predCut I b.1)) (Fin (b.1 - predCut I b.1)) K)) h2
    simpa [coe_eBlockHom] using this
  have hXc := flagCuts_of_mem_flagStabilizer (s := s) hε hI x.2
  have hUc := flagCuts_of_mem_flagStabilizer (s := s) hε hI u.2
  have key := block_rel_aux (φ := eIdx (t + s) ε (a := predCut I b.1) hbr)
    (eIdx_injective hbr) (mem_range_eIdx hbr) (γ : SemiGL (HypIndex (t + s) ε) K).right c
    (hM.cut_predCut b.1) (hM.1 b.1 b.2) (hM'.cut_predCut b.1) (hM'.1 b.1 b.2)
    (hXc.cut_predCut b.1) (hXc.1 b.1 b.2) (hUc.cut_predCut b.1)
    (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]) hUblk hrel
  rwa [hXblk] at key

variable (h) in
theorem resBlock_relation (hr : 1 ≤ t + s) (hε : ε ≤ 1) {I : Finset ℕ} (hI : IsTopCut I t)
    (γ : semilinearSimilitudes h (t + s) ε)
    (hNF : UniNormFix h hε hI (semilinearAutHom h hr hε γ))
    (hM : FlagCuts I t ((γ : SemiGL (HypIndex (t + s) ε) K).left : Matrix (HypIndex (t + s) ε)
      (HypIndex (t + s) ε) K))
    (hM' : FlagCuts I t (((γ : SemiGL (HypIndex (t + s) ε) K).left⁻¹ : GL (HypIndex (t + s) ε) K) :
      Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K))
    (hbig : 2 ≤ 2 * s + ε) (B : hypSU h s ε) :
    ∃ c : K, ((γ : SemiGL (HypIndex (t + s) ε) K).left : Matrix (HypIndex (t + s) ε)
        (HypIndex (t + s) ε) K).submatrix (resIdx t) (resIdx t) *
        ((B : GL (HypIndex s ε) K) : Matrix (HypIndex s ε) (HypIndex s ε) K).map
          (γ : SemiGL (HypIndex (t + s) ε) K).right =
      c • (((B : GL (HypIndex s ε) K) : Matrix (HypIndex s ε) (HypIndex s ε) K) *
        ((γ : SemiGL (HypIndex (t + s) ε) K).left : Matrix (HypIndex (t + s) ε)
          (HypIndex (t + s) ε) K).submatrix (resIdx t) (resIdx t)) := by
  have hB : leviResHom h hε t B ∈ flagStabilizer h (t + s) ε ↑I :=
    leviResHom_mem_flagStabilizer h hε t (I := ↑I) (fun c hc => (hI.le c hc).2) B
  set x : ↥(flagStabilizer h (t + s) ε ↑I) := ⟨leviResHom h hε t B, hB⟩ with hxdef
  have hlev := uniLeviHom_leviResHom (s := s) h hε hI B hB
  have hx := hNF.2 none hbig x
    (fun k hk => by
      rw [hxdef, hlev, Pi.mulSingle_eq_of_ne hk])
    (by
      rw [hxdef, hlev, Pi.mulSingle_eq_same]
      exact B.2)
  obtain ⟨u, c, hu, hrel⟩ := rel_of_normFix h hr hε hI γ x hx
  refine ⟨c, ?_⟩
  have hXblk : (((x : hypSU h (t + s) ε) : GL (HypIndex (t + s) ε) K) :
      Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K).submatrix (resIdx t) (resIdx t) =
      ((B : GL (HypIndex s ε) K) : Matrix (HypIndex s ε) (HypIndex s ε) K) := by
    rw [hxdef]
    change (extendMat (resIdx_injective t)
      ((B : GL (HypIndex s ε) K) : Matrix (HypIndex s ε) (HypIndex s ε) K)).submatrix
        (resIdx t) (resIdx t) = _
    exact submatrix_extendMat (resIdx_injective t) _
  have hUblk : (((u : hypSU h (t + s) ε) : GL (HypIndex (t + s) ε) K) :
      Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K).submatrix (resIdx t) (resIdx t) =
      (1 : Matrix (HypIndex s ε) (HypIndex s ε) K) := by
    have h1 : uniLeviHom (s := s) h hε hI u none = 1 := congrFun (MonoidHom.mem_ker.mp hu) _
    have h2 : resBlockHom h hε (Finset.mem_coe.mpr hI.mem) u = 1 := h1
    have := congrArg (fun g : GL (HypIndex s ε) K =>
      (g : Matrix (HypIndex s ε) (HypIndex s ε) K)) h2
    simpa [coe_resBlockHom] using this
  have hXc := flagCuts_of_mem_flagStabilizer (s := s) hε hI x.2
  have hUc := flagCuts_of_mem_flagStabilizer (s := s) hε hI u.2
  have key := block_rel_aux (φ := resIdx (s := s) (ε := ε) t) (resIdx_injective t)
    (mem_range_resIdx t) (γ : SemiGL (HypIndex (t + s) ε) K).right c
    (hM.1 t hI.mem) hM.2 (hM'.1 t hI.mem) hM'.2 (hXc.1 t hI.mem) hXc.2 (hUc.1 t hI.mem)
    (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]) hUblk hrel
  rwa [hXblk] at key

end Blocks

end Stab

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Uni
