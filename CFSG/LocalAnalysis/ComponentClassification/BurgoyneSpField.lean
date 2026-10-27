module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpBasic
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLField
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLUnitary
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpField
public import CFSG.RankThree.Classical.SteinbergBYSymplecticFieldDescent
public import CFSG.LieType.Universal.Symplectic
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.Sp

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (lam coe_lam pairMat statedSp_ext
  mem_statedSp_iff)
open CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.Burgoyne.PSL
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.UnbalancedCatalog (descentField mem_descentField)
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (subfieldSpHom
  subfieldSpHom_injective exists_subfieldSpHom_eq)
open scoped commutatorElement MatrixGroups

variable {r : ℕ} {K : Type} [Field K]

section Matrices

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem fix_unipotent_on {N : Matrix ι ι K} {x y : ι} (hxy : N x y ≠ 0) {D Di : Matrix ι ι K}
    (hDDi : D * Di = 1) (hDiD : Di * D = 1) {τ : K ≃+* K} {S : Set K} (h1 : (1 : K) ∈ S)
    (h : ∀ c ∈ S, D * (1 + τ c • N) * Di = 1 + c • N) :
    (∀ c ∈ S, τ c = c) ∧ D * N = N * D := by
  have key : ∀ c ∈ S, D * (τ c • N) * Di = c • N := by
    intro c hc
    have h2 := h c hc
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hDDi] at h2
    exact add_left_cancel h2
  have e1 := key 1 h1
  simp only [map_one, one_smul] at e1
  refine ⟨fun c hc => ?_, ?_⟩
  · have e2 := key c hc
    rw [Matrix.mul_smul, Matrix.smul_mul, e1] at e2
    have := congrFun (congrFun e2 x) y
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    exact mul_right_cancel₀ hxy this
  · calc D * N = D * N * Di * D := by rw [Matrix.mul_assoc _ Di, hDiD, Matrix.mul_one]
      _ = N * D := by rw [e1]

theorem commute_single_apply' {D : Matrix ι ι K} {a b : ι}
    (h : D * single a b 1 = single a b 1 * D) :
    D a a = D b b ∧ (∀ x, x ≠ a → D x a = 0) ∧ ∀ y, y ≠ b → D b y = 0 := by
  refine ⟨?_, fun x hx => ?_, fun y hy => ?_⟩
  · have := congrFun (congrFun h a) b
    simpa [mul_single_apply_same, single_mul_apply_same] using this
  · have := congrFun (congrFun h x) b
    rw [mul_single_apply_same, single_mul_apply_of_ne _ _ _ _ _ hx] at this
    simpa using this
  · have := congrFun (congrFun h a) y
    rw [single_mul_apply_same, mul_single_apply_of_ne _ _ _ _ _ hy] at this
    simpa using this.symm

end Matrices

theorem pairMat_map (f : K →+* K) {ι : Type} [DecidableEq ι] (a b : ι)
    (X : Matrix (Fin 2) (Fin 2) K) : (pairMat a b X).map f = pairMat a b (X.map f) := by
  ext x y
  simp only [pairMat, Matrix.map_apply, Matrix.of_apply, one_apply]
  split_ifs <;> simp

theorem pairMat_unip {ι : Type} [Fintype ι] [DecidableEq ι] {a b : ι} (hab : a ≠ b)
    (u v : K) : pairMat a b !![1, u; v, 1] = 1 + u • single a b 1 + v • single b a 1 := by
  ext x y
  by_cases hxa : x = a
  · subst hxa
    by_cases hya : y = x
    · subst hya
      simp [pairMat, Ne.symm hab]
    · by_cases hyb : y = b
      · subst hyb
        simp [pairMat, hya, Ne.symm hya]
      · simp [pairMat, hya, hyb, Ne.symm hya, Ne.symm hyb, one_apply]
  · by_cases hxb : x = b
    · subst hxb
      by_cases hya : y = a
      · subst hya
        simp [pairMat, hxa, Ne.symm hxa]
      · by_cases hyb : y = x
        · subst hyb
          simp [pairMat, hxa, Ne.symm hxa]
        · simp [pairMat, hxa, hya, hyb, Ne.symm hxa, Ne.symm hyb, Ne.symm hya, one_apply]
    · simp [pairMat, hxa, hxb, Ne.symm hxa, Ne.symm hxb, one_apply]

theorem pairMat_upper {ι : Type} [Fintype ι] [DecidableEq ι] {a b : ι} (hab : a ≠ b) (c : K) :
    pairMat a b !![1, c; 0, 1] = 1 + c • single a b 1 := by
  rw [pairMat_unip hab, zero_smul, add_zero]

theorem pairMat_lower {ι : Type} [Fintype ι] [DecidableEq ι] {a b : ι} (hab : a ≠ b) (c : K) :
    pairMat a b !![1, 0; c, 1] = 1 + c • single b a 1 := by
  rw [pairMat_unip hab, zero_smul, add_zero]

section Fixed

variable (r) in
abbrev spFixed (σ : K ≃+* K) : Subgroup (StatedSp r K) :=
  MonoidHom.eqLocus (fieldSp r K σ).toMonoidHom (MonoidHom.id _)

theorem range_subfieldSpHom (σ : K ≃+* K) :
    (subfieldSpHom r (descentField σ)).range = spFixed r σ := by
  ext g
  constructor
  · rintro ⟨g₀, rfl⟩
    apply statedSp_ext
    change ((((subfieldSpHom r (descentField σ) g₀ : StatedSp r K) :
      GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)).map σ = _
    ext i j
    rw [Matrix.map_apply]
    exact mem_descentField.1 (((g₀ : GL (Fin r ⊕ Fin r) (descentField σ)) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) (descentField σ)) i j).2
  · intro hg
    exact exists_subfieldSpHom_eq hg

theorem mem_spFixed {σ : K ≃+* K} {g : StatedSp r K}
    (hg : ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).map σ =
      ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) :
    g ∈ spFixed r σ :=
  statedSp_ext hg

theorem isQuasisimple_spFixed [Finite K] (hK : ringChar K ≠ 2) (hr : 2 ≤ r) (σ : K ≃+* K) :
    IsQuasisimple (spFixed r σ) := by
  have hodd := CatalogueBLinearHigherB.odd_card_of_ringChar_ne_two K hK
  have h0 := CatalogueBOrthogonalFieldFixed.subfield_card_odd hodd (descentField σ)
  have hq : IsQuasisimple (StatedSp r (descentField σ)) := by
    refine LieType.Universal.Symplectic.isQuasisimple r _ (by omega) ?_
    have : 2 ≤ Nat.card (descentField σ) := Finite.one_lt_card
    rcases Nat.lt_or_ge (Nat.card (descentField σ)) 4 with h | h
    · refine Or.inr (Or.inl ⟨?_, hr⟩)
      have h2 : Nat.card (descentField σ) ≠ 2 := by
        intro h2
        rw [h2] at h0
        exact absurd h0 (by decide)
      omega
    · exact Or.inl (Or.inr h)
  rw [← range_subfieldSpHom]
  exact LocalCores.isQuasisimple_of_mulEquiv (MonoidHom.ofInjective (subfieldSpHom_injective _))
    hq

theorem lam_upper_mem_spFixed {σ : K ≃+* K} (i : Fin r) {c : K} (hc : σ c = c)
    {X : SL(2, K)} (hX : (X : Matrix (Fin 2) (Fin 2) K) = !![1, c; 0, 1]) :
    lam i X ∈ spFixed r σ := by
  apply mem_spFixed
  rw [coe_lam, hX]
  change (pairMat _ _ _).map σ.toRingHom = _
  rw [pairMat_map]
  congr 1
  ext s t
  fin_cases s <;> fin_cases t <;> simp [hc]

theorem lam_lower_mem_spFixed {σ : K ≃+* K} (i : Fin r) {c : K} (hc : σ c = c)
    {X : SL(2, K)} (hX : (X : Matrix (Fin 2) (Fin 2) K) = !![1, 0; c, 1]) :
    lam i X ∈ spFixed r σ := by
  apply mem_spFixed
  rw [coe_lam, hX]
  change (pairMat _ _ _).map σ.toRingHom = _
  rw [pairMat_map]
  congr 1
  ext s t
  fin_cases s <;> fin_cases t <;> simp [hc]

abbrev symSingle (i j : Fin r) (c : K) : Matrix (Fin r) (Fin r) K :=
  c • (single i j 1 + single j i 1)

theorem symSingle_transpose (i j : Fin r) (c : K) : (symSingle i j c)ᵀ = symSingle i j c := by
  rw [symSingle, transpose_smul, transpose_add, transpose_single, transpose_single, add_comm]

theorem upper_mem_spFixed {σ : K ≃+* K} (i j : Fin r) {c : K} (hc : σ c = c) :
    upperUnipotentSp r K (symSingle_transpose i j c) ∈ spFixed r σ := by
  apply mem_spFixed
  rw [coe_upperUnipotentSp, fromBlocks_map]
  congr 1
  · exact Matrix.map_one _ (map_zero σ) (map_one σ)
  · ext x y
    simp only [symSingle, Matrix.map_apply, Matrix.smul_apply, Matrix.add_apply, single_apply,
      smul_eq_mul]
    split_ifs <;> simp [hc]
  · exact Matrix.map_zero _ (map_zero σ)
  · exact Matrix.map_one _ (map_zero σ) (map_one σ)

end Fixed

theorem eq_scalar_of_commute_roots {D : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} (i₀ : Fin r)
    (hu : ∀ i, D * single (Sum.inl i) (Sum.inr i) 1 = single (Sum.inl i) (Sum.inr i) 1 * D)
    (hl : ∀ i, D * single (Sum.inr i) (Sum.inl i) 1 = single (Sum.inr i) (Sum.inl i) 1 * D)
    (hm : ∀ i j, D * fromBlocks 0 (single i j 1 + single j i 1) 0 0 =
      fromBlocks 0 (single i j 1 + single j i 1) 0 0 * D) :
    D = Matrix.scalar (Fin r ⊕ Fin r) (D (Sum.inl i₀) (Sum.inl i₀)) := by
  have hdiag : ∀ x y, x ≠ y → D x y = 0 := by
    intro x y hxy
    rcases y with j | j
    · exact (commute_single_apply' (hu j)).2.1 x hxy
    · exact (commute_single_apply' (hl j)).2.1 x hxy
  have hpair : ∀ i, D (Sum.inl i) (Sum.inl i) = D (Sum.inr i) (Sum.inr i) :=
    fun i => (commute_single_apply' (hu i)).1
  have hmix : ∀ i j, D (Sum.inl i) (Sum.inl i) = D (Sum.inr j) (Sum.inr j) := by
    intro i j
    by_cases hij : i = j
    · rw [hij, hpair]
    have h := congrFun (congrFun (hm i j) (Sum.inl i)) (Sum.inr j)
    rw [Matrix.mul_apply, Matrix.mul_apply, Finset.sum_eq_single (Sum.inl i),
      Finset.sum_eq_single (Sum.inr j)] at h
    · simpa [fromBlocks, single_apply, hij] using h
    · intro z _ hz
      rw [hdiag z (Sum.inr j) hz, mul_zero]
    · simp
    · intro z _ hz
      rw [hdiag (Sum.inl i) z (Ne.symm hz), zero_mul]
    · simp
  ext x y
  rw [scalar_apply]
  by_cases hxy : x = y
  · subst hxy
    rw [diagonal_apply_eq]
    rcases x with j | j
    · rw [hpair j, ← hmix i₀ j]
    · rw [← hmix i₀ j]
  · rw [diagonal_apply_ne _ hxy, hdiag x y hxy]

theorem field_oddCoreIn_eq_bot [Finite K] (hK : ringChar K ≠ 2) (hr : 2 ≤ r)
    (hinj : Function.Injective
      (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))))
    {B : Subgroup (MulAut (StatedProj (StatedSp r K)))}
    (hB : (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))).range ≤
      B)
    {σ : K ≃+* K} (hσσ : ∀ x, σ (σ x) = x) (hσ : σ ≠ 1) :
    oddCoreIn B (fieldAut r K σ) = ⊥ := by
  have : Fintype K := Fintype.ofFinite K
  set p := ringChar K with hp
  have : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have i₀ : Fin r := ⟨0, by omega⟩
  rw [eq_bot_iff]
  intro y hy
  rw [mem_bot]
  have hodd := odd_orderOf_of_mem_oddCoreIn hy
  obtain ⟨D, τ, rfl⟩ := CatalogueBSymplecticRepresentation.automorphism_standard hK hr y
  have hq := isQuasisimple_spFixed hK hr σ (r := r)
  have hqim : IsQuasisimple ((spFixed r σ).map (conjProjH (StatedSp r K))) := by
    refine LocalCores.isQuasisimple_map hq _ fun hle => ?_
    obtain ⟨X, hX⟩ : ∃ X : SL(2, K), (X : Matrix (Fin 2) (Fin 2) K) = !![1, 1; 0, 1] :=
      ⟨⟨_, by simp [det_fin_two_of]⟩, rfl⟩
    have hmem := lam_upper_mem_spFixed (σ := σ) i₀ (map_one σ) hX
    have h1 : conjProjH (StatedSp r K) (lam i₀ X) = 1 := hle hmem
    have h3 : projH (StatedSp r K) (lam i₀ X) = 1 := hinj (by rw [map_one]; exact h1)
    have h4 := longRoot_inf hr i₀ (lam i₀ X) ⟨X, rfl⟩ ((QuotientGroup.eq_one_iff _).1 h3)
    have h5 := congrArg (fun g : StatedSp r K => ((g : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) (Sum.inl i₀) (Sum.inr i₀)) h4
    simp [coe_lam, hX, pairMat] at h5
  have hfix : ∀ g ∈ spFixed r σ,
      (conjAut r K D * fieldAut r K τ) (proj r K g) = proj r K g :=
    fun g hg => commute_oddCoreIn_of_fixedH hinj hB (fieldSp r K σ).toMonoidHom
      (fieldAut_proj σ) (fun _ h => h) (fun _ hh _ hg => conj_mem_eqLocus_of_scalarH _ hh hg)
      hqim hy hg
  have hperf := commutator_eq_self_of_isQuasisimple hq
  have hex := fun {g : StatedSp r K} (hg : g ∈ spFixed r σ) => semilinear_eq_of_fix hperf hfix hg
  set M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
    ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hM
  set Mi : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
    (((D : GL (Fin r ⊕ Fin r) K)⁻¹ : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hMi
  have hMMi : M * Mi = 1 := by rw [hM, hMi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hMiM : Mi * M = 1 := by rw [hM, hMi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  set S₀ : Set K := {c | σ c = c} with hS₀
  have h1S : (1 : K) ∈ S₀ := map_one σ
  have hup : ∀ i : Fin r, (∀ c ∈ S₀, τ c = c) ∧
      M * single (Sum.inl i) (Sum.inr i) 1 = single (Sum.inl i) (Sum.inr i) 1 * M := by
    intro i
    refine fix_unipotent_on (x := Sum.inl i) (y := Sum.inr i) (by simp) hMMi hMiM h1S
      fun c hc => ?_
    obtain ⟨X, hX⟩ : ∃ X : SL(2, K), (X : Matrix (Fin 2) (Fin 2) K) = !![1, c; 0, 1] :=
      ⟨⟨_, by simp [det_fin_two_of]⟩, rfl⟩
    have h := hex (lam_upper_mem_spFixed i hc hX)
    rw [coe_lam, hX] at h
    change M * (pairMat _ _ _).map τ.toRingHom * Mi = _ at h
    rw [pairMat_map, pairMat_upper Sum.inl_ne_inr] at h
    have e : (!![1, c; 0, 1] : Matrix (Fin 2) (Fin 2) K).map τ.toRingHom = !![1, τ c; 0, 1] := by
      ext s t
      fin_cases s <;> fin_cases t <;> simp
    rwa [e, pairMat_upper Sum.inl_ne_inr] at h
  have hlo : ∀ i : Fin r,
      M * single (Sum.inr i) (Sum.inl i) 1 = single (Sum.inr i) (Sum.inl i) 1 * M := by
    intro i
    refine (fix_unipotent_on (τ := τ) (x := Sum.inr i) (y := Sum.inl i) (by simp) hMMi hMiM h1S
      fun c hc => ?_).2
    obtain ⟨X, hX⟩ : ∃ X : SL(2, K), (X : Matrix (Fin 2) (Fin 2) K) = !![1, 0; c, 1] :=
      ⟨⟨_, by simp [det_fin_two_of]⟩, rfl⟩
    have h := hex (lam_lower_mem_spFixed i hc hX)
    rw [coe_lam, hX] at h
    change M * (pairMat _ _ _).map τ.toRingHom * Mi = _ at h
    rw [pairMat_map, pairMat_lower Sum.inl_ne_inr] at h
    have e : (!![1, 0; c, 1] : Matrix (Fin 2) (Fin 2) K).map τ.toRingHom = !![1, 0; τ c, 1] := by
      ext s t
      fin_cases s <;> fin_cases t <;> simp
    rwa [e, pairMat_lower Sum.inl_ne_inr] at h
  have hmid : ∀ i j : Fin r, M * fromBlocks 0 (single i j 1 + single j i 1) 0 0 =
      fromBlocks 0 (single i j 1 + single j i 1) 0 0 * M := by
    intro i j
    have hN : (fromBlocks 0 (single i j 1 + single j i 1) 0 0 :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) (Sum.inl i) (Sum.inr j) ≠ 0 := by
      by_cases hij : i = j
      · subst hij
        simpa [one_add_one_eq_two] using h2
      · simp [hij]
    refine (fix_unipotent_on (τ := τ) hN hMMi hMiM h1S fun c hc => ?_).2
    have h := hex (upper_mem_spFixed i j hc)
    rw [coe_upperUnipotentSp] at h
    have e1 : (fromBlocks 1 (symSingle i j c) 0 1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
        1 + c • fromBlocks 0 (single i j 1 + single j i 1) 0 0 := by
      rw [← fromBlocks_one, fromBlocks_smul, fromBlocks_add]
      simp [symSingle]
    have e2 : (fromBlocks 1 (symSingle i j c) 0 1 :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).map τ =
        1 + τ c • fromBlocks 0 (single i j 1 + single j i 1) 0 0 := by
      rw [fromBlocks_map, Matrix.map_one _ (map_zero τ) (map_one τ),
        Matrix.map_zero _ (map_zero τ), ← fromBlocks_one, fromBlocks_smul, fromBlocks_add]
      congr 1
      · simp
      · ext x y
        simp [symSingle, single_apply]
        split_ifs <;> simp
      · simp
      · simp
    rwa [e2, e1] at h
  have hτS : ∀ c, σ c = c → τ c = c := (hup i₀).1
  have hDs := eq_scalar_of_commute_roots i₀ (fun i => (hup i).2) hlo hmid
  have hD : conjAut r K D = 1 := by
    rw [conjAut_eq_one_iff (by omega)]
    have hu : IsUnit (M (Sum.inl i₀) (Sum.inl i₀)) := by
      rw [isUnit_iff_ne_zero]
      intro h0
      have : M = 0 := by rw [hDs, h0, map_zero]
      have h1 := hMMi
      rw [this, Matrix.zero_mul] at h1
      have := congrFun (congrFun h1 (Sum.inl i₀)) (Sum.inl i₀)
      simp at this
    refine ⟨hu.unit, Units.ext ?_⟩
    rw [GeneralLinearGroup.coe_scalar]
    exact hDs
  rw [hD, one_mul] at hodd ⊢
  have hτk : τ ^ orderOf (fieldAut r K τ) = 1 := by
    have h1 : conjAut r K 1 * fieldAut r K (τ ^ orderOf (fieldAut r K τ)) = 1 := by
      rw [map_one, one_mul, map_pow, pow_orderOf_eq_one]
    exact ((CatalogueBSymplecticRepresentation.conjAut_mul_fieldAut_eq_one_iff (by omega) 1
      _).1 h1).1
  rw [eq_one_of_fix_fixField h2 hσσ hσ hτS hodd hτk, map_one]

theorem conjAut_mul_fieldAut_not_mem [Finite K] (hr : 1 ≤ r) {A : gsp r K} {σ : K ≃+* K}
    (hσ : σ ≠ 1) : conjAut r K A * fieldAut r K σ ∉ spLinearAutGroup r K := by
  intro h
  have hrange : spLinearAutGroup r K = (conjAut r K).range := by
    rw [spLinearAutGroup, ← MonoidHom.coe_range, Subgroup.closure_eq]
  rw [hrange] at h
  obtain ⟨B, hB⟩ := h
  have h1 : conjAut r K (B⁻¹ * A) * fieldAut r K σ = 1 := by
    rw [map_mul, map_inv, mul_assoc, ← hB, inv_mul_cancel]
  exact hσ ((CatalogueBSymplecticRepresentation.conjAut_mul_fieldAut_eq_one_iff hr _ _).1 h1).1

theorem field_eq_bot [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hKc : Nat.card K = p ^ f) (hr : 2 ≤ r)
    (hinj : Function.Injective
      (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))))
    {X : Type} [Group X] [Finite X] {ψ : X →* MulAut (StatedProj (StatedSp r K))}
    (hψ : Function.Injective ψ)
    (hInn : (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))).range
      ≤ ψ.range)
    {t : X} (ht : orderOf t = 2) {A : gsp r K} {σ : K ≃+* K} (hσ : σ ≠ 1)
    (htA : ψ t = conjAut r K A * fieldAut r K σ) {Y : Subgroup X}
    (hYO : Y ≤ oddCentralizerCore t) : Y = ⊥ := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  obtain ⟨-, -, -, -, -, -, -, -, -, hdesc⟩ :=
    RankThree.Classical.SteinbergBY.symplectic_prime_semilinear_field_descent hp hf hr hKc
  have hmem : ψ t ∈ spSemilinearAutGroup r K := by
    rw [htA]
    exact mul_mem (spLinearAutGroup_le_spSemilinearAutGroup (conjAut_mem_spLinearAutGroup A))
      (fieldAut_mem_spSemilinearAutGroup σ)
  have hnot : ψ t ∉ spLinearAutGroup r K := by
    rw [htA]
    exact conjAut_mul_fieldAut_not_mem (by omega) hσ
  have hord : orderOf (ψ t) = 2 := by rw [orderOf_injective ψ hψ t, ht]
  obtain ⟨-, σ', hσ', -, h, hh, hht⟩ := hdesc 2 Nat.prime_two _ hmem hnot hord
  have hrange : spLinearAutGroup r K = (conjAut r K).range := by
    rw [spLinearAutGroup, ← MonoidHom.coe_range, Subgroup.closure_eq]
  rw [hrange] at hh
  obtain ⟨H, rfl⟩ := hh
  obtain ⟨hinj', hInn'⟩ := conj_embedding hψ hInn (conjAut r K H)⁻¹
  set ψ' := (MulAut.conj (conjAut r K H)⁻¹).toMonoidHom.comp ψ with hψ'def
  have hψ't : ψ' t = fieldAut r K σ' := by
    change (conjAut r K H)⁻¹ * ψ t * ((conjAut r K H)⁻¹)⁻¹ = _
    rw [hht]
    group
  have hσσ : ∀ x, σ' (σ' x) = x := by
    intro x
    have h2 : σ' ^ 2 = 1 := by rw [← hσ', pow_orderOf_eq_one]
    have := congrArg (fun τ : K ≃+* K => τ x) h2
    simpa [pow_two] using this
  have hσ'1 : σ' ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hσ'
    exact absurd hσ' (by decide)
  refine eq_bot_of_oddCoreIn hinj' ?_ hYO
  rw [hψ't]
  exact field_oddCoreIn_eq_bot hK hr hinj hInn' hσσ hσ'1

end CFSG.ComponentClassification.Burgoyne.Sp
