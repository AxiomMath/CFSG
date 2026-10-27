module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherOrthogonality
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearData
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveGeometryRealization

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial
open Module Submodule
open scoped Pointwise

universe u

variable {p f : ℕ} {K : Type} [Field K]

section SemiLin

variable {ι : Type} [Fintype ι] [DecidableEq ι]

@[expose] noncomputable def semiLin (x : SemiGL ι K) :
    (ι → K) →ₛₗ[(x.right : K →+* K)] (ι → K) where
  toFun v := (x.left : Matrix ι ι K) *ᵥ fun a => x.right (v a)
  map_add' v w := by
    rw [← mulVec_add]
    congr 1
    funext a
    simp
  map_smul' c v := by
    rw [← mulVec_smul]
    congr 1
    funext a
    simp

theorem semiLin_apply (x : SemiGL ι K) (v : ι → K) :
    semiLin x v = (x.left : Matrix ι ι K) *ᵥ fun a => x.right (v a) :=
  rfl

theorem semiGL_smul_eq_map (x : SemiGL ι K) (W : Submodule K (ι → K)) :
    x • W = W.map (semiLin x) := by
  ext v
  rw [semiGL_smul_def, Submodule.mem_map]
  constructor
  · intro hv
    obtain ⟨u, hu, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists v x.left _).mp hv
    refine ⟨fun a => x.right.symm (u a), hu, ?_⟩
    change (x.left : Matrix ι ι K) *ᵥ (fun a => x.right (x.right.symm (u a))) =
      (x.left : Matrix ι ι K) *ᵥ u
    simp only [RingEquiv.apply_symm_apply]
  · rintro ⟨u, hu, rfl⟩
    exact (Submodule.mem_smul_pointwise_iff_exists _ x.left _).mpr
      ⟨fun a => x.right (u a), by rw [mem_coordImage]; simpa using hu, rfl⟩

end SemiLin

variable {r ε : ℕ}

theorem hypForm_semiLin (h : UnitaryFieldData p f K) {x : SemiGL (HypIndex r ε) K} {μ : K}
    (hx : (((x.left : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K).map
        h.bar)ᵀ * hypGram r ε K *
      ((x.left : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
        μ • hypGram r ε K)
    (v w : HypIndex r ε → K) :
    hypForm h r ε (semiLin x v) (semiLin x w) = μ * x.right (hypForm h r ε v w) := by
  rw [semiLin_apply, semiLin_apply]
  change gramForm h (hypGram r ε K) _ _ = _
  rw [gramForm_mulVec, hx, gramForm_smul_gram]
  change μ * hypForm h r ε _ _ = _
  rw [hypForm_coord]

theorem subOrtho_semiGL_smul_iff (h : UnitaryFieldData p f K) {x : SemiGL (HypIndex r ε) K}
    (hx : x ∈ semilinearSimilitudes h r ε) (L M : Submodule K (HypIndex r ε → K)) :
    SubOrtho (hypForm h r ε) (x • L) (x • M) ↔ SubOrtho (hypForm h r ε) L M := by
  obtain ⟨μ, hμ0, -, hA⟩ := hx
  rw [semiGL_smul_eq_map, semiGL_smul_eq_map]
  constructor
  · intro hLM v hv w hw
    have := hLM _ (Submodule.mem_map_of_mem hv) _ (Submodule.mem_map_of_mem hw)
    rw [hypForm_semiLin h hA, mul_eq_zero, map_eq_zero_iff _ x.right.injective] at this
    exact this.resolve_left hμ0
  · rintro hLM _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩
    rw [hypForm_semiLin h hA, hLM v hv w hw, map_zero, mul_zero]

theorem lineOrth_semilinearPointAction (h : UnitaryFieldData p f K)
    (x : semilinearSimilitudes h r ε) (L M : hypIsotropicLines h r ε) :
    LineOrth h (semilinearPointAction h r ε x L) (semilinearPointAction h r ε x M) ↔
      LineOrth h L M :=
  subOrtho_semiGL_smul_iff h x.2 L M

variable (h : UnitaryFieldData p f K) in
@[expose] def toIsoLines (φ : Equiv.Perm (hypIsotropicLines h r ε)) :
    isoLines (hypForm h r ε) ≃ isoLines (hypForm h r ε) :=
  φ

theorem polarImage_semilinearPointAction (h : UnitaryFieldData p f K)
    (x : semilinearSimilitudes h r ε) {W : Submodule K (HypIndex r ε → K)}
    (hW : ∀ v ∈ W, ∀ w ∈ W, hypForm h r ε v w = 0) :
    polarImage (hypForm h r ε) (toIsoLines h (semilinearPointAction h r ε x)) W =
      (x : SemiGL (HypIndex r ε) K) • W := by
  rw [polarImage, ptSpan, Set.biUnion_image]
  conv_rhs => rw [← ptSpan_ptsIn hW, ptSpan, semiGL_smul_eq_map, Submodule.map_span,
    Set.image_iUnion₂]
  congr 1
  refine Set.iUnion₂_congr fun L _ => ?_
  change (((x : SemiGL (HypIndex r ε) K) • (L : Submodule K (HypIndex r ε → K)) :
    Submodule K (HypIndex r ε → K)) : Set (HypIndex r ε → K)) = _
  rw [semiGL_smul_eq_map, Submodule.map_coe]

theorem polarImage_trans (h : UnitaryFieldData p f K) {V : Type u} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm)
    (hBl : B.SeparatingLeft) {φ : isoLines B ≃ isoLines B}
    (hφ : ∀ L M : isoLines B, SubOrtho B L M ↔ SubOrtho B (φ L) (φ M)) (ψ : isoLines B ≃ isoLines B)
    {W : Submodule K V} (hW : ∀ x ∈ W, ∀ y ∈ W, B x y = 0) :
    polarImage B (φ.trans ψ) W = polarImage B ψ (polarImage B φ W) := by
  show ptSpan B ((φ.trans ψ) '' ptsIn B W) = ptSpan B (ψ '' ptsIn B (polarImage B φ W))
  rw [ptsIn_polarImage h hB hBl hφ hW, Set.image_image]
  rfl

section Coordinates

variable (r ε) in
@[expose] def hypXEmb : (Fin r → K) →ₗ[K] (HypIndex r ε → K) where
  toFun x := Sum.elim x 0
  map_add' x y := funext fun c => by rcases c with i | c <;> simp
  map_smul' t x := funext fun c => by rcases c with i | c <;> simp

variable (r ε) in
@[expose] def hypYEmb : (Fin r → K) →ₗ[K] (HypIndex r ε → K) where
  toFun y := Sum.elim 0 (Sum.elim 0 y)
  map_add' x y := funext fun c => by rcases c with i | k | i <;> simp
  map_smul' t x := funext fun c => by rcases c with i | k | i <;> simp

variable (K r ε) in
abbrev hypX : Submodule K (HypIndex r ε → K) :=
  LinearMap.range (hypXEmb (K := K) r ε)

variable (K r ε) in
abbrev hypY : Submodule K (HypIndex r ε → K) :=
  LinearMap.range (hypYEmb (K := K) r ε)

theorem hypXEmb_injective : Function.Injective (hypXEmb (K := K) r ε) := fun _ _ he =>
  funext fun i => congrFun he (Sum.inl i)

theorem hypYEmb_injective : Function.Injective (hypYEmb (K := K) r ε) := fun _ _ he =>
  funext fun i => congrFun he (Sum.inr (Sum.inr i))

theorem finrank_hypX : finrank K (hypX K r ε) = r := by
  rw [LinearMap.finrank_range_of_inj hypXEmb_injective, finrank_fin_fun]

theorem finrank_hypY : finrank K (hypY K r ε) = r := by
  rw [LinearMap.finrank_range_of_inj hypYEmb_injective, finrank_fin_fun]

theorem hypForm_hypXEmb (h : UnitaryFieldData p f K) (u : Fin r → K) (v : HypIndex r ε → K) :
    hypForm h r ε (hypXEmb r ε u) v = ∑ i, h.bar (u i) * v (Sum.inr (Sum.inr i)) := by
  rw [hypForm_apply, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp [hypXEmb, hypPartner]

theorem hypForm_hypYEmb (h : UnitaryFieldData p f K) (y : Fin r → K) (v : HypIndex r ε → K) :
    hypForm h r ε (hypYEmb r ε y) v = ∑ i, h.bar (y i) * v (Sum.inl i) := by
  rw [hypForm_apply, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp [hypYEmb, hypPartner]

theorem hypX_isotropic (h : UnitaryFieldData p f K) :
    ∀ v ∈ hypX K r ε, ∀ w ∈ hypX K r ε, hypForm h r ε v w = 0 := by
  rintro _ ⟨u, rfl⟩ _ ⟨u', rfl⟩
  rw [hypForm_hypXEmb]
  simp [hypXEmb]

theorem hypY_isotropic (h : UnitaryFieldData p f K) :
    ∀ v ∈ hypY K r ε, ∀ w ∈ hypY K r ε, hypForm h r ε v w = 0 := by
  rintro _ ⟨y, rfl⟩ _ ⟨y', rfl⟩
  rw [hypForm_hypYEmb]
  simp [hypYEmb]

theorem hypForm_hypXEmb_hypYEmb (h : UnitaryFieldData p f K) (u y : Fin r → K) :
    hypForm h r ε (hypXEmb r ε u) (hypYEmb r ε y) = (fun i => h.bar (u i)) ⬝ᵥ y := by
  rw [hypForm_hypXEmb]
  rfl

theorem hypX_inf_hypY : hypX K r ε ⊓ hypY K r ε = ⊥ := by
  rw [eq_bot_iff]
  rintro v ⟨⟨u, rfl⟩, ⟨y, hy⟩⟩
  rw [Submodule.mem_bot]
  have hu : u = 0 := funext fun i => by
    have := congrFun hy (Sum.inl i)
    simpa [hypXEmb, hypYEmb] using this.symm
  rw [hu, map_zero]

theorem hypX_eq_span :
    hypX K r ε = span K (Pi.basisFun K (HypIndex r ε) '' Set.range Sum.inl) := by
  refine (Submodule.eq_of_le_of_finrank_eq (span_le.mpr ?_) ?_).symm
  · rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    refine ⟨Pi.single i 1, funext fun c => ?_⟩
    rcases c with j | c
    · by_cases hij : j = i
      · subst hij
        simp [hypXEmb]
      · simp [hypXEmb, hij]
    · simp [hypXEmb]
  · rw [finrank_span_image_range _ Sum.inl_injective, Fintype.card_fin, finrank_hypX]

theorem hypY_eq_span :
    hypY K r ε = span K (Pi.basisFun K (HypIndex r ε) '' Set.range
      (fun i : Fin r => (Sum.inr (Sum.inr i) : HypIndex r ε))) := by
  have hinj : Function.Injective (fun i : Fin r => (Sum.inr (Sum.inr i) : HypIndex r ε)) :=
    fun i j he => by simpa using he
  refine (Submodule.eq_of_le_of_finrank_eq (span_le.mpr ?_) ?_).symm
  · rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    refine ⟨Pi.single i 1, funext fun c => ?_⟩
    rcases c with j | k | j
    · simp [hypYEmb]
    · simp [hypYEmb]
    · by_cases hij : j = i
      · subst hij
        simp [hypYEmb]
      · simp [hypYEmb, hij]
  · rw [finrank_span_image_range _ hinj, Fintype.card_fin, finrank_hypY]

end Coordinates

theorem exists_wittBasis_of_opposite (h : UnitaryFieldData p f K) (ε : ℕ) (hε : ε ≤ 1) :
    ∀ (r : ℕ) {V : Type u} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      {B : V →ₛₗ[h.bar] V →ₗ[K] K}, B.IsSymm → B.SeparatingLeft →
      finrank K V = 2 * r + ε → ∀ X Y : Submodule K V,
      (∀ x ∈ X, ∀ y ∈ X, B x y = 0) → (∀ x ∈ Y, ∀ y ∈ Y, B x y = 0) →
      finrank K X = r → finrank K Y = r → X ⊓ Y = ⊥ →
      ∃ w : Basis (HypIndex r ε) K V, (∀ x y, B (w x) (w y) = hypGram r ε K x y) ∧
        span K (w '' Set.range Sum.inl) = X ∧
        span K (w '' Set.range (fun i : Fin r => (Sum.inr (Sum.inr i) : HypIndex r ε))) = Y := by
  have hinj : ∀ r : ℕ,
      Function.Injective (fun i : Fin r => (Sum.inr (Sum.inr i) : HypIndex r ε)) :=
    fun r i j he => by simpa using he
  intro r
  induction r with
  | zero =>
    intro V _ _ _ B hB hBl hn X Y _ _ hX hY _
    obtain ⟨w, hw⟩ := exists_hypBasis h hB hBl hn
    refine ⟨w, hw, ?_, ?_⟩
    · rw [Set.range_eq_empty, Set.image_empty, span_empty]
      exact (Submodule.finrank_eq_zero.mp hX).symm
    · rw [Set.range_eq_empty, Set.image_empty, span_empty]
      exact (Submodule.finrank_eq_zero.mp hY).symm
  | succ r ih =>
    intro V _ _ _ B hB hBl hn X Y hXs hYs hX hY hXY
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := X) fun h0 => by
      rw [h0, finrank_bot] at hX
      omega
    have hvv : B v v = 0 := hXs v hv v hv
    obtain ⟨y, hy, hvy⟩ : ∃ y ∈ Y, B v y ≠ 0 := by
      by_contra! hz
      have hsup := sup_isotropic hvv hYs hz fun y hy => by rw [← hB.eq v y, hz y hy, map_zero]
      have h1 := Submodule.finrank_sup_add_finrank_inf_eq (K ∙ v) Y
      have h0 : K ∙ v ⊓ Y = ⊥ := by
        rw [eq_bot_iff]
        intro u hu
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu.1
        have : c • v ∈ X ⊓ Y := ⟨X.smul_mem c hv, hu.2⟩
        rwa [hXY] at this
      rw [h0, finrank_bot, finrank_span_singleton hv0, hY] at h1
      have := finrank_le_of_isTotIso h hB hBl hsup
      rw [hn] at this
      omega
    set w := (B v y)⁻¹ • y with hwdef
    have hwY : w ∈ Y := Y.smul_mem _ hy
    have hvw : B v w = 1 := by rw [hwdef, map_smul, smul_eq_mul, inv_mul_cancel₀ hvy]
    have hww : B w w = 0 := hYs w hwY w hwY
    have hwv : B w v = 1 := by rw [← hB.eq v w, hvw, map_one]
    have hw0 : w ≠ 0 := fun h0 => by
      rw [h0, map_zero] at hvw
      exact zero_ne_one hvw
    obtain ⟨-, hsplit⟩ := hermitian_hyperbolic_splitting h hB hBl hv0 hvv
    obtain ⟨-, -, -, hUsep, hUdim⟩ := hsplit w hvw hww
    have hXU := finrank_inf_orthogonal_add_one hv0 hwv hv fun x hx => hXs v hv x hx
    have hYU := finrank_inf_orthogonal_add_one hw0 hvw hwY fun x hx => hYs w hwY x hx
    rw [Set.pair_comm] at hYU
    set U := (Submodule.span K {v, w}).orthogonalBilin B with hU
    have hX'd : finrank K (X.comap U.subtype) = r := by
      rw [finrank_comap_subtype]
      omega
    have hY'd : finrank K (Y.comap U.subtype) = r := by
      rw [finrank_comap_subtype]
      omega
    have hX'Y' : X.comap U.subtype ⊓ Y.comap U.subtype = ⊥ := by
      rw [← Submodule.comap_inf, hXY, Submodule.comap_bot, Submodule.ker_subtype]
    obtain ⟨w', hw', hX'w, hY'w⟩ := ih (hB.domRestrict U) hUsep (by rw [hUdim, hn]; omega)
      (X.comap U.subtype) (Y.comap U.subtype)
      (fun x hx y hy => hXs x hx y hy) (fun x hx y hy => hYs x hx y hy) hX'd hY'd hX'Y'
    obtain ⟨t, ht_def⟩ : ∃ t : HypIndex r ε → V, t = fun x => (w' x : V) := ⟨_, rfl⟩
    have htx : ∀ x, t x = (w' x : V) := fun x => by rw [ht_def]
    have hvt : ∀ x, B v (t x) = 0 := fun x => by
      rw [htx]
      exact (mem_orthogonalBilin.mp (w' x).2) v (subset_span (by simp))
    have hwt : ∀ x, B w (t x) = 0 := fun x => by
      rw [htx]
      exact (mem_orthogonalBilin.mp (w' x).2) w (subset_span (by simp))
    have hc := consHyp_gram hvv hvw hwv hww (u := t) (fun x y => by rw [htx, htx]; exact hw' x y)
      hvt hwt (fun x => by rw [← hB.eq v, hvt, map_zero])
      (fun x => by rw [← hB.eq w, hwt, map_zero])
    set W := basisOfHypGram (consHyp v w t) hc hn with hW
    have hWc : ⇑W = consHyp v w t := coe_basisOfHypGram _ _ _
    have hmemX : ∀ x : HypIndex r ε, w' x ∈ X.comap U.subtype → t x ∈ X := fun x hx => by
      rw [htx]
      exact hx
    have hmemY : ∀ x : HypIndex r ε, w' x ∈ Y.comap U.subtype → t x ∈ Y := fun x hx => by
      rw [htx]
      exact hx
    refine ⟨W, fun x y => by rw [hWc, hc], ?_, ?_⟩
    · refine Submodule.eq_of_le_of_finrank_eq (span_le.mpr ?_) ?_
      · rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
        rw [SetLike.mem_coe, hWc]
        cases i using Fin.cases with
        | zero => exact hv
        | succ i =>
          refine hmemX (.inl i) ?_
          rw [← hX'w]
          exact subset_span ⟨.inl i, ⟨i, rfl⟩, rfl⟩
      · rw [finrank_span_image_range _ Sum.inl_injective, Fintype.card_fin, hX]
    · refine Submodule.eq_of_le_of_finrank_eq (span_le.mpr ?_) ?_
      · rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
        rw [SetLike.mem_coe, hWc]
        cases i using Fin.cases with
        | zero => exact hwY
        | succ i =>
          refine hmemY (.inr (.inr i)) ?_
          rw [← hY'w]
          exact subset_span ⟨.inr (.inr i), ⟨i, rfl⟩, rfl⟩
      · rw [finrank_span_image_range _ (hinj (r + 1)), Fintype.card_fin, hY]

section GLMat

variable {ι : Type} [Fintype ι] [DecidableEq ι]

@[expose] noncomputable def glOfLinearEquiv (g : (ι → K) ≃ₗ[K] (ι → K)) : GL ι K :=
  Matrix.GeneralLinearGroup.toLin.symm (LinearMap.GeneralLinearGroup.ofLinearEquiv g)

theorem glOfLinearEquiv_mulVec (g : (ι → K) ≃ₗ[K] (ι → K)) (v : ι → K) :
    ((glOfLinearEquiv g : GL ι K) : Matrix ι ι K) *ᵥ v = g v := by
  have h1 := Matrix.GeneralLinearGroup.coe_toLin (glOfLinearEquiv g)
  rw [glOfLinearEquiv, MulEquiv.apply_symm_apply] at h1
  have h2 := LinearMap.congr_fun h1 v
  rw [Matrix.mulVecLin_apply] at h2
  rw [glOfLinearEquiv, ← h2]
  rfl

end GLMat

section Levi

variable (h : UnitaryFieldData p f K)

@[expose] def leviFun (A C : Matrix (Fin r) (Fin r) K) (v : HypIndex r ε → K) :
    HypIndex r ε → K :=
  Sum.elim (A *ᵥ fun i => v (Sum.inl i))
    (Sum.elim (fun k => v (Sum.inr (Sum.inl k))) (C *ᵥ fun i => v (Sum.inr (Sum.inr i))))

theorem leviFun_leviFun (A C A' C' : Matrix (Fin r) (Fin r) K) (v : HypIndex r ε → K) :
    leviFun A C (leviFun A' C' v) = leviFun (A * A') (C * C') v := by
  funext c
  rcases c with i | k | i <;> simp [leviFun, mulVec_mulVec]

theorem leviFun_one (v : HypIndex r ε → K) : leviFun (1 : Matrix (Fin r) (Fin r) K) 1 v = v := by
  funext c
  rcases c with i | k | i <;> simp [leviFun]

noncomputable abbrev leviDual (A : GL (Fin r) K) : Matrix (Fin r) (Fin r) K :=
  ((((A⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K).map h.bar)ᵀ)

theorem bar_map_mul_inv (A : GL (Fin r) K) :
    ((A : Matrix (Fin r) (Fin r) K).map h.bar)ᵀ * leviDual h A = 1 := by
  rw [leviDual, ← transpose_mul, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, Matrix.map_one _ (map_zero h.bar) (map_one h.bar), transpose_one]

theorem leviDual_mul (A : GL (Fin r) K) :
    leviDual h A * ((A : Matrix (Fin r) (Fin r) K).map h.bar)ᵀ = 1 := by
  rw [leviDual, ← transpose_mul, ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, Matrix.map_one _ (map_zero h.bar) (map_one h.bar), transpose_one]

theorem leviDual_map_transpose (A : GL (Fin r) K) :
    ((leviDual h A).map h.bar)ᵀ = ((A⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) := by
  ext i j
  simp [h.bar_bar]

theorem bar_mulVec (M : Matrix (Fin r) (Fin r) K) (a : Fin r → K) :
    (fun i => h.bar ((M *ᵥ a) i)) = M.map h.bar *ᵥ fun i => h.bar (a i) := by
  funext i
  simp [mulVec, dotProduct, map_sum]

theorem bar_mulVec_dotProduct (M N : Matrix (Fin r) (Fin r) K) (a b : Fin r → K) :
    (fun i => h.bar ((M *ᵥ a) i)) ⬝ᵥ (N *ᵥ b) =
      (fun i => h.bar (a i)) ⬝ᵥ (((M.map h.bar)ᵀ * N) *ᵥ b) := by
  rw [bar_mulVec, dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm,
    mulVec_mulVec]

theorem hypForm_eq_dotProduct (v w : HypIndex r ε → K) :
    hypForm h r ε v w =
      (fun i => h.bar (v (Sum.inl i))) ⬝ᵥ (fun i => w (Sum.inr (Sum.inr i))) +
        (fun k => h.bar (v (Sum.inr (Sum.inl k)))) ⬝ᵥ (fun k => w (Sum.inr (Sum.inl k))) +
        (fun i => h.bar (v (Sum.inr (Sum.inr i)))) ⬝ᵥ (fun i => w (Sum.inl i)) := by
  rw [hypForm_apply, Fintype.sum_sum_type, Fintype.sum_sum_type, ← add_assoc]
  rfl

theorem hypForm_leviFun (A : GL (Fin r) K) (v w : HypIndex r ε → K) :
    hypForm h r ε (leviFun (A : Matrix (Fin r) (Fin r) K) (leviDual h A) v)
      (leviFun (A : Matrix (Fin r) (Fin r) K) (leviDual h A) w) = hypForm h r ε v w := by
  rw [hypForm_eq_dotProduct, hypForm_eq_dotProduct]
  simp only [leviFun, Sum.elim_inl, Sum.elim_inr]
  rw [bar_mulVec_dotProduct, bar_mulVec_dotProduct, bar_map_mul_inv, leviDual_map_transpose,
    ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec, one_mulVec]

@[expose] noncomputable def hypLeviEquiv (A : GL (Fin r) K) :
    (HypIndex r ε → K) ≃ₗ[K] (HypIndex r ε → K) where
  toFun := leviFun (A : Matrix (Fin r) (Fin r) K) (leviDual h A)
  invFun := leviFun ((A⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)
    (((A : Matrix (Fin r) (Fin r) K).map h.bar)ᵀ)
  map_add' v w := by
    funext c
    rcases c with i | k | i
    · change ((A : Matrix (Fin r) (Fin r) K) *ᵥ
        ((fun i => v (Sum.inl i)) + fun i => w (Sum.inl i))) i = _
      rw [mulVec_add]
      rfl
    · rfl
    · change (leviDual h A *ᵥ
        ((fun i => v (Sum.inr (Sum.inr i))) + fun i => w (Sum.inr (Sum.inr i)))) i = _
      rw [mulVec_add]
      rfl
  map_smul' t v := by
    funext c
    rcases c with i | k | i
    · change ((A : Matrix (Fin r) (Fin r) K) *ᵥ (t • fun i => v (Sum.inl i))) i = _
      rw [mulVec_smul]
      rfl
    · rfl
    · change (leviDual h A *ᵥ (t • fun i => v (Sum.inr (Sum.inr i)))) i = _
      rw [mulVec_smul]
      rfl
  left_inv v := by
    rw [leviFun_leviFun, ← Units.val_mul, inv_mul_cancel, Units.val_one, bar_map_mul_inv,
      leviFun_one]
  right_inv v := by
    rw [leviFun_leviFun, ← Units.val_mul, mul_inv_cancel, Units.val_one, leviDual_mul,
      leviFun_one]

theorem hypLeviEquiv_apply (A : GL (Fin r) K) (v : HypIndex r ε → K) :
    hypLeviEquiv h A v = leviFun (A : Matrix (Fin r) (Fin r) K) (leviDual h A) v :=
  rfl

theorem hypLevi_isometry (A : GL (Fin r) K) :
    (((glOfLinearEquiv (hypLeviEquiv (ε := ε) h A) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar)ᵀ * hypGram r ε K *
      ((glOfLinearEquiv (hypLeviEquiv (ε := ε) h A) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) = hypGram r ε K :=
  (gramForm_isometry_iff h _ _).mp fun v w => by
    rw [glOfLinearEquiv_mulVec, glOfLinearEquiv_mulVec, hypLeviEquiv_apply, hypLeviEquiv_apply]
    exact hypForm_leviFun h A v w

theorem leviFun_hypXEmb (A C : Matrix (Fin r) (Fin r) K) (u : Fin r → K) :
    leviFun A C (hypXEmb r ε u) = hypXEmb r ε (A *ᵥ u) := by
  funext c
  rcases c with i | k | i
  · rfl
  · rfl
  · change (C *ᵥ (0 : Fin r → K)) i = 0
    rw [mulVec_zero]
    rfl

theorem leviFun_hypYEmb (A C : Matrix (Fin r) (Fin r) K) (y : Fin r → K) :
    leviFun A C (hypYEmb r ε y) = hypYEmb r ε (C *ᵥ y) := by
  funext c
  rcases c with i | k | i
  · change (A *ᵥ (0 : Fin r → K)) i = 0
    rw [mulVec_zero]
    rfl
  · rfl
  · rfl

omit h in
theorem coord_hypXEmb (σ : K ≃+* K) (u : Fin r → K) :
    (fun a => σ (hypXEmb r ε u a)) = hypXEmb r ε (fun i => σ (u i)) := by
  funext c
  rcases c with i | c
  · rfl
  · change σ 0 = 0
    exact map_zero σ

omit h in
theorem coord_hypYEmb (σ : K ≃+* K) (y : Fin r → K) :
    (fun a => σ (hypYEmb r ε y a)) = hypYEmb r ε (fun i => σ (y i)) := by
  funext c
  rcases c with i | k | i
  · change σ 0 = 0
    exact map_zero σ
  · change σ 0 = 0
    exact map_zero σ
  · rfl

theorem semiLin_levi_hypXEmb (A : GL (Fin r) K) (σ : K ≃+* K) (u : Fin r → K) :
    semiLin (⟨glOfLinearEquiv (hypLeviEquiv (ε := ε) h A), σ⟩ : SemiGL (HypIndex r ε) K)
      (hypXEmb r ε u) = hypXEmb r ε ((A : Matrix (Fin r) (Fin r) K) *ᵥ fun i => σ (u i)) := by
  rw [semiLin_apply]
  change ((glOfLinearEquiv (hypLeviEquiv h A) : GL (HypIndex r ε) K) :
    Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ (fun a => σ (hypXEmb r ε u a)) = _
  rw [glOfLinearEquiv_mulVec, coord_hypXEmb, hypLeviEquiv_apply, leviFun_hypXEmb]

theorem semiLin_levi_hypYEmb (A : GL (Fin r) K) (σ : K ≃+* K) (y : Fin r → K) :
    semiLin (⟨glOfLinearEquiv (hypLeviEquiv (ε := ε) h A), σ⟩ : SemiGL (HypIndex r ε) K)
      (hypYEmb r ε y) = hypYEmb r ε (leviDual h A *ᵥ fun i => σ (y i)) := by
  rw [semiLin_apply]
  change ((glOfLinearEquiv (hypLeviEquiv h A) : GL (HypIndex r ε) K) :
    Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ (fun a => σ (hypYEmb r ε y a)) = _
  rw [glOfLinearEquiv_mulVec, coord_hypYEmb, hypLeviEquiv_apply, leviFun_hypYEmb]

theorem levi_smul_map_hypXEmb (A : GL (Fin r) K) (σ : K ≃+* K) (W : Submodule K (Fin r → K)) :
    (⟨glOfLinearEquiv (hypLeviEquiv (ε := ε) h A), σ⟩ : SemiGL (HypIndex r ε) K) •
        W.map (hypXEmb r ε) =
      ((LinearFlag.coordImage σ W).map (mulVecLin (A : Matrix (Fin r) (Fin r) K))).map
        (hypXEmb r ε) := by
  rw [semiGL_smul_eq_map]
  ext v
  simp only [Submodule.mem_map]
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨_, ⟨fun i => σ (u i), LinearFlag.coord_mem_coordImage hu, rfl⟩,
      (semiLin_levi_hypXEmb h A σ u).symm⟩
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨hypXEmb r ε (fun i => σ.symm (z i)), ⟨_, hz, rfl⟩, ?_⟩
    rw [semiLin_levi_hypXEmb]
    simp only [RingEquiv.apply_symm_apply]
    rfl

theorem levi_smul_hypY (A : GL (Fin r) K) (σ : K ≃+* K) :
    (⟨glOfLinearEquiv (hypLeviEquiv (ε := ε) h A), σ⟩ : SemiGL (HypIndex r ε) K) •
      hypY K r ε = hypY K r ε := by
  rw [semiGL_smul_eq_map]
  apply le_antisymm
  · rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨_, (semiLin_levi_hypYEmb h A σ y).symm⟩
  · rintro _ ⟨y, rfl⟩
    refine ⟨hypYEmb r ε (fun i => σ.symm
      ((((A : Matrix (Fin r) (Fin r) K).map h.bar)ᵀ *ᵥ y) i)), ⟨_, rfl⟩, ?_⟩
    rw [semiLin_levi_hypYEmb]
    simp only [RingEquiv.apply_symm_apply]
    change hypYEmb r ε (leviDual h A *ᵥ (((A : Matrix (Fin r) (Fin r) K).map h.bar)ᵀ *ᵥ y)) = _
    rw [mulVec_mulVec, leviDual_mul, one_mulVec]

end Levi

section XPoints

theorem finrank_map_hypXEmb (W : Submodule K (Fin r → K)) :
    finrank K (W.map (hypXEmb r ε)) = finrank K W :=
  (Submodule.equivMapOfInjective _ hypXEmb_injective W).finrank_eq.symm

theorem map_comap_hypXEmb {W : Submodule K (HypIndex r ε → K)} (hW : W ≤ hypX K r ε) :
    (W.comap (hypXEmb r ε)).map (hypXEmb r ε) = W := by
  rw [Submodule.map_comap_eq, inf_eq_right.mpr hW]

theorem comap_map_hypXEmb (W : Submodule K (Fin r → K)) :
    (W.map (hypXEmb r ε)).comap (hypXEmb r ε) = W :=
  Submodule.comap_map_eq_of_injective hypXEmb_injective W

theorem finrank_comap_hypXEmb {W : Submodule K (HypIndex r ε → K)} (hW : W ≤ hypX K r ε) :
    finrank K (W.comap (hypXEmb r ε)) = finrank K W := by
  rw [← finrank_map_hypXEmb, map_comap_hypXEmb hW]

theorem comap_le_comap_hypXEmb_iff {W W' : Submodule K (HypIndex r ε → K)}
    (hW : W ≤ hypX K r ε) (hW' : W' ≤ hypX K r ε) :
    W.comap (hypXEmb r ε) ≤ W'.comap (hypXEmb r ε) ↔ W ≤ W' := by
  rw [← Submodule.map_le_map_iff_of_injective hypXEmb_injective, map_comap_hypXEmb hW,
    map_comap_hypXEmb hW']

variable (h : UnitaryFieldData p f K)

@[expose] def hypXPoint (L' : ProjectiveGeometry.Point r K) : hypIsotropicLines h r ε :=
  ⟨L'.1.map (hypXEmb r ε), by rw [finrank_map_hypXEmb]; exact L'.2,
    fun a ha => hypX_isotropic h a (LinearMap.map_le_range ha) a (LinearMap.map_le_range ha)⟩

theorem coe_hypXPoint (L' : ProjectiveGeometry.Point r K) :
    ((hypXPoint (ε := ε) h L' : hypIsotropicLines h r ε) : Submodule K (HypIndex r ε → K)) =
      L'.1.map (hypXEmb r ε) :=
  rfl

@[expose] def hypToKPoint (L : hypIsotropicLines h r ε)
    (hL : (L : Submodule K (HypIndex r ε → K)) ≤ hypX K r ε) : ProjectiveGeometry.Point r K :=
  ⟨(L : Submodule K (HypIndex r ε → K)).comap (hypXEmb r ε), by
    rw [finrank_comap_hypXEmb hL]
    exact L.2.1⟩

theorem coe_hypToKPoint (L : hypIsotropicLines h r ε)
    (hL : (L : Submodule K (HypIndex r ε → K)) ≤ hypX K r ε) :
    (hypToKPoint h L hL).1 = (L : Submodule K (HypIndex r ε → K)).comap (hypXEmb r ε) :=
  rfl

theorem hypXPoint_hypToKPoint (L : hypIsotropicLines h r ε)
    (hL : (L : Submodule K (HypIndex r ε → K)) ≤ hypX K r ε) :
    hypXPoint h (hypToKPoint h L hL) = L :=
  Subtype.ext (map_comap_hypXEmb hL)

theorem span_mem_hypIsotropicLines {v : HypIndex r ε → K} (hv0 : v ≠ 0)
    (hv : hypForm h r ε v v = 0) : K ∙ v ∈ hypIsotropicLines h r ε :=
  mem_hypIsotropicLines.mpr ⟨finrank_span_singleton hv0, fun x hx => by
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    simp [hv]⟩

end XPoints

theorem eq_smul_of_dotProduct_iff {y y' : Fin r → K} (hy : y ≠ 0)
    (hyy : ∀ u : Fin r → K, u ⬝ᵥ y = 0 ↔ u ⬝ᵥ y' = 0) : ∃ l : K, l ≠ 0 ∧ y' = l • y := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hy
  have hi' : y i ≠ 0 := hi
  have key : ∀ j, y' j = y' i / y i * y j := by
    intro j
    have hu := (hyy ((y i) • Pi.single j 1 - (y j) • Pi.single i 1)).1 (by
      rw [sub_dotProduct, smul_dotProduct, smul_dotProduct, single_dotProduct, single_dotProduct]
      simp only [smul_eq_mul]
      ring)
    rw [sub_dotProduct, smul_dotProduct, smul_dotProduct, single_dotProduct, single_dotProduct]
      at hu
    simp only [smul_eq_mul, one_mul] at hu
    rw [div_mul_eq_mul_div, eq_div_iff hi']
    linear_combination hu
  refine ⟨y' i / y i, fun h0 => hi' ?_, funext fun j => by rw [key j, Pi.smul_apply, smul_eq_mul]⟩
  have hy'0 : y' = 0 := funext fun j => by rw [key j, h0, zero_mul, Pi.zero_apply]
  have := (hyy (Pi.single i 1)).2 (by rw [hy'0, dotProduct_zero])
  rwa [single_dotProduct, one_mul] at this

theorem eq_of_le_hypY (h : UnitaryFieldData p f K) (ψ : Equiv.Perm (hypIsotropicLines h r ε))
    (hψ : ∀ L M : hypIsotropicLines h r ε, LineOrth h L M ↔ LineOrth h (ψ L) (ψ M))
    (hX : ∀ L : hypIsotropicLines h r ε,
      (L : Submodule K (HypIndex r ε → K)) ≤ hypX K r ε → ψ L = L)
    {L : hypIsotropicLines h r ε} (hL : (L : Submodule K (HypIndex r ε → K)) ≤ hypY K r ε)
    (hψL : (ψ L : Submodule K (HypIndex r ε → K)) ≤ hypY K r ε) : ψ L = L := by
  obtain ⟨m, hm0, -, hLm⟩ := exists_eq_span_of_mem_hypIsotropicLines h L.2
  obtain ⟨m', hm'0, -, hψm'⟩ := exists_eq_span_of_mem_hypIsotropicLines h (ψ L).2
  obtain ⟨y, rfl⟩ : m ∈ hypY K r ε := hL (by rw [hLm]; exact mem_span_singleton_self m)
  obtain ⟨y', rfl⟩ : m' ∈ hypY K r ε := hψL (by rw [hψm']; exact mem_span_singleton_self _)
  have hy0 : y ≠ 0 := fun h0 => hm0 (by rw [h0, map_zero])
  have hkey : ∀ u : Fin r → K, u ⬝ᵥ y = 0 ↔ u ⬝ᵥ y' = 0 := by
    intro u
    set u' : Fin r → K := fun i => h.bar (u i) with hu'def
    have hu' : (fun i => h.bar (u' i)) = u := funext fun i => h.bar_bar (u i)
    by_cases hu0 : u' = 0
    · have hu : u = 0 := by
        rw [← hu', hu0]
        funext i
        simp
      simp [hu]
    have hx0 : hypXEmb r ε u' ≠ 0 := fun h0 =>
      hu0 (hypXEmb_injective (h0.trans (map_zero _).symm))
    let P : hypIsotropicLines h r ε := ⟨K ∙ hypXEmb r ε u',
      span_mem_hypIsotropicLines h hx0 (hypX_isotropic h _ ⟨u', rfl⟩ _ ⟨u', rfl⟩)⟩
    have hPX : (P : Submodule K (HypIndex r ε → K)) ≤ hypX K r ε :=
      (span_singleton_le_iff_mem _ _).mpr ⟨u', rfl⟩
    have hiff := hψ P L
    rw [hX P hPX] at hiff
    have hiff' : SubOrtho (hypForm h r ε) (K ∙ hypXEmb r ε u') (L : Submodule K _) ↔
        SubOrtho (hypForm h r ε) (K ∙ hypXEmb r ε u') (ψ L : Submodule K _) := hiff
    rw [hLm, hψm'] at hiff'
    unfold SubOrtho at hiff'
    rw [orth_span_iff, orth_span_iff, hypForm_hypXEmb_hypYEmb, hypForm_hypXEmb_hypYEmb, hu']
      at hiff'
    exact hiff'
  obtain ⟨l, hl, hly⟩ := eq_smul_of_dotProduct_iff hy0 hkey
  apply Subtype.ext
  rw [hψm', hLm, hly, map_smul, span_singleton_smul_eq (IsUnit.mk0 _ hl)]


theorem unitary_opposite_space_normalization (h : UnitaryFieldData p f K) (hr : 3 ≤ r)
    (hε : ε ≤ 1) (φ : Equiv.Perm (hypIsotropicLines h r ε))
    (hφ : ∀ L M : hypIsotropicLines h r ε, LineOrth h L M ↔ LineOrth h (φ L) (φ M)) :
    ∃ x : semilinearSimilitudes h r ε,
      ((((x : SemiGL (HypIndex r ε) K).left : GL (HypIndex r ε) K) :
          Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar)ᵀ * hypGram r ε K *
        (((x : SemiGL (HypIndex r ε) K).left : GL (HypIndex r ε) K) :
          Matrix (HypIndex r ε) (HypIndex r ε) K) = hypGram r ε K ∧
      ∀ L : hypIsotropicLines h r ε,
        ((L : Submodule K (HypIndex r ε → K)) ≤ hypX K r ε ∨
          (L : Submodule K (HypIndex r ε → K)) ≤ hypY K r ε) →
        φ L = semilinearPointAction h r ε x L := by
  have hB := hypForm_isSymm h (r := r) (ε := ε)
  have hBl := hypForm_separatingLeft h (r := r) (ε := ε)
  have hXs := hypX_isotropic h (r := r) (ε := ε)
  have hYs := hypY_isotropic h (r := r) (ε := ε)
  have hcomp : ∀ (x : semilinearSimilitudes h r ε) (ψ : Equiv.Perm (hypIsotropicLines h r ε)),
      (∀ L M, LineOrth h L M ↔ LineOrth h (ψ L) (ψ M)) →
      ∀ L M, LineOrth h L M ↔ LineOrth h (((semilinearPointAction h r ε x)⁻¹ * ψ) L)
        (((semilinearPointAction h r ε x)⁻¹ * ψ) M) := by
    intro x ψ hψ L M
    rw [hψ L M]
    have := lineOrth_semilinearPointAction h x⁻¹ (ψ L) (ψ M)
    rw [map_inv] at this
    exact this.symm
  set φ' := toIsoLines h φ with hφ'def
  have hφ' : ∀ L M : isoLines (hypForm h r ε),
      SubOrtho (hypForm h r ε) L M ↔ SubOrtho (hypForm h r ε) (φ' L) (φ' M) := fun L M => hφ L M
  set X₁ := polarImage (hypForm h r ε) φ' (hypX K r ε) with hX₁
  set Y₁ := polarImage (hypForm h r ε) φ' (hypY K r ε) with hY₁
  have hX₁s := isTotIso_polarImage φ' hφ' hXs
  have hY₁s := isTotIso_polarImage φ' hφ' hYs
  have hX₁d : finrank K X₁ = r := by
    rw [hX₁, finrank_polarImage h hB hBl hφ' hXs, finrank_hypX]
  have hY₁d : finrank K Y₁ = r := by
    rw [hY₁, finrank_polarImage h hB hBl hφ' hYs, finrank_hypY]
  have hX₁Y₁ : X₁ ⊓ Y₁ = ⊥ := by
    have hZs : ∀ v ∈ X₁ ⊓ Y₁, ∀ w ∈ X₁ ⊓ Y₁, hypForm h r ε v w = 0 :=
      fun v hv w hw => hX₁s v hv.1 w hw.1
    have hφ'' := subOrtho_symm_iff φ' hφ'
    have h1 : polarImage (hypForm h r ε) φ'.symm (X₁ ⊓ Y₁) ≤ hypX K r ε := by
      rw [← polarImage_symm_polarImage h hB hBl hφ' hXs]
      exact (polarImage_le_iff h hB hBl hφ'' hZs hX₁s).2 inf_le_left
    have h2 : polarImage (hypForm h r ε) φ'.symm (X₁ ⊓ Y₁) ≤ hypY K r ε := by
      rw [← polarImage_symm_polarImage h hB hBl hφ' hYs]
      exact (polarImage_le_iff h hB hBl hφ'' hZs hY₁s).2 inf_le_right
    have h0 : polarImage (hypForm h r ε) φ'.symm (X₁ ⊓ Y₁) = ⊥ := by
      rw [eq_bot_iff, ← hypX_inf_hypY]
      exact le_inf h1 h2
    have hd := finrank_polarImage h hB hBl hφ'' hZs
    rw [h0, finrank_bot] at hd
    exact Submodule.finrank_eq_zero.mp hd.symm
  obtain ⟨w, hw, hwX, hwY⟩ := exists_wittBasis_of_opposite h ε hε r hB hBl finrank_hypIndex_fun
    X₁ Y₁ hX₁s hY₁s hX₁d hY₁d hX₁Y₁
  set g := (Pi.basisFun K (HypIndex r ε)).equiv w (Equiv.refl _) with hg
  have hgiso : ∀ u v, hypForm h r ε (g u) (g v) = hypForm h r ε u v :=
    isometry_basis_equiv (Pi.basisFun K (HypIndex r ε)) w fun x y => by
      rw [hw, Pi.basisFun_apply, Pi.basisFun_apply, gramForm_single]
  have hgb : ∀ x, g (Pi.basisFun K (HypIndex r ε) x) = w x := fun x => by
    rw [hg, Module.Basis.equiv_apply, Equiv.refl_apply]
  set T₀ := glOfLinearEquiv g with hT₀
  have hT₀v : ∀ v, (T₀ : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v = g v :=
    glOfLinearEquiv_mulVec g
  have hT₀J : ((T₀ : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar)ᵀ * hypGram r ε K *
      (T₀ : Matrix (HypIndex r ε) (HypIndex r ε) K) = hypGram r ε K :=
    (gramForm_isometry_iff h _ _).mp fun u v => by
      rw [hT₀v, hT₀v]
      exact hgiso u v
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : semilinearSimilitudes h r ε,
      (x₀ : SemiGL (HypIndex r ε) K) = ⟨T₀, 1⟩ :=
    ⟨⟨⟨T₀, 1⟩, 1, one_ne_zero, map_one _, by rw [one_smul]; exact hT₀J⟩, rfl⟩
  have hx₀W : ∀ W : Submodule K (HypIndex r ε → K),
      (x₀ : SemiGL (HypIndex r ε) K) • W = W.map (g : (HypIndex r ε → K) →ₗ[K] _) := by
    intro W
    rw [semiGL_smul_eq_map, hx₀]
    ext v
    simp only [Submodule.mem_map]
    refine exists_congr fun u => and_congr_right fun _ => ?_
    rw [semiLin_apply]
    rw [show ((T₀ : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ
      (fun a => (1 : K ≃+* K) (u a)) = g u from hT₀v u]
    rfl
  have hx₀X : (x₀ : SemiGL (HypIndex r ε) K) • hypX K r ε = X₁ := by
    rw [hx₀W, hypX_eq_span, Submodule.map_span, ← hwX, Set.image_image]
    congr 1
    exact Set.image_congr fun x _ => hgb x
  have hx₀Y : (x₀ : SemiGL (HypIndex r ε) K) • hypY K r ε = Y₁ := by
    rw [hx₀W, hypY_eq_span, Submodule.map_span, ← hwY, Set.image_image]
    congr 1
    exact Set.image_congr fun x _ => hgb x
  obtain ⟨ψ₁, hψ₁def⟩ : ∃ ψ₁ : Equiv.Perm (hypIsotropicLines h r ε),
      ψ₁ = (semilinearPointAction h r ε x₀)⁻¹ * φ := ⟨_, rfl⟩
  have hψ₁ : ∀ L M, LineOrth h L M ↔ LineOrth h (ψ₁ L) (ψ₁ M) := by
    rw [hψ₁def]
    exact hcomp x₀ φ hφ
  obtain ⟨ψ₁', hψ₁'def⟩ : ∃ ψ₁' : isoLines (hypForm h r ε) ≃ isoLines (hypForm h r ε),
      ψ₁' = toIsoLines h ψ₁ := ⟨_, rfl⟩
  have hψ₁'L : ∀ L : hypIsotropicLines h r ε,
      (ψ₁' L : Submodule K (HypIndex r ε → K)) = (ψ₁ L : Submodule K (HypIndex r ε → K)) :=
    fun L => by rw [hψ₁'def]; rfl
  have hψ₁' : ∀ L M : isoLines (hypForm h r ε),
      SubOrtho (hypForm h r ε) L M ↔ SubOrtho (hypForm h r ε) (ψ₁' L) (ψ₁' M) := by
    rw [hψ₁'def]
    exact fun L M => hψ₁ L M
  have hψ₁eq : ψ₁' = φ'.trans (toIsoLines h (semilinearPointAction h r ε x₀⁻¹)) := by
    rw [hψ₁'def, hψ₁def, map_inv]
    rfl
  have hψ₁X : polarImage (hypForm h r ε) ψ₁' (hypX K r ε) = hypX K r ε := by
    rw [hψ₁eq, polarImage_trans h hB hBl hφ' _ hXs, polarImage_semilinearPointAction h x₀⁻¹ hX₁s,
      ← hX₁, ← hx₀X, InvMemClass.coe_inv, inv_smul_smul]
  have hψ₁Y : polarImage (hypForm h r ε) ψ₁' (hypY K r ε) = hypY K r ε := by
    rw [hψ₁eq, polarImage_trans h hB hBl hφ' _ hYs, polarImage_semilinearPointAction h x₀⁻¹ hY₁s,
      ← hY₁, ← hx₀Y, InvMemClass.coe_inv, inv_smul_smul]
  have hptsX := ptsIn_polarImage h hB hBl hψ₁' hXs
  rw [hψ₁X] at hptsX
  have hptsY := ptsIn_polarImage h hB hBl hψ₁' hYs
  rw [hψ₁Y] at hptsY
  have hmapX : ∀ L : hypIsotropicLines h r ε, (L : Submodule K (HypIndex r ε → K)) ≤ hypX K r ε →
      (ψ₁ L : Submodule K (HypIndex r ε → K)) ≤ hypX K r ε := fun L hL => by
    have : ψ₁' L ∈ ψ₁' '' ptsIn (hypForm h r ε) (hypX K r ε) := ⟨L, hL, rfl⟩
    rw [← hptsX] at this
    rw [← hψ₁'L]
    exact this
  have hmapY : ∀ L : hypIsotropicLines h r ε, (L : Submodule K (HypIndex r ε → K)) ≤ hypY K r ε →
      (ψ₁ L : Submodule K (HypIndex r ε → K)) ≤ hypY K r ε := fun L hL => by
    have : ψ₁' L ∈ ψ₁' '' ptsIn (hypForm h r ε) (hypY K r ε) := ⟨L, hL, rfl⟩
    rw [← hptsY] at this
    rw [← hψ₁'L]
    exact this
  have hmapX' : ∀ L : hypIsotropicLines h r ε,
      (L : Submodule K (HypIndex r ε → K)) ≤ hypX K r ε →
      (ψ₁.symm L : Submodule K (HypIndex r ε → K)) ≤ hypX K r ε := fun L hL => by
    have hL' : (L : isoLines (hypForm h r ε)) ∈ ptsIn (hypForm h r ε) (hypX K r ε) := hL
    rw [hptsX] at hL'
    obtain ⟨M, hM, hML⟩ := hL'
    have hML' : ψ₁ M = L := by
      apply Subtype.ext
      rw [← hψ₁'L M]
      exact congrArg Subtype.val hML
    have hsymm : ψ₁.symm L = M := (Equiv.symm_apply_eq ψ₁).mpr hML'.symm
    rw [hsymm]
    exact hM
  have hfwd : ∀ L' : ProjectiveGeometry.Point r K,
      (ψ₁ (hypXPoint h L') : Submodule K (HypIndex r ε → K)) ≤ hypX K r ε :=
    fun L' => hmapX _ LinearMap.map_le_range
  have hbwd : ∀ L' : ProjectiveGeometry.Point r K,
      (ψ₁.symm (hypXPoint h L') : Submodule K (HypIndex r ε → K)) ≤ hypX K r ε :=
    fun L' => hmapX' _ LinearMap.map_le_range
  let fP : ProjectiveGeometry.Point r K ≃ ProjectiveGeometry.Point r K :=
    { toFun := fun L' => hypToKPoint h (ψ₁ (hypXPoint h L')) (hfwd L')
      invFun := fun L' => hypToKPoint h (ψ₁.symm (hypXPoint h L')) (hbwd L')
      left_inv := fun L' => Subtype.ext (by
        rw [coe_hypToKPoint, hypXPoint_hypToKPoint, Equiv.symm_apply_apply, coe_hypXPoint,
          comap_map_hypXEmb])
      right_inv := fun L' => Subtype.ext (by
        rw [coe_hypToKPoint, hypXPoint_hypToKPoint, Equiv.apply_symm_apply, coe_hypXPoint,
          comap_map_hypXEmb]) }
  have hHs : ∀ H : Submodule K (Fin r → K), ∀ v ∈ H.map (hypXEmb r ε),
      ∀ w ∈ H.map (hypXEmb r ε), hypForm h r ε v w = 0 :=
    fun H v hv w hw => hXs v (LinearMap.map_le_range hv) w (LinearMap.map_le_range hw)
  have hψ₁'' := subOrtho_symm_iff ψ₁' hψ₁'
  have hle₁ : ∀ H : Submodule K (Fin r → K),
      polarImage (hypForm h r ε) ψ₁' (H.map (hypXEmb r ε)) ≤ hypX K r ε := fun H => by
    rw [← hψ₁X]
    exact (polarImage_le_iff h hB hBl hψ₁' (hHs H) hXs).2 LinearMap.map_le_range
  have hψ₁sX : polarImage (hypForm h r ε) ψ₁'.symm (hypX K r ε) = hypX K r ε := by
    conv_lhs => rw [← hψ₁X]
    exact polarImage_symm_polarImage h hB hBl hψ₁' hXs
  have hle₂ : ∀ H : Submodule K (Fin r → K),
      polarImage (hypForm h r ε) ψ₁'.symm (H.map (hypXEmb r ε)) ≤ hypX K r ε := fun H => by
    rw [← hψ₁sX]
    exact (polarImage_le_iff h hB hBl hψ₁'' (hHs H) hXs).2 LinearMap.map_le_range
  let hyp : ProjectiveGeometry.Hyperplane r K ≃ ProjectiveGeometry.Hyperplane r K :=
    { toFun := fun H => ⟨(polarImage (hypForm h r ε) ψ₁' (H.1.map (hypXEmb r ε))).comap
          (hypXEmb r ε), by
        rw [finrank_comap_hypXEmb (hle₁ H.1), finrank_polarImage h hB hBl hψ₁' (hHs H.1),
          finrank_map_hypXEmb]
        exact H.2⟩
      invFun := fun H => ⟨(polarImage (hypForm h r ε) ψ₁'.symm (H.1.map (hypXEmb r ε))).comap
          (hypXEmb r ε), by
        rw [finrank_comap_hypXEmb (hle₂ H.1), finrank_polarImage h hB hBl hψ₁'' (hHs H.1),
          finrank_map_hypXEmb]
        exact H.2⟩
      left_inv := fun H => Subtype.ext (by
        change (polarImage (hypForm h r ε) ψ₁'.symm (((polarImage (hypForm h r ε) ψ₁'
          (H.1.map (hypXEmb r ε))).comap (hypXEmb r ε)).map (hypXEmb r ε))).comap
          (hypXEmb r ε) = H.1
        rw [map_comap_hypXEmb (hle₁ H.1), polarImage_symm_polarImage h hB hBl hψ₁' (hHs H.1),
          comap_map_hypXEmb])
      right_inv := fun H => Subtype.ext (by
        change (polarImage (hypForm h r ε) ψ₁' (((polarImage (hypForm h r ε) ψ₁'.symm
          (H.1.map (hypXEmb r ε))).comap (hypXEmb r ε)).map (hypXEmb r ε))).comap
          (hypXEmb r ε) = H.1
        have h3 := polarImage_symm_polarImage h hB hBl hψ₁'' (hHs H.1)
        rw [Equiv.symm_symm] at h3
        rw [map_comap_hypXEmb (hle₂ H.1), h3, comap_map_hypXEmb]) }
  have hinc : ∀ (L' : ProjectiveGeometry.Point r K) (H : ProjectiveGeometry.Hyperplane r K),
      (L' : Submodule K (Fin r → K)) ≤ H ↔ (fP L' : Submodule K (Fin r → K)) ≤ hyp H := by
    intro L' H
    have hpt : (ψ₁ (hypXPoint h L') : Submodule K (HypIndex r ε → K)) =
        polarImage (hypForm h r ε) ψ₁'
          (hypXPoint (ε := ε) h L' : Submodule K (HypIndex r ε → K)) := by
      rw [← hψ₁'L]
      exact (polarImage_point ψ₁' (hypXPoint h L')).symm
    change L'.1 ≤ H.1 ↔ (ψ₁ (hypXPoint h L') : Submodule K (HypIndex r ε → K)).comap
        (hypXEmb r ε) ≤ (polarImage (hypForm h r ε) ψ₁' (H.1.map (hypXEmb r ε))).comap
        (hypXEmb r ε)
    rw [comap_le_comap_hypXEmb_iff (hfwd L') (hle₁ H.1), hpt,
      polarImage_le_iff h hB hBl hψ₁'
        (isTotIso_of_mem_isoLines (B := hypForm h r ε) (hypXPoint h L').2) (hHs H.1),
      coe_hypXPoint, Submodule.map_le_map_iff_of_injective hypXEmb_injective]
  obtain ⟨A₀, σ, hfA, -⟩ := ProjectiveGeometry.semilinear_realization hr fP hyp hinc
  have hT₁J := hypLevi_isometry (ε := ε) h A₀
  obtain ⟨x₁, hx₁⟩ : ∃ x₁ : semilinearSimilitudes h r ε,
      (x₁ : SemiGL (HypIndex r ε) K) = ⟨glOfLinearEquiv (hypLeviEquiv (ε := ε) h A₀), σ⟩ :=
    ⟨⟨⟨glOfLinearEquiv (hypLeviEquiv (ε := ε) h A₀), σ⟩, 1, one_ne_zero, map_one _, by
      rw [one_smul]
      exact hT₁J⟩, rfl⟩
  have hψ₁T₁ : ∀ L : hypIsotropicLines h r ε,
      (L : Submodule K (HypIndex r ε → K)) ≤ hypX K r ε →
      ψ₁ L = semilinearPointAction h r ε x₁ L := by
    intro L hL
    have h1 := hfA (hypToKPoint h L hL)
    change (ψ₁ (hypXPoint h (hypToKPoint h L hL)) : Submodule K (HypIndex r ε → K)).comap
      (hypXEmb r ε) = _ at h1
    rw [hypXPoint_hypToKPoint] at h1
    apply Subtype.ext
    change (ψ₁ L : Submodule K (HypIndex r ε → K)) =
      (x₁ : SemiGL (HypIndex r ε) K) • (L : Submodule K (HypIndex r ε → K))
    rw [← map_comap_hypXEmb (hmapX L hL), h1, hx₁, ← levi_smul_map_hypXEmb h A₀ σ,
      coe_hypToKPoint, map_comap_hypXEmb hL]
  obtain ⟨ψ₂, hψ₂def⟩ : ∃ ψ₂ : Equiv.Perm (hypIsotropicLines h r ε),
      ψ₂ = (semilinearPointAction h r ε x₁)⁻¹ * ψ₁ := ⟨_, rfl⟩
  have hψ₂ : ∀ L M, LineOrth h L M ↔ LineOrth h (ψ₂ L) (ψ₂ M) := by
    rw [hψ₂def]
    exact hcomp x₁ ψ₁ hψ₁
  have hψ₂X : ∀ L : hypIsotropicLines h r ε,
      (L : Submodule K (HypIndex r ε → K)) ≤ hypX K r ε → ψ₂ L = L := by
    intro L hL
    rw [hψ₂def, Equiv.Perm.mul_apply, hψ₁T₁ L hL, Equiv.Perm.inv_eq_iff_eq]
  have hx₁Y : ((x₁⁻¹ : semilinearSimilitudes h r ε) : SemiGL (HypIndex r ε) K) • hypY K r ε =
      hypY K r ε := by
    rw [InvMemClass.coe_inv, hx₁]
    conv_lhs => rw [← levi_smul_hypY (ε := ε) h A₀ σ]
    exact inv_smul_smul _ _
  have hψ₂Y : ∀ L : hypIsotropicLines h r ε,
      (L : Submodule K (HypIndex r ε → K)) ≤ hypY K r ε →
      (ψ₂ L : Submodule K (HypIndex r ε → K)) ≤ hypY K r ε := by
    intro L hL
    have h3 : (ψ₂ L : Submodule K (HypIndex r ε → K)) =
        ((x₁⁻¹ : semilinearSimilitudes h r ε) : SemiGL (HypIndex r ε) K) •
          (ψ₁ L : Submodule K (HypIndex r ε → K)) := by
      rw [hψ₂def, Equiv.Perm.mul_apply, ← map_inv]
      rfl
    rw [h3, ← hx₁Y, semiGL_smul_eq_map, semiGL_smul_eq_map]
    exact Submodule.map_mono (hmapY L hL)
  refine ⟨x₀ * x₁, ?_, fun L hL => ?_⟩
  · have hl : ((x₀ * x₁ : semilinearSimilitudes h r ε) : SemiGL (HypIndex r ε) K).left =
        T₀ * glOfLinearEquiv (hypLeviEquiv (ε := ε) h A₀) := by
      rw [Subgroup.coe_mul, hx₀, hx₁, SemidirectProduct.mul_left]
      change T₀ * glAut (1 : K ≃+* K) (glOfLinearEquiv (hypLeviEquiv (ε := ε) h A₀)) = _
      rw [map_one, MulAut.one_apply]
    rw [hl, Units.val_mul, conjTranspose_mul_mul, hT₀J, hT₁J]
  · have hfix : ψ₂ L = L := hL.elim (hψ₂X L) fun hLY =>
      eq_of_le_hypY h ψ₂ hψ₂ hψ₂X hLY (hψ₂Y L hLY)
    have h1 : ψ₁ L = semilinearPointAction h r ε x₁ L := by
      rw [hψ₂def, Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq] at hfix
      exact hfix
    rw [map_mul, Equiv.Perm.mul_apply, ← h1, hψ₁def, Equiv.Perm.mul_apply, Equiv.Perm.coe_inv,
      Equiv.apply_symm_apply]

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
