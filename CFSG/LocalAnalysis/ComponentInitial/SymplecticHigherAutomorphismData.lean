module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherParabolicData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldAction

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

open Matrix CFSG.Assembly.LowTwoRank SymplecticFlag
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldEquiv glFieldAut
  glFieldEquiv_scalar)

section Generic

variable {M G : Type*} [Group M] [Group G]

@[expose] def restrictAutHom (φ : M →* MulAut G) (H : Subgroup G)
    (hH : ∀ m, ∀ g ∈ H, φ m g ∈ H) : M →* MulAut H where
  toFun m :=
    { toFun := fun g => ⟨φ m (g : G), hH m (g : G) g.2⟩
      invFun := fun g => ⟨φ m⁻¹ (g : G), hH m⁻¹ (g : G) g.2⟩
      left_inv := fun g => Subtype.ext <| by
        change φ m⁻¹ (φ m (g : G)) = g
        rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
      right_inv := fun g => Subtype.ext <| by
        change φ m (φ m⁻¹ (g : G)) = g
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
      map_mul' := fun g h => Subtype.ext (map_mul (φ m) (g : G) h) }
  map_one' := by
    ext g
    change φ 1 (g : G) = g
    rw [map_one, MulAut.one_apply]
  map_mul' a b := by
    ext g
    change φ (a * b) (g : G) = φ a (φ b g)
    rw [map_mul, MulAut.mul_apply]

theorem restrictAutHom_apply (φ : M →* MulAut G) (H : Subgroup G)
    (hH : ∀ m, ∀ g ∈ H, φ m g ∈ H) (m : M) (g : H) :
    ((restrictAutHom φ H hH m g : H) : G) = φ m (g : G) :=
  rfl

theorem map_eq_of_forall_mem (φ : M →* MulAut G) (N : Subgroup G)
    (hN : ∀ m, ∀ g ∈ N, φ m g ∈ N) (m : M) : N.map (φ m : G →* G) = N := by
  refine le_antisymm ?_ fun g hg => ⟨φ m⁻¹ g, hN _ _ hg, ?_⟩
  · rintro _ ⟨g, hg, rfl⟩
    exact hN m g hg
  · change φ m (φ m⁻¹ g) = g
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

@[expose] def quotientAutHom (φ : M →* MulAut G) (N : Subgroup G) [N.Normal]
    (hN : ∀ m, ∀ g ∈ N, φ m g ∈ N) : M →* MulAut (G ⧸ N) where
  toFun m := QuotientGroup.congr N N (φ m) (map_eq_of_forall_mem φ N hN m)
  map_one' := by
    ext x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    change ((φ 1 g : G) : G ⧸ N) = g
    rw [map_one, MulAut.one_apply]
  map_mul' a b := by
    ext x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    change ((φ (a * b) g : G) : G ⧸ N) = ((φ a (φ b g) : G) : G ⧸ N)
    rw [map_mul, MulAut.mul_apply]

theorem quotientAutHom_mk (φ : M →* MulAut G) (N : Subgroup G) [N.Normal]
    (hN : ∀ m, ∀ g ∈ N, φ m g ∈ N) (m : M) (g : G) :
    quotientAutHom φ N hN m (g : G ⧸ N) = ((φ m g : G) : G ⧸ N) :=
  rfl

end Generic

variable (r : ℕ) (K : Type) [Field K]

abbrev formJ : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K := fromBlocks 0 1 (-1) 0

variable {r K}

theorem inv_transpose_formJ {A : GL (Fin r ⊕ Fin r) K} {μ : Kˣ}
    (hA : (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ * formJ r K * A =
      (μ : K) • formJ r K) :
    ((A⁻¹ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ * formJ r K *
      ((A⁻¹ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      ((μ⁻¹ : Kˣ) : K) • formJ r K := by
  set B := ((A⁻¹ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
  set a := (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
  have hAB : a * B = 1 := A.mul_inv
  have hJ : formJ r K = ((μ⁻¹ : Kˣ) : K) • (aᵀ * formJ r K * a) := by
    rw [hA, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  calc Bᵀ * formJ r K * B = Bᵀ * (((μ⁻¹ : Kˣ) : K) • (aᵀ * formJ r K * a)) * B := by
        rw [← hJ]
    _ = ((μ⁻¹ : Kˣ) : K) • ((a * B)ᵀ * formJ r K * (a * B)) := by
        rw [transpose_mul, Matrix.mul_smul, Matrix.smul_mul]
        simp only [Matrix.mul_assoc]
    _ = ((μ⁻¹ : Kˣ) : K) • formJ r K := by
        rw [hAB, transpose_one, Matrix.one_mul, Matrix.mul_one]

theorem mul_transpose_formJ_mul {a : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} {μ : K}
    (ha : aᵀ * formJ r K * a = μ • formJ r K) (b : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) :
    (a * b)ᵀ * formJ r K * (a * b) = μ • (bᵀ * formJ r K * b) := by
  rw [transpose_mul]
  calc bᵀ * aᵀ * formJ r K * (a * b) = bᵀ * (aᵀ * formJ r K * a) * b := by
        simp only [Matrix.mul_assoc]
    _ = μ • (bᵀ * formJ r K * b) := by rw [ha, Matrix.mul_smul, Matrix.smul_mul]

variable (r K)

@[expose] def gsp : Subgroup (GL (Fin r ⊕ Fin r) K) where
  carrier := {A | ∃ μ : Kˣ, (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ * formJ r K * A =
    (μ : K) • formJ r K}
  mul_mem' := by
    rintro A B ⟨μ, hA⟩ ⟨ν, hB⟩
    exact ⟨μ * ν, by rw [Units.val_mul, mul_transpose_formJ_mul hA, hB, Units.val_mul, smul_smul]⟩
  one_mem' := ⟨1, by simp⟩
  inv_mem' := by
    rintro A ⟨μ, hA⟩
    exact ⟨μ⁻¹, inv_transpose_formJ hA⟩

variable {r K}

theorem mem_gsp {A : GL (Fin r ⊕ Fin r) K} :
    A ∈ gsp r K ↔ ∃ μ : Kˣ, (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ * formJ r K * A =
      (μ : K) • formJ r K :=
  Iff.rfl

theorem statedSp_le_gsp : StatedSp r K ≤ gsp r K := fun g hg =>
  ⟨1, by rw [Units.val_one, one_smul]; exact SymplecticTorusWeyl.mem_statedSp_iff.mp hg⟩

theorem smul_formJ_injective (r : ℕ) [NeZero r] {μ ν : K}
    (h : μ • formJ r K = ν • formJ r K) : μ = ν := by
  have := congrFun (congrFun h (Sum.inl 0)) (Sum.inr 0)
  simpa [formJ] using this

@[expose] def multiplierUnit (A : gsp r K) : Kˣ :=
  Classical.choose (mem_gsp.mp A.2)

theorem multiplierUnit_spec (A : gsp r K) :
    ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ * formJ r K *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      (multiplierUnit A : K) • formJ r K :=
  Classical.choose_spec (mem_gsp.mp A.2)

theorem multiplierUnit_eq [NeZero r] (A : gsp r K) {μ : Kˣ}
    (h : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ * formJ r K *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      (μ : K) • formJ r K) : multiplierUnit A = μ :=
  Units.ext <| smul_formJ_injective r <| by rw [← multiplierUnit_spec, h]

variable (r K)

@[expose] def multiplier [NeZero r] : gsp r K →* Kˣ where
  toFun := multiplierUnit
  map_one' := multiplierUnit_eq 1 (by simp)
  map_mul' A B := multiplierUnit_eq (A * B) (by
    rw [Subgroup.coe_mul, Units.val_mul, mul_transpose_formJ_mul (multiplierUnit_spec A),
      multiplierUnit_spec B, Units.val_mul, smul_smul])

variable {r K}

theorem multiplier_spec [NeZero r] (A : gsp r K) :
    ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ * formJ r K *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      (multiplier r K A : K) • formJ r K :=
  multiplierUnit_spec A

theorem multiplier_eq [NeZero r] (A : gsp r K) {μ : Kˣ}
    (h : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ * formJ r K *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      (μ : K) • formJ r K) : multiplier r K A = μ :=
  multiplierUnit_eq A h

theorem ker_multiplier [NeZero r] :
    (multiplier r K).ker = (StatedSp r K).subgroupOf (gsp r K) := by
  ext A
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, SymplecticTorusWeyl.mem_statedSp_iff]
  constructor
  · intro h
    rw [multiplier_spec, h, Units.val_one, one_smul]
  · intro h
    exact multiplier_eq A (by rw [h, Units.val_one, one_smul])

theorem conj_mem_statedSp {A : GL (Fin r ⊕ Fin r) K} (hA : A ∈ gsp r K)
    {g : GL (Fin r ⊕ Fin r) K} (hg : g ∈ StatedSp r K) : A * g * A⁻¹ ∈ StatedSp r K := by
  obtain ⟨μ, hA⟩ := hA
  have hB := inv_transpose_formJ hA
  have hg' := SymplecticTorusWeyl.mem_statedSp_iff.mp hg
  rw [SymplecticTorusWeyl.mem_statedSp_iff]
  set B := ((A⁻¹ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
  set a := (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
  set G := (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
  rw [Units.val_mul, Units.val_mul]
  calc (a * G * B)ᵀ * formJ r K * (a * G * B) = Bᵀ * (Gᵀ * (aᵀ * formJ r K * a) * G) * B := by
        simp only [transpose_mul, Matrix.mul_assoc]
    _ = (μ : K) • (Bᵀ * (Gᵀ * formJ r K * G) * B) := by
        rw [hA, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul]
    _ = (μ : K) • (((μ⁻¹ : Kˣ) : K) • formJ r K) := by rw [hg', hB]
    _ = formJ r K := by rw [smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]

theorem formJ_map (σ : K ≃+* K) : (formJ r K).map σ = formJ r K := by
  rw [formJ, fromBlocks_map]
  congr 1
  · exact Matrix.map_zero _ (map_zero σ)
  · exact Matrix.map_one _ (map_zero σ) (map_one σ)
  · rw [Matrix.map_neg _ (map_neg σ), Matrix.map_one _ (map_zero σ) (map_one σ)]
  · exact Matrix.map_zero _ (map_zero σ)

theorem map_mul_ringEquiv {ι : Type*} [Fintype ι] (σ : K ≃+* K) (M N : Matrix ι ι K) :
    (M * N).map σ = M.map σ * N.map σ :=
  Matrix.map_mul (f := σ.toRingHom)

theorem fieldEquiv_mem_statedSp (σ : K ≃+* K) {g : GL (Fin r ⊕ Fin r) K}
    (hg : g ∈ StatedSp r K) : glFieldEquiv (Fin r ⊕ Fin r) σ g ∈ StatedSp r K := by
  have hg' : (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ * formJ r K * g = formJ r K :=
    SymplecticTorusWeyl.mem_statedSp_iff.mp hg
  rw [SymplecticTorusWeyl.mem_statedSp_iff]
  change ((g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).map σ)ᵀ * formJ r K *
      (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).map σ = formJ r K
  calc ((g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).map σ)ᵀ * formJ r K *
        (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).map σ =
        ((g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ * formJ r K * g).map σ := by
        rw [map_mul_ringEquiv, map_mul_ringEquiv, transpose_map, formJ_map]
    _ = formJ r K := by rw [hg', formJ_map]

variable (r K)

@[expose] def conjSp : gsp r K →* MulAut (StatedSp r K) :=
  restrictAutHom ((MulAut.conj).comp (gsp r K).subtype) (StatedSp r K)
    fun A _ hg => conj_mem_statedSp A.2 hg

@[expose] def fieldSp : (K ≃+* K) →* MulAut (StatedSp r K) :=
  restrictAutHom (glFieldAut (Fin r ⊕ Fin r) K) (StatedSp r K) fun σ _ hg =>
    fieldEquiv_mem_statedSp σ hg

variable {r K}

theorem coe_conjSp (A : gsp r K) (g : StatedSp r K) :
    ((conjSp r K A g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) =
      (A : GL (Fin r ⊕ Fin r) K) * g * (A : GL (Fin r ⊕ Fin r) K)⁻¹ :=
  rfl

theorem coe_fieldSp (σ : K ≃+* K) (g : StatedSp r K) :
    (((fieldSp r K σ g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).map σ :=
  rfl

theorem conjSp_mem_spScalars (A : gsp r K) {z : StatedSp r K} (hz : z ∈ spScalars r K) :
    conjSp r K A z ∈ spScalars r K := by
  have hz' := hz
  rw [Subgroup.mem_subgroupOf, StatedScalars,
    ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz'
  have hcomm := Subgroup.mem_center_iff.mp hz' (A : GL (Fin r ⊕ Fin r) K)
  have hfix : conjSp r K A z = z :=
    Subtype.ext (by rw [coe_conjSp, hcomm, mul_inv_cancel_right])
  rw [hfix]
  exact hz

theorem fieldSp_mem_spScalars (σ : K ≃+* K) {z : StatedSp r K} (hz : z ∈ spScalars r K) :
    fieldSp r K σ z ∈ spScalars r K := by
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hz ⊢
  obtain ⟨c, hc⟩ := hz
  refine ⟨Units.map σ.toRingHom.toMonoidHom c, ?_⟩
  change _ = glFieldEquiv (Fin r ⊕ Fin r) σ (z : GL (Fin r ⊕ Fin r) K)
  rw [← hc, glFieldEquiv_scalar]

variable (r K)

@[expose] def conjAut : gsp r K →* MulAut (StatedProj (StatedSp r K)) :=
  quotientAutHom (conjSp r K) (spScalars r K) fun A _ hz => conjSp_mem_spScalars A hz

@[expose] def fieldAut : (K ≃+* K) →* MulAut (StatedProj (StatedSp r K)) :=
  quotientAutHom (fieldSp r K) (spScalars r K) fun σ _ hz => fieldSp_mem_spScalars σ hz

@[expose] def spLinearAutGroup : Subgroup (MulAut (StatedProj (StatedSp r K))) :=
  Subgroup.closure (Set.range (conjAut r K))

@[expose] def spSemilinearAutGroup : Subgroup (MulAut (StatedProj (StatedSp r K))) :=
  Subgroup.closure ((spLinearAutGroup r K : Set (MulAut (StatedProj (StatedSp r K)))) ∪
    Set.range (fieldAut r K))

variable {r K}

theorem conjAut_proj (A : gsp r K) (g : StatedSp r K) :
    conjAut r K A (proj r K g) = proj r K (conjSp r K A g) :=
  rfl

theorem fieldAut_proj (σ : K ≃+* K) (g : StatedSp r K) :
    fieldAut r K σ (proj r K g) = proj r K (fieldSp r K σ g) :=
  rfl

theorem conjAut_mem_spLinearAutGroup (A : gsp r K) : conjAut r K A ∈ spLinearAutGroup r K :=
  Subgroup.subset_closure ⟨A, rfl⟩

theorem spLinearAutGroup_le_spSemilinearAutGroup :
    spLinearAutGroup r K ≤ spSemilinearAutGroup r K :=
  fun _ h => Subgroup.subset_closure (Or.inl h)

theorem fieldAut_mem_spSemilinearAutGroup (σ : K ≃+* K) :
    fieldAut r K σ ∈ spSemilinearAutGroup r K :=
  Subgroup.subset_closure (Or.inr ⟨σ, rfl⟩)

theorem standard_automorphism_data [NeZero r] :
    StatedSp r K ≤ gsp r K ∧
    (∀ (A : gsp r K) (μ : Kˣ),
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ * formJ r K *
        ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
        (μ : K) • formJ r K ↔ multiplier r K A = μ) ∧
    (multiplier r K).ker = (StatedSp r K).subgroupOf (gsp r K) ∧
    (∀ (A : gsp r K) (g : StatedSp r K), conjAut r K A (proj r K g) =
      proj r K ⟨(A : GL (Fin r ⊕ Fin r) K) * g * (A : GL (Fin r ⊕ Fin r) K)⁻¹,
        conj_mem_statedSp A.2 g.2⟩) ∧
    (∀ (σ : K ≃+* K) (g : StatedSp r K), fieldAut r K σ (proj r K g) =
      proj r K ⟨glFieldEquiv (Fin r ⊕ Fin r) σ g, fieldEquiv_mem_statedSp σ g.2⟩) ∧
    (∀ A : gsp r K, (conjAut r K A)⁻¹ = conjAut r K A⁻¹) ∧
    (∀ σ : K ≃+* K, (fieldAut r K σ)⁻¹ = fieldAut r K σ⁻¹) ∧
    spLinearAutGroup r K ≤ spSemilinearAutGroup r K :=
  ⟨statedSp_le_gsp, fun A _ => ⟨multiplier_eq A, fun h => h ▸ multiplier_spec A⟩,
    ker_multiplier, fun _ _ => rfl, fun _ _ => rfl, fun A => (map_inv _ A).symm,
    fun σ => (map_inv _ σ).symm, spLinearAutGroup_le_spSemilinearAutGroup⟩

end CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
