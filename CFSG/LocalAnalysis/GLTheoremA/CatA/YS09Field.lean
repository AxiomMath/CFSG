module

public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsU
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaModelMinus

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Assembly
open scoped MatrixGroups Matrix

namespace YS09Field

abbrev ClosedCont (Q : LargeEvenRawCont) : LargeEvenRawCont :=
  fun R _ I F => Q R I F ∧ ∀ f ∈ F, ∀ n : ℕ, 0 < n → f ^ n ∈ F

theorem closure_stable {G : Type*} [Group G] (S : Set G) (φ : G →* G)
    (hS : ∀ s ∈ S, φ s ∈ Subgroup.closure S) {g : G} (hg : g ∈ Subgroup.closure S) :
    φ g ∈ Subgroup.closure S := by
  have h : (Subgroup.closure S).map φ ≤ Subgroup.closure S := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨s, hs, rfl⟩
    exact hS s hs
  exact h ⟨g, hg, rfl⟩

theorem derived_stable {G : Type*} [Group G] (H : Subgroup G) (φ : G →* G)
    (hH : ∀ h ∈ H, φ h ∈ H) {g : G} (hg : g ∈ ⁅H, H⁆) : φ g ∈ ⁅H, H⁆ := by
  have hle : H.map φ ≤ H := by
    rintro _ ⟨h, hh, rfl⟩
    exact hH h hh
  have h : (⁅H, H⁆ : Subgroup G).map φ ≤ ⁅H, H⁆ := by
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono hle hle
  exact h ⟨g, hg, rfl⟩

theorem graph_pow {M R S : Type*} [Group M] [Group R] [Group S] (H : Subgroup M) (π : H →* R)
    (act : S → M → M) (hact1 : ∀ x, act 1 x = x)
    (hactmul : ∀ a b x, act (a * b) x = act a (act b x))
    (hstab : ∀ a (h : H), act a h ∈ H) (rel : S → H → H → Prop)
    (hrel : ∀ a h h', rel a h h' ↔ (h' : M) = act a h) (a : S) (f : MulAut R)
    (hf : LargeEvenGraphAut π (rel a) f) (n : ℕ) :
    LargeEvenGraphAut π (rel (a ^ n)) (f ^ n) := by
  suffices H' : ∀ n : ℕ, ∀ h h' : H, (h' : M) = act (a ^ n) h → (f ^ n) (π h) = π h' from
    fun h h' hh => H' n h h' ((hrel _ _ _).1 hh)
  intro n
  induction n with
  | zero =>
    intro h h' hh'
    rw [pow_zero, hact1] at hh'
    have e : h' = h := Subtype.ext hh'
    subst e
    rw [pow_zero, MulAut.one_apply]
  | succ n ih =>
    intro h h' hh'
    let h1 : H := ⟨act (a ^ n) h, hstab _ h⟩
    let h2 : H := ⟨act a (act (a ^ n) h), hstab _ h1⟩
    have e1 : (f ^ n) (π h) = π h1 := ih h h1 rfl
    have e2 : f (π h1) = π h2 := hf h1 h2 ((hrel a h1 h2).2 rfl)
    have e3 : h' = h2 := Subtype.ext (by
      show (h' : M) = act a (act (a ^ n) h)
      rw [hh', pow_succ', hactmul])
    rw [pow_succ', MulAut.mul_apply, e1, e2, e3]

theorem coe_glMap {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] (τ : K →+* K) (g : GL ι K) :
    ((Matrix.GeneralLinearGroup.map τ g : GL ι K) : Matrix ι ι K) = (g : Matrix ι ι K).map τ :=
  rfl

theorem glMap_one {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] (g : GL ι K) :
    Matrix.GeneralLinearGroup.map (1 : K ≃+* K).toRingHom g = g := by
  rw [show (1 : K ≃+* K).toRingHom = RingHom.id K from rfl, Matrix.GeneralLinearGroup.map_id]
  rfl

theorem glMap_mul {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] (σ τ : K ≃+* K) (g : GL ι K) :
    Matrix.GeneralLinearGroup.map (σ * τ).toRingHom g =
      Matrix.GeneralLinearGroup.map σ.toRingHom (Matrix.GeneralLinearGroup.map τ.toRingHom g) := by
  rw [show (σ * τ).toRingHom = σ.toRingHom.comp τ.toRingHom from rfl,
    Matrix.GeneralLinearGroup.map_comp]
  rfl

theorem matField_pow_closed {ι K R : Type} [Fintype ι] [DecidableEq ι] [Field K] [Group R]
    (H : Subgroup (GL ι K))
    (hH : ∀ σ : K ≃+* K, ∀ h ∈ H, Matrix.GeneralLinearGroup.map σ.toRingHom h ∈ H)
    (π : H →* R) (f : MulAut R) (hf : f ∈ LargeEvenMatFieldImage π) (n : ℕ) :
    f ^ n ∈ LargeEvenMatFieldImage π := by
  obtain ⟨σ, hσ⟩ := hf
  exact ⟨σ ^ n, graph_pow (S := K ≃+* K) H π
    (fun τ g => Matrix.GeneralLinearGroup.map τ.toRingHom g) glMap_one glMap_mul
    (fun τ h => hH τ h h.2)
    (fun τ h h' => ((h' : GL ι K) : Matrix ι ι K) = ((h : GL ι K) : Matrix ι ι K).map τ.toRingHom)
    (fun τ h h' => by rw [Units.ext_iff, coe_glMap]) σ f hσ n⟩

theorem mem_LargeEvenSL_iff {d : ℕ} {K : Type} [Field K] (h : GL (Fin d) K) :
    h ∈ LargeEvenSLGroup (Fin d) K ↔ (h : Matrix (Fin d) (Fin d) K).det = 1 := by
  unfold LargeEvenSLGroup
  rw [MonoidHom.mem_ker, Units.ext_iff, Matrix.GeneralLinearGroup.val_det_apply]
  rfl

theorem sl_map_mem {d : ℕ} {K : Type} [Field K] (σ : K ≃+* K) (h : GL (Fin d) K)
    (hh : h ∈ LargeEvenSLGroup (Fin d) K) :
    Matrix.GeneralLinearGroup.map σ.toRingHom h ∈ LargeEvenSLGroup (Fin d) K := by
  rw [mem_LargeEvenSL_iff] at hh ⊢
  rw [coe_glMap]
  calc ((h : Matrix (Fin d) (Fin d) K).map σ).det = σ ((h : Matrix (Fin d) (Fin d) K).det) :=
        (RingHom.map_det σ.toRingHom _).symm
    _ = 1 := by rw [hh, map_one]

theorem su_map_mem {d q : ℕ} {K : Type} [Field K] (σ : K ≃+* K) (h : GL (Fin d) K)
    (hh : h ∈ LargeEvenSUGroup (Fin d) K q) :
    Matrix.GeneralLinearGroup.map σ.toRingHom h ∈ LargeEvenSUGroup (Fin d) K q := by
  unfold LargeEvenSUGroup at hh ⊢
  refine closure_stable {A : GL (Fin d) K | (A : Matrix (Fin d) (Fin d) K).det = 1 ∧
      ((A : Matrix (Fin d) (Fin d) K).map (· ^ q))ᵀ * (A : Matrix (Fin d) (Fin d) K) = 1}
    (Matrix.GeneralLinearGroup.map σ.toRingHom) (fun s hs => Subgroup.subset_closure ?_) hh
  obtain ⟨h1, h2⟩ := hs
  simp only [Set.mem_setOf_eq, coe_glMap]
  refine ⟨?_, ?_⟩
  · calc ((s : Matrix (Fin d) (Fin d) K).map σ).det = σ ((s : Matrix (Fin d) (Fin d) K).det) :=
          (RingHom.map_det σ.toRingHom _).symm
      _ = 1 := by rw [h1, map_one]
  · have hq : ((s : Matrix (Fin d) (Fin d) K).map σ.toRingHom).map (· ^ q) =
        ((s : Matrix (Fin d) (Fin d) K).map (· ^ q)).map σ.toRingHom := by
      rw [Matrix.map_map, Matrix.map_map]
      congr 1
      funext x
      simp [map_pow]
    rw [hq, ← Matrix.transpose_map, ← Matrix.map_mul, h2,
      Matrix.map_one _ (map_zero σ.toRingHom) (map_one σ.toRingHom)]

theorem gram_map_mem {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] (σ : K ≃+* K)
    (J : Matrix ι ι K) (hJ : J.map σ.toRingHom = J) (h : GL ι K)
    (hh : h ∈ CFSG.MatrixModel.gramCore J) :
    Matrix.GeneralLinearGroup.map σ.toRingHom h ∈ CFSG.MatrixModel.gramCore J := by
  unfold CFSG.MatrixModel.gramCore at hh ⊢
  refine closure_stable {A : GL ι K | (A : Matrix ι ι K)ᵀ * J * (A : Matrix ι ι K) = J}
    (Matrix.GeneralLinearGroup.map σ.toRingHom) (fun s hs => Subgroup.subset_closure ?_) hh
  have key : ∀ A B : Matrix ι ι K,
      A.map σ.toRingHom * J * B.map σ.toRingHom = (A * J * B).map σ.toRingHom := by
    intro A B
    rw [Matrix.map_mul, Matrix.map_mul, hJ]
  show ((Matrix.GeneralLinearGroup.map σ.toRingHom s : GL ι K) : Matrix ι ι K)ᵀ * J *
    ((Matrix.GeneralLinearGroup.map σ.toRingHom s : GL ι K) : Matrix ι ι K) = J
  rw [coe_glMap, ← Matrix.transpose_map, key, hs, hJ]

theorem sp_map_mem {m : ℕ} {K : Type} [Field K] (σ : K ≃+* K) (h : GL (Fin m ⊕ Fin m) K)
    (hh : h ∈ LargeEvenSpGroup K m) :
    Matrix.GeneralLinearGroup.map σ.toRingHom h ∈ LargeEvenSpGroup K m := by
  refine gram_map_mem σ (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) K) 1 (-1) 0) ?_ h hh
  rw [Matrix.fromBlocks_map]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.fromBlocks, Matrix.one_apply]

theorem quadPlus_map {m : ℕ} {K : Type} [Field K] (σ : K ≃+* K) (x : Fin m ⊕ Fin m → K) :
    CFSG.Open.StatedQuadPlus m K (fun i => σ (x i)) = σ (CFSG.Open.StatedQuadPlus m K x) := by
  simp [CFSG.Open.StatedQuadPlus, CFSG.MatrixModel.plusQuadCore, map_sum, map_mul]

theorem isometry_map_mem {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] (σ : K ≃+* K)
    (Q : (ι → K) → K) (hQ : ∀ x : ι → K, Q (fun i => σ (x i)) = σ (Q x)) (h : GL ι K)
    (hh : ∀ v : ι → K, Q ((h : Matrix ι ι K) *ᵥ v) = Q v) :
    ∀ v : ι → K, Q (((Matrix.GeneralLinearGroup.map σ.toRingHom h : GL ι K) : Matrix ι ι K) *ᵥ v) =
      Q v := by
  intro v
  obtain ⟨w, rfl⟩ : ∃ w : ι → K, v = fun i => σ (w i) :=
    ⟨fun i => σ.symm (v i), funext fun i => (σ.apply_symm_apply _).symm⟩
  have e : ((h : Matrix ι ι K).map σ.toRingHom) *ᵥ (fun i => σ (w i)) =
      fun i => σ (((h : Matrix ι ι K) *ᵥ w) i) := by
    funext i
    exact (RingHom.map_mulVec σ.toRingHom (h : Matrix ι ι K) w i).symm
  rw [coe_glMap, e, hQ, hh w, hQ]

theorem omegaPlus_map_mem {m : ℕ} {K : Type} [Field K] (σ : K ≃+* K) (h : GL (Fin m ⊕ Fin m) K)
    (hh : h ∈ LargeEvenOmega (LargeEvenQPlus K m)) :
    Matrix.GeneralLinearGroup.map σ.toRingHom h ∈ LargeEvenOmega (LargeEvenQPlus K m) := by
  have hC : ∀ g ∈ CFSG.MatrixModel.isometryCore (CFSG.Open.StatedQuadPlus m K),
      Matrix.GeneralLinearGroup.map σ.toRingHom g ∈
        CFSG.MatrixModel.isometryCore (CFSG.Open.StatedQuadPlus m K) := by
    intro g hg
    unfold CFSG.MatrixModel.isometryCore at hg ⊢
    refine closure_stable {A : GL (Fin m ⊕ Fin m) K | ∀ v : Fin m ⊕ Fin m → K,
        CFSG.Open.StatedQuadPlus m K (Matrix.mulVec (A : Matrix _ _ K) v) =
          CFSG.Open.StatedQuadPlus m K v}
      (Matrix.GeneralLinearGroup.map σ.toRingHom) (fun s hs => Subgroup.subset_closure ?_) hg
    exact isometry_map_mem σ _ (quadPlus_map σ) s hs
  exact derived_stable _ _ hC hh

theorem szGens_map {a : ℕ} {K : Type} [Field K] (σ : K ≃+* K) {M : Matrix (Fin 4) (Fin 4) K}
    (hM : M ∈ LargeEvenSzGens a K) : M.map σ ∈ LargeEvenSzGens a K := by
  rcases hM with ⟨u, v, rfl⟩ | ⟨l, rfl⟩ | rfl
  · refine Or.inl ⟨σ u, σ v, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [map_add, map_mul, map_pow]
  · refine Or.inr (Or.inl ⟨Units.map σ.toMonoidHom l, ?_⟩)
    rw [Matrix.diagonal_map (map_zero σ)]
    congr 1
    funext i
    fin_cases i <;> simp [map_pow, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
  · refine Or.inr (Or.inr ?_)
    ext i j
    fin_cases i <;> fin_cases j <;> simp

theorem sz_map_mem {a : ℕ} {K : Type} [Field K] (σ : K ≃+* K) (h : GL (Fin 4) K)
    (hh : h ∈ LargeEvenSzGroup a K) :
    Matrix.GeneralLinearGroup.map σ.toRingHom h ∈ LargeEvenSzGroup a K := by
  unfold LargeEvenSzGroup at hh ⊢
  refine closure_stable {g : GL (Fin 4) K | (g : Matrix (Fin 4) (Fin 4) K) ∈ LargeEvenSzGens a K}
    (Matrix.GeneralLinearGroup.map σ.toRingHom) (fun s hs => Subgroup.subset_closure ?_) hh
  rw [Set.mem_setOf_eq, coe_glMap]
  exact szGens_map σ hs

theorem recLinear_closed {d N : ℕ} (Q : LargeEvenRawCont) (h : LargeEvenRecipeLinear d N Q) :
    LargeEvenRecipeLinear d N (ClosedCont Q) := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  exact ⟨K, hF, hfin, hK, ⟨hQ, fun f hf n _ =>
    matField_pow_closed _ (fun σ g hg => sl_map_mem σ g hg) _ f hf n⟩⟩

theorem recUnitary_closed {d q : ℕ} (Q : LargeEvenRawCont) (h : LargeEvenRecipeUnitary d q Q) :
    LargeEvenRecipeUnitary d q (ClosedCont Q) := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  exact ⟨K, hF, hfin, hK, ⟨hQ, fun f hf n _ =>
    matField_pow_closed _ (fun σ g hg => su_map_mem σ g hg) _ f hf n⟩⟩

theorem recSymplectic_closed {m q : ℕ} (derived : Bool) (Q : LargeEvenRawCont)
    (h : LargeEvenRecipeSymplectic m q derived Q) :
    LargeEvenRecipeSymplectic m q derived (ClosedCont Q) := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  have hH : ∀ σ : K ≃+* K, ∀ g ∈ (if derived then ⁅LargeEvenSpGroup K m, LargeEvenSpGroup K m⁆
      else LargeEvenSpGroup K m), Matrix.GeneralLinearGroup.map σ.toRingHom g ∈
      (if derived then ⁅LargeEvenSpGroup K m, LargeEvenSpGroup K m⁆ else LargeEvenSpGroup K m) := by
    intro σ g hg
    cases derived
    · exact sp_map_mem σ g hg
    · exact derived_stable _ _ (fun x hx => sp_map_mem σ x hx) hg
  exact ⟨K, hF, hfin, hK, ⟨hQ, fun f hf n _ => matField_pow_closed _ hH _ f hf n⟩⟩

theorem recOmegaPlus_closed {m q : ℕ} (Q : LargeEvenRawCont) (h : LargeEvenRecipeOmegaPlus m q Q) :
    LargeEvenRecipeOmegaPlus m q (ClosedCont Q) := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  exact ⟨K, hF, hfin, hK, ⟨hQ, fun f hf n _ =>
    matField_pow_closed _ (fun σ g hg => omegaPlus_map_mem σ g hg) _ f hf n⟩⟩

theorem recSuzuki_closed {a : ℕ} (Q : LargeEvenRawCont) (h : LargeEvenRecipeSuzuki a Q) :
    LargeEvenRecipeSuzuki a (ClosedCont Q) := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  exact ⟨K, hF, hfin, hK, ⟨hQ, fun f hf n _ =>
    matField_pow_closed _ (fun σ g hg => sz_map_mem σ g hg) _ f hf n⟩⟩

theorem charP_two_of_card_two_pow {K : Type} [Field K] [Finite K] {j : ℕ}
    (hK : Nat.card K = 2 ^ j) : CharP K 2 := by
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨p, hchar, n, hp, hcard⟩ := FiniteField.card' K
  rw [← Nat.card_eq_fintype_card, hK] at hcard
  have hdvd : p ∣ 2 ^ j := by
    rw [hcard]
    exact dvd_pow_self p n.pos.ne'
  have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd)
  subst hp2
  exact hchar

theorem phiQ_pow_closed {n : ℕ} (hn4 : 4 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2]
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {f : MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (n - 1) b c)))}
    (hf : f ∈ LargeEvenPhiQ (n - 1) b c
      (LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus (n - 1) b c))))
    (N : ℕ) :
    f ^ N ∈ LargeEvenPhiQ (n - 1) b c
      (LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus (n - 1) b c))) := by
  obtain ⟨k, hk⟩ := CFSG.StandardType.RecipeFieldOmega.congr_minusEquiv_of_mem_phi hn4 hirr hf
  obtain ⟨φ, hφ, hφe⟩ :=
    CFSG.StandardType.RecipeFieldOmega.exists_mem_phi_congr_minusEquiv hn4 hirr (k * N)
  have e : f ^ N = φ := by
    apply (MulAut.congr (CFSG.StandardType.RecipeFieldOmega.minusEquiv hn4 b c)).injective
    rw [map_pow, hk, hφe, ← pow_mul]
  rw [e]
  exact hφ

theorem recOmegaMinus_closed {n j : ℕ} (hn4 : 4 ≤ n) (Q : LargeEvenRawCont)
    (h : LargeEvenRecipeOmegaMinus (n - 1) (2 ^ j) Q) :
    LargeEvenRecipeOmegaMinus (n - 1) (2 ^ j) (ClosedCont Q) := by
  obtain ⟨K, hF, hfin, hK, b, c, hirr, hQ⟩ := h
  haveI : CharP K 2 := charP_two_of_card_two_pow hK
  exact ⟨K, hF, hfin, hK, b, c, hirr, ⟨hQ, fun f hf N _ => phiQ_pow_closed hn4 hirr hf N⟩⟩

section Chev

variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (K : Type) [Field K]

theorem entrywise_single_one (f : K → K) (hf : f 0 = 0)
    (g : Module.End K (LargeEvenChevModule A K)) (b : LargeEvenRootIndex A) :
    LargeEvenEntrywise A K f hf g (Finsupp.single b 1) =
      Finsupp.mapRange f hf (g (Finsupp.single b 1)) := by
  simp [LargeEvenEntrywise, Finsupp.linearCombination_single]

theorem end_ext_basis {φ ψ : Module.End K (LargeEvenChevModule A K)}
    (h : ∀ b : LargeEvenRootIndex A, φ (Finsupp.single b 1) = ψ (Finsupp.single b 1)) : φ = ψ := by
  apply Finsupp.lhom_ext
  intro b c
  rw [← Finsupp.smul_single_one b c, map_smul, map_smul, h b]

@[expose] noncomputable def trS (σ : K ≃+* K) :
    LargeEvenChevModule A K →+ LargeEvenChevModule A K :=
  Finsupp.mapRange.addMonoidHom (σ.toRingHom.toAddMonoidHom)

theorem trS_apply (σ : K ≃+* K) (v : LargeEvenChevModule A K) :
    trS A K σ v = Finsupp.mapRange σ (map_zero σ) v := rfl

theorem trS_smul (σ : K ≃+* K) (c : K) (v : LargeEvenChevModule A K) :
    trS A K σ (c • v) = σ c • trS A K σ v := by
  rw [trS_apply, trS_apply]
  ext x
  simp [Finsupp.mapRange_apply, Finsupp.smul_apply, smul_eq_mul, map_mul]

theorem trS_rootVec (σ : K ≃+* K) (β : Fin r → ℤ) :
    trS A K σ (LargeEvenRootVec A K β) = LargeEvenRootVec A K β := by
  rw [trS_apply]
  unfold LargeEvenRootVec
  split_ifs
  · simp [Finsupp.mapRange_single]
  · simp

theorem trS_hVec (σ : K ≃+* K) (j : Fin r) :
    trS A K σ (LargeEvenHVec A K j) = LargeEvenHVec A K j := by
  rw [trS_apply]
  simp [LargeEvenHVec, Finsupp.mapRange_single]

theorem mapRange_smul_ring (σ : K ≃+* K) (c : K) (v : LargeEvenChevModule A K) :
    Finsupp.mapRange σ (map_zero σ) (c • v) = σ c • Finsupp.mapRange σ (map_zero σ) v := by
  ext x
  simp [Finsupp.mapRange_apply, Finsupp.smul_apply, smul_eq_mul, map_mul]

theorem entrywise_mapRange (σ : K ≃+* K) (g : Module.End K (LargeEvenChevModule A K))
    (v : LargeEvenChevModule A K) :
    LargeEvenEntrywise A K σ (map_zero σ) g (Finsupp.mapRange σ (map_zero σ) v) =
      Finsupp.mapRange σ (map_zero σ) (g v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw =>
    rw [Finsupp.mapRange_add (map_add σ), map_add, hv, hw, map_add,
      Finsupp.mapRange_add (map_add σ)]
  | single b c =>
    rw [Finsupp.mapRange_single, ← Finsupp.smul_single_one b (σ c), map_smul,
      entrywise_single_one, ← Finsupp.smul_single_one b c, map_smul, mapRange_smul_ring]

theorem entrywise_mul (σ : K ≃+* K) (g h : Module.End K (LargeEvenChevModule A K)) :
    LargeEvenEntrywise A K σ (map_zero σ) (g * h) =
      LargeEvenEntrywise A K σ (map_zero σ) g * LargeEvenEntrywise A K σ (map_zero σ) h := by
  apply end_ext_basis
  intro b
  simp only [Module.End.mul_apply, entrywise_single_one, entrywise_mapRange]

theorem entrywise_one (σ : K ≃+* K) :
    LargeEvenEntrywise A K σ (map_zero σ) (1 : Module.End K (LargeEvenChevModule A K)) = 1 := by
  apply end_ext_basis
  intro b
  simp only [Module.End.one_apply, entrywise_single_one, Finsupp.mapRange_single, map_one]

@[expose] noncomputable def entrywiseHom (σ : K ≃+* K) :
    Module.End K (LargeEvenChevModule A K) →* Module.End K (LargeEvenChevModule A K) where
  toFun g := LargeEvenEntrywise A K σ (map_zero σ) g
  map_one' := entrywise_one A K σ
  map_mul' g h := entrywise_mul A K σ g h

@[expose] noncomputable def chevAct (σ : K ≃+* K) : LargeEvenChevGL A K →* LargeEvenChevGL A K :=
  Units.map (entrywiseHom A K σ)

theorem chevAct_val (σ : K ≃+* K) (g : LargeEvenChevGL A K) :
    ((chevAct A K σ g : LargeEvenChevGL A K) : Module.End K (LargeEvenChevModule A K)) =
      LargeEvenEntrywise A K σ (map_zero σ) (g : Module.End K (LargeEvenChevModule A K)) :=
  rfl

theorem entrywise_fun_comp (f g : K → K) (hf : f 0 = 0) (hg : g 0 = 0)
    (x : Module.End K (LargeEvenChevModule A K)) :
    LargeEvenEntrywise A K f hf (LargeEvenEntrywise A K g hg x) =
      LargeEvenEntrywise A K (fun c => f (g c)) (by simp [hf, hg]) x := by
  apply end_ext_basis
  intro b
  rw [entrywise_single_one, entrywise_single_one, entrywise_single_one]
  ext y
  simp [Finsupp.mapRange_apply]

theorem entrywise_ring_one (x : Module.End K (LargeEvenChevModule A K)) :
    LargeEvenEntrywise A K (1 : K ≃+* K) (map_zero (1 : K ≃+* K)) x = x := by
  apply end_ext_basis
  intro b
  rw [entrywise_single_one]
  ext y
  simp [Finsupp.mapRange_apply]

theorem chevAct_one (g : LargeEvenChevGL A K) : chevAct A K 1 g = g := by
  apply Units.ext
  rw [chevAct_val]
  exact entrywise_ring_one A K _

theorem chevAct_mul (σ τ : K ≃+* K) (g : LargeEvenChevGL A K) :
    chevAct A K (σ * τ) g = chevAct A K σ (chevAct A K τ g) := by
  apply Units.ext
  rw [chevAct_val, chevAct_val, chevAct_val]
  exact (entrywise_fun_comp A K σ τ _ _ _).symm

theorem entrywise_X (σ : K ≃+* K) (i : Fin r) (c : K) :
    LargeEvenEntrywise A K σ (map_zero σ) (LargeEvenXOp A K i c) = LargeEvenXOp A K i (σ c) := by
  apply end_ext_basis
  intro b
  rw [entrywise_single_one, ← trS_apply]
  rcases b with j | α
  · simp only [LargeEvenXOp, Finsupp.linearCombination_single, one_smul, map_add, trS_hVec,
      trS_smul, trS_rootVec, map_mul, map_natCast]
  · simp only [LargeEvenXOp, Finsupp.linearCombination_single, one_smul]
    split_ifs with h1 h2
    · exact trS_rootVec A K σ _
    · simp only [map_add, trS_rootVec, trS_smul, trS_hVec, map_pow]
    · rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [trS_smul, trS_rootVec, map_mul, map_natCast, map_pow]

theorem entrywise_Y (σ : K ≃+* K) (i : Fin r) (c : K) :
    LargeEvenEntrywise A K σ (map_zero σ) (LargeEvenYOp A K i c) = LargeEvenYOp A K i (σ c) := by
  apply end_ext_basis
  intro b
  rw [entrywise_single_one, ← trS_apply]
  rcases b with j | α
  · simp only [LargeEvenYOp, Finsupp.linearCombination_single, one_smul, map_add, trS_hVec,
      trS_smul, trS_rootVec, map_mul, map_natCast]
  · simp only [LargeEvenYOp, Finsupp.linearCombination_single, one_smul]
    split_ifs with h1 h2
    · exact trS_rootVec A K σ _
    · simp only [map_add, trS_rootVec, trS_smul, trS_hVec, map_pow]
    · rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [trS_smul, trS_rootVec, map_mul, map_natCast, map_pow]

theorem chevGroup_map_mem (σ : K ≃+* K) {g : LargeEvenChevGL A K}
    (hg : g ∈ LargeEvenChevGroup A K) : chevAct A K σ g ∈ LargeEvenChevGroup A K := by
  unfold LargeEvenChevGroup at hg ⊢
  refine closure_stable {g : LargeEvenChevGL A K | ∃ (i : Fin r) (c : K),
      (g : Module.End K (LargeEvenChevModule A K)) = LargeEvenXOp A K i c ∨
        (g : Module.End K (LargeEvenChevModule A K)) = LargeEvenYOp A K i c}
    (chevAct A K σ) (fun s hs => Subgroup.subset_closure ?_) hg
  obtain ⟨i, c, h | h⟩ := hs
  · exact ⟨i, σ c, Or.inl (by rw [chevAct_val, h, entrywise_X])⟩
  · exact ⟨i, σ c, Or.inr (by rw [chevAct_val, h, entrywise_Y])⟩

end Chev

section ChevFields

variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (K : Type) [Field K]

theorem chevField_pow_closed (H : Subgroup (LargeEvenChevGL A K))
    (hH : ∀ σ : K ≃+* K, ∀ h ∈ H, chevAct A K σ h ∈ H)
    (f : MulAut (LargeEvenCenterQuot H)) (hf : f ∈ LargeEvenChevFieldImage A K H) (n : ℕ) :
    f ^ n ∈ LargeEvenChevFieldImage A K H := by
  obtain ⟨σ, hσ⟩ := hf
  exact ⟨σ ^ n, graph_pow (S := K ≃+* K) H (LargeEvenCenterMk H) (fun τ g => chevAct A K τ g)
    (chevAct_one A K) (fun a b x => chevAct_mul A K a b x) (fun τ h => hH τ h h.2)
    (fun τ h h' => ((h' : LargeEvenChevGL A K) : Module.End K (LargeEvenChevModule A K)) =
      LargeEvenEntrywise A K τ (map_zero τ)
        ((h : LargeEvenChevGL A K) : Module.End K (LargeEvenChevModule A K)))
    (fun τ h h' => by rw [Units.ext_iff, chevAct_val]) σ f hσ n⟩

theorem chevH_stable (derived : Bool) (σ : K ≃+* K) (h : LargeEvenChevGL A K)
    (hh : h ∈ LargeEvenChevH A K derived) : chevAct A K σ h ∈ LargeEvenChevH A K derived := by
  cases derived
  · exact chevGroup_map_mem A K σ hh
  · exact derived_stable _ _ (fun x hx => chevGroup_map_mem A K σ hx) hh

theorem entrywise_comm_fun (f g : K → K) (hf : f 0 = 0) (hg : g 0 = 0)
    (hcomm : ∀ c, f (g c) = g (f c)) (x : Module.End K (LargeEvenChevModule A K)) :
    LargeEvenEntrywise A K f hf (LargeEvenEntrywise A K g hg x) =
      LargeEvenEntrywise A K g hg (LargeEvenEntrywise A K f hf x) := by
  rw [entrywise_fun_comp, entrywise_fun_comp]
  congr 1
  funext c
  exact hcomm c

theorem entrywise_diagramMap (ρ : Equiv.Perm (Fin r)) (σ : K ≃+* K) :
    LargeEvenEntrywise A K σ (map_zero σ) (LargeEvenDiagramMap A K ρ) =
      LargeEvenDiagramMap A K ρ := by
  apply end_ext_basis
  intro b
  rw [entrywise_single_one]
  rcases b with i | α
  · simp only [LargeEvenDiagramMap, Finsupp.linearCombination_single, one_smul]
    exact trS_hVec A K σ _
  · simp only [LargeEvenDiagramMap, Finsupp.linearCombination_single, one_smul]
    exact trS_rootVec A K σ _

theorem twistedGen_map_mem (ρ : Equiv.Perm (Fin r)) (n : ℕ) (σ : K ≃+* K)
    (g : LargeEvenChevGL A K)
    (hg : g ∈ LargeEvenChevGroup A K ∧ LargeEvenDiagramMap A K ρ *
        LargeEvenEntrywise A K (fun c => c ^ 2 ^ n) (zero_pow (pow_ne_zero n two_ne_zero))
          (g : Module.End K (LargeEvenChevModule A K)) =
        (g : Module.End K (LargeEvenChevModule A K)) * LargeEvenDiagramMap A K ρ) :
    chevAct A K σ g ∈ LargeEvenChevGroup A K ∧ LargeEvenDiagramMap A K ρ *
        LargeEvenEntrywise A K (fun c => c ^ 2 ^ n) (zero_pow (pow_ne_zero n two_ne_zero))
          ((chevAct A K σ g : LargeEvenChevGL A K) : Module.End K (LargeEvenChevModule A K)) =
        ((chevAct A K σ g : LargeEvenChevGL A K) : Module.End K (LargeEvenChevModule A K)) *
          LargeEvenDiagramMap A K ρ := by
  refine ⟨chevGroup_map_mem A K σ hg.1, ?_⟩
  rw [chevAct_val]
  have h1 := congrArg (LargeEvenEntrywise A K σ (map_zero σ)) hg.2
  rw [entrywise_mul, entrywise_mul, entrywise_diagramMap] at h1
  rw [entrywise_comm_fun A K σ (fun c => c ^ 2 ^ n) (map_zero σ)
    (zero_pow (pow_ne_zero n two_ne_zero)) (fun c => map_pow σ c (2 ^ n))] at h1
  exact h1

theorem twisted_map_mem (ρ : Equiv.Perm (Fin r)) (n : ℕ) (σ : K ≃+* K) (h : LargeEvenChevGL A K)
    (hh : h ∈ LargeEvenTwistedH A K ρ n) : chevAct A K σ h ∈ LargeEvenTwistedH A K ρ n := by
  unfold LargeEvenTwistedH at hh ⊢
  refine derived_stable _ (chevAct A K σ) (fun x hx => ?_) hh
  refine closure_stable {g : LargeEvenChevGL A K | g ∈ LargeEvenChevGroup A K ∧
      LargeEvenDiagramMap A K ρ * LargeEvenEntrywise A K (fun c => c ^ 2 ^ n)
        (zero_pow (pow_ne_zero n two_ne_zero)) (g : Module.End K (LargeEvenChevModule A K)) =
        (g : Module.End K (LargeEvenChevModule A K)) * LargeEvenDiagramMap A K ρ}
    (chevAct A K σ) (fun s hs => Subgroup.subset_closure ?_) hx
  exact twistedGen_map_mem A K ρ n σ s hs

end ChevFields

section ReeTits

variable (K : Type) [Field K]

@[expose] def twF4Gens (a : ℕ) : Set (LargeEvenChevGL LargeEvenCartanF4 K ×
    LargeEvenChevGL LargeEvenCartanF4 K) :=
  {gh | ∃ (i : Fin 4) (c : K),
    ((gh.1 : Module.End K (LargeEvenChevModule LargeEvenCartanF4 K)) =
        LargeEvenXOp LargeEvenCartanF4 K i c ∧
      (gh.2 : Module.End K (LargeEvenChevModule LargeEvenCartanF4 K)) =
        LargeEvenXOp LargeEvenCartanF4 K (LargeEvenRhoF4 i) (c ^ LargeEvenTwF4Exp a i)) ∨
    ((gh.1 : Module.End K (LargeEvenChevModule LargeEvenCartanF4 K)) =
        LargeEvenYOp LargeEvenCartanF4 K i c ∧
      (gh.2 : Module.End K (LargeEvenChevModule LargeEvenCartanF4 K)) =
        LargeEvenYOp LargeEvenCartanF4 K (LargeEvenRhoF4 i) (c ^ LargeEvenTwF4Exp a i))}

theorem twF4R0_map_mem (a : ℕ) (σ : K ≃+* K)
    {x : LargeEvenChevGL LargeEvenCartanF4 K × LargeEvenChevGL LargeEvenCartanF4 K}
    (hx : x ∈ Subgroup.closure (twF4Gens K a)) :
    MonoidHom.prodMap (chevAct LargeEvenCartanF4 K σ) (chevAct LargeEvenCartanF4 K σ) x ∈
      Subgroup.closure (twF4Gens K a) := by
  refine closure_stable _ _ (fun s hs => Subgroup.subset_closure ?_) hx
  unfold twF4Gens at hs ⊢
  obtain ⟨i, c, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := hs
  · refine ⟨i, σ c, Or.inl ⟨?_, ?_⟩⟩
    · show ((chevAct LargeEvenCartanF4 K σ s.1 : LargeEvenChevGL LargeEvenCartanF4 K) :
        Module.End K (LargeEvenChevModule LargeEvenCartanF4 K)) = _
      rw [chevAct_val, h1, entrywise_X]
    · show ((chevAct LargeEvenCartanF4 K σ s.2 : LargeEvenChevGL LargeEvenCartanF4 K) :
        Module.End K (LargeEvenChevModule LargeEvenCartanF4 K)) = _
      rw [chevAct_val, h2, entrywise_X, map_pow]
  · refine ⟨i, σ c, Or.inr ⟨?_, ?_⟩⟩
    · show ((chevAct LargeEvenCartanF4 K σ s.1 : LargeEvenChevGL LargeEvenCartanF4 K) :
        Module.End K (LargeEvenChevModule LargeEvenCartanF4 K)) = _
      rw [chevAct_val, h1, entrywise_Y]
    · show ((chevAct LargeEvenCartanF4 K σ s.2 : LargeEvenChevGL LargeEvenCartanF4 K) :
        Module.End K (LargeEvenChevModule LargeEvenCartanF4 K)) = _
      rw [chevAct_val, h2, entrywise_Y, map_pow]

theorem twF4Parent_map_mem (a : ℕ) (σ : K ≃+* K) (x : LargeEvenChevGL LargeEvenCartanF4 K)
    (hx : x ∈ LargeEvenTwF4Parent a K) :
    chevAct LargeEvenCartanF4 K σ x ∈ LargeEvenTwF4Parent a K := by
  dsimp only [LargeEvenTwF4Parent] at hx ⊢
  rw [Subgroup.mem_inf] at hx ⊢
  refine ⟨chevGroup_map_mem LargeEvenCartanF4 K σ hx.1, ?_⟩
  rw [Subgroup.mem_comap] at hx ⊢
  have key := twF4R0_map_mem K a σ (x := (x, x)) hx.2
  unfold twF4Gens at key
  simpa only [MonoidHom.prod_apply, MonoidHom.coe_prodMap, Prod.map_apply, MonoidHom.id_apply]
    using key

theorem twF4H_map_mem (a : ℕ) (σ : K ≃+* K) (h : LargeEvenChevGL LargeEvenCartanF4 K)
    (hh : h ∈ LargeEvenTwF4H a K) : chevAct LargeEvenCartanF4 K σ h ∈ LargeEvenTwF4H a K := by
  unfold LargeEvenTwF4H at hh ⊢
  exact derived_stable _ _ (fun x hx => twF4Parent_map_mem K a σ x hx) hh

end ReeTits

theorem recChevalley_closed {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) {q : ℕ} (derived : Bool)
    (Q : LargeEvenRawCont) (h : LargeEvenRecipeChevalley A q derived Q) :
    LargeEvenRecipeChevalley A q derived (ClosedCont Q) := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  exact ⟨K, hF, hfin, hK, ⟨hQ, fun f hf n _ =>
    chevField_pow_closed A K _ (fun σ h hh => chevH_stable A K derived σ h hh) f hf n⟩⟩

theorem recG2Derived_closed (Q : LargeEvenRawCont) (h : LargeEvenRecipeG2Derived Q) :
    LargeEvenRecipeG2Derived (ClosedCont Q) := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  exact ⟨K, hF, hfin, hK, ⟨hQ, fun f hf n _ =>
    chevField_pow_closed LargeEvenCartanG2 K _
      (fun σ h hh => chevH_stable LargeEvenCartanG2 K true σ h hh) f hf n⟩⟩

theorem recTwisted_closed {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (ρ : Equiv.Perm (Fin r))
    (m n : ℕ) (Q : LargeEvenRawCont) (h : LargeEvenRecipeTwisted A ρ m n Q) :
    LargeEvenRecipeTwisted A ρ m n (ClosedCont Q) := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  exact ⟨K, hF, hfin, hK, ⟨hQ, fun f hf N _ =>
    chevField_pow_closed A K _ (fun σ h hh => twisted_map_mem A K ρ n σ h hh) f hf N⟩⟩

theorem recTwF4Inherited_closed (a : ℕ) (Q : LargeEvenRawCont)
    (h : LargeEvenRecipeTwF4Inherited a Q) : LargeEvenRecipeTwF4Inherited a (ClosedCont Q) := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  exact ⟨K, hF, hfin, hK, ⟨hQ, fun f hf n _ =>
    chevField_pow_closed LargeEvenCartanF4 K _
      (fun σ h hh => twF4H_map_mem K a σ h hh) f hf n⟩⟩

theorem rawDatum_closed (lab : LargeEvenLabel) (hlab : LargeEvenInLambda2 lab)
    (Q : LargeEvenRawCont) (h : LargeEvenRawDatum lab Q) :
    LargeEvenRawDatum lab (ClosedCont Q) := by
  obtain ⟨tag, rank, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  cases tag
  case A => exact recLinear_closed _ h
  case twA => exact recUnitary_closed _ h
  case B => exact recSymplectic_closed false _ h
  case C => exact recSymplectic_closed false _ h
  case D =>
    unfold LargeEvenRawDatum at h ⊢
    dsimp only at h ⊢
    split_ifs at h ⊢
    · exact recLinear_closed _ h
    · exact recOmegaPlus_closed _ h
  case twD =>
    have h2 : 2 ≤ rank := hlab.2
    unfold LargeEvenRawDatum at h ⊢
    dsimp only at h ⊢
    split_ifs at h ⊢ with h2' h3'
    · exact recLinear_closed _ h
    · exact recUnitary_closed _ h
    · exact recOmegaMinus_closed (n := rank) (by omega) _ h
  case E6 => exact recChevalley_closed (LargeEvenCartanE 6) false _ h
  case E7 => exact recChevalley_closed (LargeEvenCartanE 7) false _ h
  case E8 => exact recChevalley_closed (LargeEvenCartanE 8) false _ h
  case F4 => exact recChevalley_closed LargeEvenCartanF4 false _ h
  case twE6 => exact recTwisted_closed (LargeEvenCartanE 6) LargeEvenRhoE6 2 n _ h
  case triD4 => exact recTwisted_closed LargeEvenCartanD4 LargeEvenRhoD4 3 n _ h
  case G2 => exact recChevalley_closed LargeEvenCartanG2 false _ h
  case twB2 => exact recSuzuki_closed _ h
  case twF4 => exact recTwF4Inherited_closed _ _ h
  case B2der => exact recSymplectic_closed true _ h
  case G2der => exact recG2Derived_closed _ h
  case twF4der => exact recTwF4Inherited_closed _ _ h

end YS09Field

theorem fieldAutPowClosedAt_holds : FieldAutPowClosedAt := by
  unfold FieldAutPowClosedAt
  intro lab hlab Q hQ
  exact YS09Field.rawDatum_closed lab hlab Q hQ

end CFSG.LocalAnalysis.GLTheoremA
