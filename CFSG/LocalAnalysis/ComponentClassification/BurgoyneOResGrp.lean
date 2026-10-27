module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneORes
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLUnitary

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Subgroup

variable {K : Type} [Field K]

@[expose] def CompData {G : Type*} [Group G] (F : Subgroup G) : Prop :=
  ⁅F, F⁆ = F ∧ ∃ (m : ℕ) (L : Fin m → Subgroup G), (⨆ i, L i) = F ∧
    ∀ i, IsQuasisimple (L i) ∧ L i ≤ F ∧ ∀ x ∈ F, ∀ l ∈ L i, x * l * x⁻¹ ∈ L i

theorem CompData.map {G G' : Type*} [Group G] [Group G'] {F : Subgroup G} (h : CompData F)
    {f : G →* G'} (hf : Function.Injective f) : CompData (F.map f) := by
  obtain ⟨hperf, m, L, hsup, hL⟩ := h
  refine ⟨by rw [← Subgroup.map_commutator, hperf], m, fun i => (L i).map f, ?_,
    fun i => ⟨?_, map_mono (hL i).2.1, ?_⟩⟩
  · rw [← Subgroup.map_iSup, hsup]
  · exact LocalCores.isQuasisimple_of_mulEquiv ((L i).equivMapOfInjective _ hf) (hL i).1
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨l, hl, rfl⟩
    exact ⟨x * l * x⁻¹, (hL i).2.2 x hx l hl, by simp only [map_mul, map_inv]⟩

theorem CompData.of_isQuasisimple {G : Type*} [Group G] {F : Subgroup G} (h : IsQuasisimple F) :
    CompData F :=
  ⟨PSL.commutator_eq_self_of_isQuasisimple h, 1, fun _ => F, by simp,
    fun _ => ⟨h, le_rfl, fun _ hx _ hl => mul_mem (mul_mem hx hl) (inv_mem hx)⟩⟩

theorem CompData.congr {G : Type*} [Group G] {F F' : Subgroup G} (h : CompData F) (e : F = F') :
    CompData F' := e ▸ h

theorem blkDiag_mul (n : ℕ) (W W' : Matrix (Fin 2) (Fin 2) K) :
    blkDiag n W * blkDiag n W' = blkDiag n (W * W') := by
  rw [blkDiag, blkDiag, blkDiag, ← map_mul, diagonal_mul_diagonal]

theorem blkDiag_one (n : ℕ) : blkDiag n (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  rw [blkDiag, diagonal_one, map_one]

theorem blkDiag_transpose (n : ℕ) (W : Matrix (Fin 2) (Fin 2) K) :
    (blkDiag n W)ᵀ = blkDiag n Wᵀ := by
  rw [blkDiag, blkEquiv_transpose, blkDiag, diagonal_transpose]
  congr 1
  ext i k : 1
  simp only [map_apply, diagonal_apply]
  split_ifs <;> simp

variable {Λ : Type*} [CommRing Λ]

@[expose] def resGL (φ : Λ →+* Matrix (Fin 2) (Fin 2) K) (n : ℕ) :
    GL (Fin n) Λ →* GL (Fin (2 * n)) K :=
  Units.map (resMat φ n).toMonoidHom

theorem coe_resGL (φ : Λ →+* Matrix (Fin 2) (Fin 2) K) (n : ℕ) (Y : GL (Fin n) Λ) :
    ((resGL φ n Y : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) =
      resMat φ n (Y : Matrix (Fin n) (Fin n) Λ) := rfl

theorem resGL_injective {φ : Λ →+* Matrix (Fin 2) (Fin 2) K} (hφ : Function.Injective φ)
    (n : ℕ) : Function.Injective (resGL φ n) :=
  fun _ _ h => Units.ext (resMat_injective hφ n (congrArg Units.val h))

variable (K) in
@[expose] def kronGL (n : ℕ) : GL (Fin n) K →* GL (Fin (2 * n)) K :=
  Units.map (kronI K n).toMonoidHom

theorem coe_kronGL (n : ℕ) (X : GL (Fin n) K) :
    ((kronGL K n X : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) =
      kronI K n (X : Matrix (Fin n) (Fin n) K) := rfl

theorem resGL_map_algebraMap [Algebra K Λ] (φ : Λ →+* Matrix (Fin 2) (Fin 2) K)
    (hφ : ∀ a : K, φ (algebraMap K Λ a) = algebraMap K (Matrix (Fin 2) (Fin 2) K) a) (n : ℕ)
    (X : GL (Fin n) K) :
    resGL φ n (GeneralLinearGroup.map (algebraMap K Λ) X) = kronGL K n X :=
  Units.ext (resMat_map_algebraMap φ hφ n X)

@[expose] def uGrp (σ : Λ →+* Λ) {n : ℕ} (G : Matrix (Fin n) (Fin n) Λ) :
    Subgroup (GL (Fin n) Λ) where
  carrier := {Y | ((Y : Matrix (Fin n) (Fin n) Λ).map σ)ᵀ * G * Y = G}
  mul_mem' {Y Y'} hY hY' := by
    simp only [Set.mem_ofPred_eq, Units.val_mul, Matrix.map_mul, transpose_mul] at hY hY' ⊢
    calc ((Y' : Matrix (Fin n) (Fin n) Λ).map σ)ᵀ * ((Y : Matrix (Fin n) (Fin n) Λ).map σ)ᵀ * G *
          ((Y : Matrix (Fin n) (Fin n) Λ) * Y') =
        ((Y' : Matrix (Fin n) (Fin n) Λ).map σ)ᵀ *
          (((Y : Matrix (Fin n) (Fin n) Λ).map σ)ᵀ * G * Y) * Y' := by
          simp only [Matrix.mul_assoc]
      _ = G := by rw [hY, hY']
  one_mem' := by
    simp only [Set.mem_ofPred_eq, Units.val_one, Matrix.map_one σ (map_zero σ) (map_one σ),
      transpose_one, Matrix.one_mul, Matrix.mul_one]
  inv_mem' {Y} hY := by
    simp only [Set.mem_ofPred_eq] at hY ⊢
    have h1 : (Y : Matrix (Fin n) (Fin n) Λ) * ((Y⁻¹ : GL (Fin n) Λ) : Matrix (Fin n) (Fin n) Λ) =
        1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc (((Y⁻¹ : GL (Fin n) Λ) : Matrix (Fin n) (Fin n) Λ).map σ)ᵀ * G *
          ((Y⁻¹ : GL (Fin n) Λ) : Matrix (Fin n) (Fin n) Λ) =
        (((Y⁻¹ : GL (Fin n) Λ) : Matrix (Fin n) (Fin n) Λ).map σ)ᵀ *
          (((Y : Matrix (Fin n) (Fin n) Λ).map σ)ᵀ * G * Y) *
            ((Y⁻¹ : GL (Fin n) Λ) : Matrix (Fin n) (Fin n) Λ) := by rw [hY]
      _ = ((((Y : Matrix (Fin n) (Fin n) Λ) *
            ((Y⁻¹ : GL (Fin n) Λ) : Matrix (Fin n) (Fin n) Λ)).map σ)ᵀ * G *
          ((Y : Matrix (Fin n) (Fin n) Λ) *
            ((Y⁻¹ : GL (Fin n) Λ) : Matrix (Fin n) (Fin n) Λ))) := by
          simp only [Matrix.map_mul, transpose_mul, Matrix.mul_assoc]
      _ = G := by
          rw [h1, Matrix.map_one σ (map_zero σ) (map_one σ), transpose_one, Matrix.one_mul,
            Matrix.mul_one]

theorem mem_uGrp (σ : Λ →+* Λ) {n : ℕ} (G : Matrix (Fin n) (Fin n) Λ) (Y : GL (Fin n) Λ) :
    Y ∈ uGrp σ G ↔ ((Y : Matrix (Fin n) (Fin n) Λ).map σ)ᵀ * G * Y = G := Iff.rfl

section Centralizer

variable {φ : Λ →+* Matrix (Fin 2) (Fin 2) K} {σ : Λ →+* Λ} {W₀ : Matrix (Fin 2) (Fin 2) K}

theorem resMat_transpose_mul_mul (hW : ∀ x, (φ x)ᵀ * W₀ = W₀ * φ (σ x)) {n : ℕ}
    (G Y : Matrix (Fin n) (Fin n) Λ) :
    (resMat φ n Y)ᵀ * (blkDiag n W₀ * resMat φ n G) * resMat φ n Y =
      blkDiag n W₀ * resMat φ n ((Y.map σ)ᵀ * G * Y) := by
  rw [← Matrix.mul_assoc, resMat_transpose_mul φ σ hW, map_mul, map_mul]
  simp only [Matrix.mul_assoc]

variable {j : Matrix (Fin 2) (Fin 2) K} {r : Λ}

theorem resGL_mem_iso_inf (hW : ∀ x, (φ x)ᵀ * W₀ = W₀ * φ (σ x)) (hr : φ r = j) {n : ℕ}
    {G : Matrix (Fin n) (Fin n) Λ} {R A : GL (Fin (2 * n)) K}
    (hR : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n W₀ * resMat φ n G)
    (hA : (A : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n j) {Y : GL (Fin n) Λ}
    (hY : Y ∈ uGrp σ G) :
    resGL φ n Y ∈ CatalogueBGraphForm.isometryGroup (2 * n) K R ⊓
      centralizer ({A} : Set (GL (Fin (2 * n)) K)) := by
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [CatalogueBGraphForm.mem_isometryGroup]
    change (resMat φ n (Y : Matrix (Fin n) (Fin n) Λ))ᵀ * R.val *
      resMat φ n (Y : Matrix (Fin n) (Fin n) Λ) = R.val
    rw [show R.val = (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) from rfl, hR,
      resMat_transpose_mul_mul hW, (mem_uGrp σ G Y).1 hY]
  · rw [mem_centralizer_singleton_iff]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hA, coe_resGL, ← hr, ← resMat_diagonal, ← map_mul,
      ← map_mul]
    congr 1
    ext i k
    rw [diagonal_mul, mul_diagonal, mul_comm]

theorem iso_inf_centralizer_eq (hφ : Function.Injective φ) {W₀' : Matrix (Fin 2) (Fin 2) K}
    (hW₀ : W₀' * W₀ = 1) (hW : ∀ x, (φ x)ᵀ * W₀ = W₀ * φ (σ x)) (hr : φ r = j)
    (hcomm : ∀ M : Matrix (Fin 2) (Fin 2) K, M * j = j * M → ∃ x, φ x = M) {n : ℕ}
    (G : Matrix (Fin n) (Fin n) Λ) {R A : GL (Fin (2 * n)) K}
    (hR : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n W₀ * resMat φ n G)
    (hA : (A : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n j) :
    CatalogueBGraphForm.isometryGroup (2 * n) K R ⊓
        centralizer ({A} : Set (GL (Fin (2 * n)) K)) = (uGrp σ G).map (resGL φ n) := by
  apply le_antisymm
  · intro h hh
    obtain ⟨hiso, hcen⟩ := Subgroup.mem_inf.1 hh
    have hcm : ∀ g : GL (Fin (2 * n)) K, g ∈ centralizer ({A} : Set (GL (Fin (2 * n)) K)) →
        (g : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * blkDiag n j =
          blkDiag n j * (g : Matrix (Fin (2 * n)) (Fin (2 * n)) K) := by
      intro g hg
      have := congrArg Units.val (mem_centralizer_singleton_iff.1 hg)
      rw [Units.val_mul, Units.val_mul, hA] at this
      exact this
    obtain ⟨Y, hY⟩ := exists_resMat_of_commute φ hcomm (hcm h hcen)
    obtain ⟨Y', hY'⟩ := exists_resMat_of_commute φ hcomm (hcm h⁻¹ (inv_mem hcen))
    have e1 : Y * Y' = 1 := resMat_injective hφ n (by
      rw [map_mul, hY, hY', ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one])
    have e2 : Y' * Y = 1 := resMat_injective hφ n (by
      rw [map_mul, hY, hY', ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one])
    refine ⟨⟨Y, Y', e1, e2⟩, (mem_uGrp σ G _).2 ?_, Units.ext hY⟩
    change ((Y.map σ)ᵀ * G * Y) = G
    apply resMat_injective hφ n
    have hiso' := (CatalogueBGraphForm.mem_isometryGroup _ _ _ _).1 hiso
    rw [show h.val = (h : Matrix (Fin (2 * n)) (Fin (2 * n)) K) from rfl,
      show R.val = (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) from rfl, hR, ← hY,
      resMat_transpose_mul_mul hW] at hiso'
    have := congrArg (fun M => blkDiag n W₀' * M) hiso'
    simp only [← Matrix.mul_assoc, blkDiag_mul, hW₀, blkDiag_one, Matrix.one_mul] at this
    exact this
  · rintro _ ⟨Y, hY, rfl⟩
    exact resGL_mem_iso_inf hW hr hR hA hY

theorem commutator_iso_inf_centralizer_eq (hφ : Function.Injective φ)
    {W₀' : Matrix (Fin 2) (Fin 2) K} (hW₀ : W₀' * W₀ = 1) (hW : ∀ x, (φ x)ᵀ * W₀ = W₀ * φ (σ x))
    (hr : φ r = j) (hcomm : ∀ M : Matrix (Fin 2) (Fin 2) K, M * j = j * M → ∃ x, φ x = M)
    {n : ℕ} (G : Matrix (Fin n) (Fin n) Λ) {R A : GL (Fin (2 * n)) K}
    (hR : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n W₀ * resMat φ n G)
    (hA : (A : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n j) :
    ⁅CatalogueBGraphForm.isometryGroup (2 * n) K R ⊓
        centralizer ({A} : Set (GL (Fin (2 * n)) K)),
      CatalogueBGraphForm.isometryGroup (2 * n) K R ⊓
        centralizer ({A} : Set (GL (Fin (2 * n)) K))⁆ =
      (⁅uGrp σ G, uGrp σ G⁆).map (resGL φ n) := by
  rw [iso_inf_centralizer_eq hφ hW₀ hW hr hcomm G hR hA, Subgroup.map_commutator]

theorem kronGL_mem_iso_inf [Algebra K Λ]
    (hφa : ∀ a : K, φ (algebraMap K Λ a) = algebraMap K (Matrix (Fin 2) (Fin 2) K) a)
    (hσa : ∀ a : K, σ (algebraMap K Λ a) = algebraMap K Λ a)
    (hW : ∀ x, (φ x)ᵀ * W₀ = W₀ * φ (σ x)) (hr : φ r = j) {n : ℕ}
    {G : Matrix (Fin n) (Fin n) Λ} {R A : GL (Fin (2 * n)) K}
    (hR : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n W₀ * resMat φ n G)
    (hA : (A : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n j) {X : GL (Fin n) K}
    (hX : (X : Matrix (Fin n) (Fin n) K)ᵀ * X = 1)
    (hXG : (X : Matrix (Fin n) (Fin n) K).map (algebraMap K Λ) * G =
      G * (X : Matrix (Fin n) (Fin n) K).map (algebraMap K Λ)) :
    kronGL K n X ∈ CatalogueBGraphForm.isometryGroup (2 * n) K R ⊓
      centralizer ({A} : Set (GL (Fin (2 * n)) K)) := by
  rw [← resGL_map_algebraMap φ hφa]
  refine resGL_mem_iso_inf hW hr hR hA ?_
  rw [mem_uGrp]
  change (((X : Matrix (Fin n) (Fin n) K).map (algebraMap K Λ)).map σ)ᵀ * G *
    (X : Matrix (Fin n) (Fin n) K).map (algebraMap K Λ) = G
  have hmap : ((X : Matrix (Fin n) (Fin n) K).map (algebraMap K Λ)).map σ =
      (X : Matrix (Fin n) (Fin n) K).map (algebraMap K Λ) := by
    ext i k
    simp only [map_apply, hσa]
  rw [hmap, Matrix.mul_assoc, ← hXG, ← Matrix.mul_assoc, ← transpose_map, ← Matrix.map_mul, hX,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

end Centralizer

end CFSG.ComponentClassification.Burgoyne.O
