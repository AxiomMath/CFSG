module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLSplit

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.PSL

open Matrix CFSG Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.TBLit
open scoped commutatorElement MatrixGroups

variable {n : ℕ} {K : Type} [Field K]

theorem isSubnormal_map_fixed
    (hinj : Function.Injective (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)))
    {B : Subgroup (MulAut (projectiveSL n K))}
    (hB : (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range ≤ B)
    {t : MulAut (projectiveSL n K)}
    (φ : SpecialLinearGroup (Fin n) K →* SpecialLinearGroup (Fin n) K)
    (hφ : ∀ g, t (proj n K g) = proj n K (φ g))
    {F : Subgroup (SpecialLinearGroup (Fin n) K)} (hF1 : ∀ g ∈ F, φ g = g)
    (hF2 : ∀ h : SpecialLinearGroup (Fin n) K, h⁻¹ * φ h ∈ scalars n K →
      ∀ g ∈ F, h * g * h⁻¹ ∈ F) :
    F.map (conjProj n K) ≤ B ⊓ centralizer ({t} : Set _) ∧
      ((F.map (conjProj n K)).subgroupOf (B ⊓ centralizer ({t} : Set _))).IsSubnormal := by
  set H := B ⊓ centralizer ({t} : Set (MulAut (projectiveSL n K))) with hH
  set Inn := (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range with hInn
  have hInnN : Inn.Normal := conj_range_normal
  have hFC : F.map (conjProj n K) ≤ Inn ⊓ H := by
    rintro _ ⟨g, hg, rfl⟩
    refine ⟨⟨_, rfl⟩, hB ⟨_, rfl⟩, mem_centralizer_singleton_iff.2 ?_⟩
    have h1 : t * conjProj n K g * t⁻¹ = conjProj n K g := by
      rw [MonoidHom.comp_apply, mul_conj_mul_inv, hφ, hF1 g hg]
    calc conjProj n K g * t = t * conjProj n K g * t⁻¹ * t := by rw [h1]
      _ = t * conjProj n K g := by group
  have hnF : ∀ c ∈ Inn ⊓ H, ∀ x ∈ F.map (conjProj n K), c * x * c⁻¹ ∈ F.map (conjProj n K) := by
    rintro c ⟨⟨y, rfl⟩, -, hct⟩ _ ⟨g, hg, rfl⟩
    obtain ⟨h, rfl⟩ := proj_surjective n K y
    have hct' := mem_centralizer_singleton_iff.1 hct
    have h1 : MulAut.conj (t (proj n K h)) = MulAut.conj (proj n K h) := by
      have h0 : t * MulAut.conj (proj n K h) * t⁻¹ = MulAut.conj (proj n K h) := by
        have : MulAut.conj (proj n K h) * t = t * MulAut.conj (proj n K h) := hct'
        rw [← this, mul_inv_cancel_right]
      rwa [mul_conj_mul_inv] at h0
    have h2 : proj n K h = proj n K (φ h) := by rw [← hφ]; exact (hinj h1).symm
    refine ⟨h * g * h⁻¹, hF2 h (proj_eq_proj_iff.1 h2) g hg, ?_⟩
    simp only [map_mul, map_inv]
    rfl
  have hC : ((Inn ⊓ H).subgroupOf H).IsSubnormal := isSubnormal_inf_subgroupOf H
  exact ⟨hFC.trans inf_le_right, isSubnormal_subgroupOf_of_normalizes hFC hnF hC⟩

theorem commute_oddCoreIn_of_fixed [Finite K]
    (hinj : Function.Injective (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)))
    {B : Subgroup (MulAut (projectiveSL n K))}
    (hB : (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range ≤ B)
    {t : MulAut (projectiveSL n K)}
    (φ : SpecialLinearGroup (Fin n) K →* SpecialLinearGroup (Fin n) K)
    (hφ : ∀ g, t (proj n K g) = proj n K (φ g))
    {F : Subgroup (SpecialLinearGroup (Fin n) K)} (hF1 : ∀ g ∈ F, φ g = g)
    (hF2 : ∀ h : SpecialLinearGroup (Fin n) K, h⁻¹ * φ h ∈ scalars n K →
      ∀ g ∈ F, h * g * h⁻¹ ∈ F)
    (hq : IsQuasisimple (F.map (conjProj n K))) {y : MulAut (projectiveSL n K)}
    (hy : y ∈ oddCoreIn B t) {g : SpecialLinearGroup (Fin n) K} (hg : g ∈ F) :
    y (proj n K g) = proj n K g := by
  obtain ⟨hle, hs⟩ := isSubnormal_map_fixed hinj hB φ hφ hF1 hF2
  exact apply_proj_eq_of_commute hinj
    (commute_of_mem_pPrimeCore hle hq hs (even_card_of_isQuasisimple hq) hy ⟨g, hg, rfl⟩)

theorem conj_mem_eqLocus_of_scalar
    (φ : SpecialLinearGroup (Fin n) K →* SpecialLinearGroup (Fin n) K)
    {h : SpecialLinearGroup (Fin n) K} (hh : h⁻¹ * φ h ∈ scalars n K)
    {g : SpecialLinearGroup (Fin n) K} (hg : g ∈ MonoidHom.eqLocus φ (MonoidHom.id _)) :
    h * g * h⁻¹ ∈ MonoidHom.eqLocus φ (MonoidHom.id _) := by
  have hz := mem_center_iff.1 (scalars_le_center n K hh)
  have hg' : φ g = g := hg
  have hφh : φ h = h * (h⁻¹ * φ h) := by rw [mul_inv_cancel_left]
  change φ (h * g * h⁻¹) = h * g * h⁻¹
  rw [map_mul, map_mul, map_inv, hg', hφh]
  set z := h⁻¹ * φ h
  calc h * z * g * (h * z)⁻¹ = h * (z * g) * z⁻¹ * h⁻¹ := by group
    _ = h * (g * z) * z⁻¹ * h⁻¹ := by rw [hz g]
    _ = h * g * h⁻¹ := by group

theorem commutatorElement_mul_mem_center {G : Type*} [Group G] (a b : G) {w v : G}
    (hw : w ∈ Subgroup.center G) (hv : v ∈ Subgroup.center G) : ⁅a * w, b * v⁆ = ⁅a, b⁆ := by
  have hw' := mem_center_iff.1 hw
  have hv' := mem_center_iff.1 hv
  have hwi : ∀ g : G, g * w⁻¹ = w⁻¹ * g := fun g => by
    rw [mul_inv_eq_iff_eq_mul, mul_assoc, hw' g, inv_mul_cancel_left]
  simp only [commutatorElement_def, _root_.mul_inv_rev]
  calc a * w * (b * v) * (w⁻¹ * a⁻¹) * (v⁻¹ * b⁻¹)
      = a * (w * b) * v * w⁻¹ * a⁻¹ * v⁻¹ * b⁻¹ := by group
    _ = a * b * (w * v * w⁻¹) * a⁻¹ * v⁻¹ * b⁻¹ := by rw [← hw' b]; group
    _ = a * b * v * a⁻¹ * v⁻¹ * b⁻¹ := by rw [← hw' v]; group
    _ = a * b * (v * a⁻¹) * v⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * v) * v⁻¹ * b⁻¹ := by rw [← hv' a⁻¹]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem slConj_map_eq_of_commutator_eq {D : GL (Fin n) K} {τ : K ≃+* K}
    {F : Subgroup (SpecialLinearGroup (Fin n) K)} (hF : ⁅F, F⁆ = F)
    (h : ∀ g ∈ F, (conjAut n K D * fieldAut n K τ) (proj n K g) = proj n K g) {g}
    (hg : g ∈ F) :
    CatalogueBHigherLinearAction.slConjugation n K D (SpecialLinearGroup.map τ.toRingHom g) =
      g := by
  set φ : SpecialLinearGroup (Fin n) K →* SpecialLinearGroup (Fin n) K :=
    (CatalogueBHigherLinearAction.slConjugation n K D).toMonoidHom.comp
      (SpecialLinearGroup.map τ.toRingHom) with hφ
  have hz : ∀ a ∈ F, a⁻¹ * φ a ∈ Subgroup.center (SpecialLinearGroup (Fin n) K) := by
    intro a ha
    apply scalars_le_center n K
    rw [← proj_eq_proj_iff]
    have := h a ha
    rw [MulAut.mul_apply, fieldAut_proj, conjAut_proj] at this
    exact this.symm
  have hle : ⁅F, F⁆ ≤ MonoidHom.eqLocus φ (MonoidHom.id _) := by
    rw [commutator_le]
    intro a ha b hb
    change φ ⁅a, b⁆ = ⁅a, b⁆
    rw [map_commutatorElement, ← mul_inv_cancel_left a (φ a), ← mul_inv_cancel_left b (φ b)]
    exact commutatorElement_mul_mem_center a b (hz a ha) (hz b hb)
  exact hle (hF.symm ▸ hg)

theorem fix_unipotent_family {p : ℕ} [Fact p.Prime] [CharP K p]
    {N : Matrix (Fin n) (Fin n) K} (hNN : N * N = 0) {a b : Fin n} (hab : N a b ≠ 0)
    (g : K → SpecialLinearGroup (Fin n) K) (hg : ∀ c, (g c : Matrix (Fin n) (Fin n) K) = 1 + c • N)
    {D : GL (Fin n) K} {τ : K ≃+* K}
    (h : ∀ c : K, (conjAut n K D * fieldAut n K τ) (proj n K (g c)) = proj n K (g c)) :
    τ = 1 ∧ (D : Matrix (Fin n) (Fin n) K) * N = N * (D : Matrix (Fin n) (Fin n) K) := by
  set M : Matrix (Fin n) (Fin n) K := (D : Matrix (Fin n) (Fin n) K) with hM
  set Mi : Matrix (Fin n) (Fin n) K := ((D⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    with hMi
  have h1M : M * Mi = 1 := by rw [hM, hMi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2' : Mi * M = 1 := by rw [hM, hMi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hpow : ∀ (c : K) (k : ℕ), ((1 + c • N) ^ k : Matrix (Fin n) (Fin n) K) =
      1 + ((k : K) * c) • N := by
    intro c k
    induction k with
    | zero => simp
    | succ k ih =>
      have hN1 : N * (1 + c • N) = N := by
        rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, hNN, smul_zero, add_zero]
      rw [pow_succ, ih, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, hN1, add_assoc,
        ← add_smul]
      congr 2
      push_cast
      ring
  have hgp : ∀ c, g c ^ p = 1 := by
    intro c
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, hg, hpow, CharP.cast_eq_zero, zero_mul, zero_smul,
      add_zero, Matrix.SpecialLinearGroup.coe_one]
  have hmap : ∀ c, ((SpecialLinearGroup.map τ.toRingHom (g c) : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = 1 + τ c • N.map τ := by
    intro c
    rw [Matrix.SpecialLinearGroup.map_apply_coe, hg, RingHom.mapMatrix_apply]
    ext x y
    have e : ∀ z, τ.toRingHom z = τ z := fun z => rfl
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, one_apply, e]
    rw [map_add, map_mul]
    split_ifs <;> simp
  have key : ∀ c : K, M * (τ c • N.map τ) * Mi = c • N := by
    intro c
    have h1 := h c
    rw [MulAut.mul_apply, fieldAut_proj, conjAut_proj] at h1
    have h3 := eq_of_proj_eq_of_pow_char (p := p)
      (by rw [← map_pow, ← map_pow, hgp, map_one, map_one]) (hgp c) h1
    have h4 := congrArg (fun x : SpecialLinearGroup (Fin n) K =>
      (x : Matrix (Fin n) (Fin n) K)) h3
    simp only [CatalogueBHigherLinearAction.slConjugation_matrix, hg, hmap] at h4
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, h1M] at h4
    exact add_left_cancel h4
  have e1 := key 1
  rw [map_one, one_smul, one_smul] at e1
  have hτ : ∀ c, τ c = c := by
    intro c
    have e2 := key c
    rw [Matrix.mul_smul, Matrix.smul_mul, e1] at e2
    have := congrFun (congrFun e2 a) b
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    exact mul_right_cancel₀ hab this
  have hτ1 : τ = 1 := RingEquiv.ext hτ
  refine ⟨hτ1, ?_⟩
  have hNτ : N.map τ = N := by
    ext x y
    simp [hτ]
  rw [hNτ] at e1
  calc M * N = M * N * Mi * M := by rw [Matrix.mul_assoc _ Mi, h2', Matrix.mul_one]
    _ = N * M := by rw [e1]

theorem fix_transvections_on {p : ℕ} [Fact p.Prime] [CharP K p]
    {i j : Fin n} (hij : i ≠ j) {D : GL (Fin n) K} {τ : K ≃+* K} {S : Set K} (hS : (1 : K) ∈ S)
    (h : ∀ c ∈ S, (conjAut n K D * fieldAut n K τ)
      (proj n K (Matrix.SpecialLinearGroup.transvection hij c)) =
        proj n K (Matrix.SpecialLinearGroup.transvection hij c)) :
    (∀ c ∈ S, τ c = c) ∧ (D : Matrix (Fin n) (Fin n) K) * single i j 1 =
      single i j 1 * (D : Matrix (Fin n) (Fin n) K) := by
  set M : Matrix (Fin n) (Fin n) K := (D : Matrix (Fin n) (Fin n) K) with hM
  set Mi : Matrix (Fin n) (Fin n) K := ((D⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    with hMi
  have h2' : Mi * M = 1 := by rw [hM, hMi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h1M : M * Mi = 1 := by rw [hM, hMi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have key : ∀ c ∈ S, M * single i j (τ c) * Mi = single i j c := by
    intro c hc
    have h1 := h c hc
    rw [MulAut.mul_apply, fieldAut_proj_transvection, conjAut_proj] at h1
    have h3 := eq_of_proj_eq_of_pow_char (p := p)
      (by rw [← map_pow, transvection_pow_char, map_one]) (transvection_pow_char hij c) h1
    have h4 := congrArg (fun g : Matrix.SpecialLinearGroup (Fin n) K =>
      (g : Matrix (Fin n) (Fin n) K)) h3
    simp only [CatalogueBHigherLinearAction.slConjugation_matrix,
      Matrix.SpecialLinearGroup.transvection_coe] at h4
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, h1M] at h4
    exact add_left_cancel h4
  have e1 := key 1 hS
  rw [map_one] at e1
  refine ⟨fun c hc => ?_, ?_⟩
  · have e2 := key c hc
    have : single i j (τ c) = (τ c) • single i j (1 : K) := by
      rw [smul_single, smul_eq_mul, mul_one]
    rw [this, Matrix.mul_smul, Matrix.smul_mul, e1, smul_single, smul_eq_mul, mul_one] at e2
    have := congrFun (congrFun e2 i) j
    simpa using this
  · calc M * single i j 1 = M * single i j 1 * Mi * M := by
          rw [Matrix.mul_assoc _ Mi, h2', Matrix.mul_one]
      _ = single i j 1 * M := by rw [e1]

theorem eq_scalar_of_commute_single {D : Matrix (Fin n) (Fin n) K} (a : Fin n)
    (h : ∀ i j : Fin n, i ≠ j → D * single i j 1 = single i j 1 * D) :
    D = Matrix.scalar (Fin n) (D a a) := by
  ext i j
  rw [scalar_apply, diagonal_apply]
  by_cases hij : i = j
  · subst hij
    simp only [↓reduceIte]
    by_cases ha : i = a
    · rw [ha]
    · exact (commute_single_apply (h a i (Ne.symm ha))).1
  · simp only [hij, ↓reduceIte]
    exact (commute_single_apply (h j i (Ne.symm hij))).2.1 i hij

theorem conjAut_eq_one_of_commute_single {D : GL (Fin n) K} (a : Fin n)
    (h : ∀ i j : Fin n, i ≠ j → (D : Matrix (Fin n) (Fin n) K) * single i j 1 =
      single i j 1 * (D : Matrix (Fin n) (Fin n) K)) :
    conjAut n K D = 1 := by
  have hD := eq_scalar_of_commute_single a h
  have h0 : (D : Matrix (Fin n) (Fin n) K) a a ≠ 0 := by
    intro h0
    have hdet : IsUnit (D : Matrix (Fin n) (Fin n) K).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 D.isUnit
    have hD0 : (D : Matrix (Fin n) (Fin n) K) = 0 := by
      rw [hD, h0, map_zero]
    have : Nonempty (Fin n) := ⟨a⟩
    rw [hD0, det_zero] at hdet
    exact not_isUnit_zero hdet
  have hDs : D = GeneralLinearGroup.scalar (Fin n) (Units.mk0 _ h0) := Units.ext (hD.trans rfl)
  rw [hDs, conjAut_scalar]

theorem eq_bot_of_oddCoreIn {X G : Type} [Group X] [Group G] [Finite X] {ψ : X →* G}
    (hψ : Function.Injective ψ) {t : X} (h : oddCoreIn ψ.range (ψ t) = ⊥) {Y : Subgroup X}
    (hYO : Y ≤ oddCentralizerCore t) : Y = ⊥ := by
  apply (map_eq_bot_iff_of_injective _ hψ).1
  rw [eq_bot_iff, ← h, ← map_oddCentralizerCore_of_injective hψ]
  exact map_mono hYO

end CFSG.ComponentClassification.Burgoyne.PSL
