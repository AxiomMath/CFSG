module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneLargeTorusCore
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneUnitaryInner
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneUnitaryFrame
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneUnitaryOvergroup

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane

open Matrix Matrix.ProjGenLinGroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag UnitaryHigher
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)

section Reindex

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {r ε : ℕ}
  {κ : Type} [Fintype κ] [DecidableEq κ] (e : HypIndex r ε ≃ κ)

omit [Fintype κ] [DecidableEq κ] in
theorem conjT_reindex_hypGram :
    ((reindex e e (hypGram r ε K)).map h.bar)ᵀ = reindex e e (hypGram r ε K) := by
  have h1 := hypGram_conjTranspose h (r := r) (ε := ε)
  calc ((reindex e e (hypGram r ε K)).map h.bar)ᵀ =
        reindex e e (((hypGram r ε K).map h.bar)ᵀ) := by
        ext i j
        rfl
    _ = reindex e e (hypGram r ε K) := by rw [h1]

theorem reindex_hypGram_mul_self :
    reindex e e (hypGram r ε K) * reindex e e (hypGram r ε K) = 1 := by
  rw [← coe_reindexAlgEquiv K K e, ← map_mul, hypGram_mul_self, map_one]

theorem reindex_similitude {A : GL (HypIndex r ε) K} (hA : A ∈ linearSimilitudes h r ε) :
    ∃ μ : K, μ ≠ 0 ∧ (((glReindex e A : GL κ K) : Matrix κ κ K).map h.bar)ᵀ *
      reindex e e (hypGram r ε K) * (glReindex e A : GL κ K) =
        μ • reindex e e (hypGram r ε K) := by
  obtain ⟨μ, hμ0, -, hμ⟩ := mem_linearSimilitudes.1 hA
  refine ⟨μ, hμ0, ?_⟩
  rw [coe_glReindex, reindex_conjTranspose_mul_mul, hμ]
  ext i j
  rfl

theorem reindex_isometry {A : GL (HypIndex r ε) K} (hA : A ∈ hypUnitary h r ε) :
    (((glReindex e A : GL κ K) : Matrix κ κ K).map h.bar)ᵀ * reindex e e (hypGram r ε K) *
      (glReindex e A : GL κ K) = reindex e e (hypGram r ε K) := by
  rw [coe_glReindex, reindex_conjTranspose_mul_mul, mem_hypUnitary.1 hA]

theorem symm_glReindex_mem_hypUnitary {M : GL κ K}
    (hM : ((M : Matrix κ κ K).map h.bar)ᵀ * reindex e e (hypGram r ε K) * M =
      reindex e e (hypGram r ε K)) :
    (glReindex e).symm M ∈ hypUnitary h r ε := by
  rw [mem_hypUnitary]
  apply (reindex e e).injective
  rw [← reindex_conjTranspose_mul_mul, ← coe_glReindex, MulEquiv.apply_symm_apply]
  exact hM

theorem det_symm_glReindex (M : GL κ K) :
    (((glReindex e).symm M : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K).det =
      (M : Matrix κ κ K).det := by
  rw [← det_reindex_self e, ← coe_glReindex, MulEquiv.apply_symm_apply]

end Reindex

section Norm

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem conjT_smul {ι : Type*} (c : K) (M : Matrix ι ι K) :
    ((c • M).map h.bar)ᵀ = h.bar c • (M.map h.bar)ᵀ := by
  ext i j
  simp [map_mul]

theorem norm_eq_one_of_commutator {ι : Type*} [Fintype ι] [DecidableEq ι] (i₀ : ι)
    {G X Y : Matrix ι ι K} (hGG : G * G = 1) (hX : (X.map h.bar)ᵀ * G * X = G) {μ : K}
    (hμ : μ ≠ 0) (hY : (Y.map h.bar)ᵀ * G * Y = μ • G) {ζ : K} (hXY : X * Y = ζ • (Y * X)) :
    h.norm ζ = 1 := by
  have h1 : ((X * Y).map h.bar)ᵀ * G * (X * Y) = μ • G := by
    rw [conjTranspose_mul_mul, hX, hY]
  have h2 : ((ζ • (Y * X)).map h.bar)ᵀ * G * (ζ • (Y * X)) = (h.norm ζ * μ) • G := by
    have e1 : ((ζ • (Y * X)).map h.bar)ᵀ * G * (ζ • (Y * X)) =
        (h.bar ζ * ζ) • (((Y * X).map h.bar)ᵀ * G * (Y * X)) := by
      rw [conjT_smul]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm]
    rw [e1, conjTranspose_mul_mul, hY, Matrix.mul_smul, Matrix.smul_mul, hX, smul_smul,
      UnitaryFieldData.norm, mul_comm (h.bar ζ) ζ]
  rw [hXY] at h1
  rw [h1] at h2
  have h3 := congrArg (· * G) h2
  simp only [Matrix.smul_mul, hGG] at h3
  have h4 := congrFun (congrFun h3 i₀) i₀
  simp only [Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one] at h4
  have h5 : (h.norm ζ - 1) * μ = 0 := by linear_combination -h4
  exact sub_eq_zero.1 ((mul_eq_zero.1 h5).resolve_right hμ)

end Norm

variable {r f : ℕ} {K : Type} [Field K]

theorem unitary_projective_nonabelian_plane_delta_centralizes_large_torus
    (h : UnitaryFieldData r f K) {p a : ℕ} (hp : p.Prime) (hpa : p = 2 * a + 1) (ha : 1 ≤ a)
    (hp5 : 5 ≤ p) (D : Subgroup (MulAut (hypPSU h a 1)))
    (hDI : D ≤ linearSimAutGroup h ha le_rfl) (hDab : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x)
    (hDp : ∀ x ∈ D, x ^ p = 1) (hcard : Nat.card D = p ^ 2)
    (hna : ¬ ∀ A ∈ D.comap (linearSimAut h ha le_rfl), ∀ B ∈ D.comap (linearSimAut h ha le_rfl),
      A * B = B * A) :
    D ⊓ (MulAut.conj : hypPSU h a 1 →* MulAut (hypPSU h a 1)).range ≠ ⊥ ∧
      ∀ d ∈ D ⊓ (MulAut.conj : hypPSU h a 1 →* MulAut (hypPSU h a 1)).range, d ≠ 1 →
        ∃ U : Subgroup (MulAut (hypPSU h a 1)),
          U ≤ linearSimAutGroup h ha le_rfl ⊓ Subgroup.centralizer {d} ∧
          (∀ x ∈ U, ∀ y ∈ U, x * y = y * x) ∧ (∀ x ∈ U, x ^ p = 1) ∧
          Nat.card U = p ^ (p - 1) ∧
          (U.subgroupOf (linearSimAutGroup h ha le_rfl ⊓
            Subgroup.centralizer {d})).Characteristic ∧
          (U.subgroupOf (Subgroup.centralizer {d})).Normal ∧ d ∈ U ∧
          (∃ k, p - 2 ≤ k ∧ Nat.card (U ⊓ (MulAut.conj : hypPSU h a 1 →*
            MulAut (hypPSU h a 1)).range : Subgroup (MulAut (hypPSU h a 1))) = p ^ k) ∧
          (∀ x ∈ localDelta p ⊤ D, ∀ u ∈ U, x * u = u * x) ∧
          ∀ H : Subgroup (MulAut (hypPSU h a 1)),
            (MulAut.conj : hypPSU h a 1 →* MulAut (hypPSU h a 1)).range ≤ H → D ≤ H →
            ∀ x ∈ localDelta p H D, ∀ v ∈ (U ⊓ (MulAut.conj : hypPSU h a 1 →*
              MulAut (hypPSU h a 1)).range : Subgroup (MulAut (hypPSU h a 1))),
              x * v = v * x := by
  classical
  have := finite_mulAut_hypPSU h a 1
  have := h.finite
  have : NeZero p := ⟨hp.ne_zero⟩
  have hn : 3 ≤ 2 * a + 1 := by omega
  have hqa : ¬(2 * a + 1 = 3 ∧ r ^ f = 2) := fun ⟨h3, _⟩ => by omega
  set Inn := (MulAut.conj : hypPSU h a 1 →* MulAut (hypPSU h a 1)).range with hInn
  have hInnN : Inn.Normal := inner_normal _
  have hIN : (linearSimAut h ha le_rfl).range.Normal :=
    linearSimAutGroup_normal h ha le_rfl hn hqa
  have hDInn : D ⊓ Inn ≠ ⊥ := by
    have := isCyclic_map_linearSimAutGroup h ha le_rfl hn
    have hmap : D.map (QuotientGroup.mk' (inner (hypPSU h a 1))) ≤
        (linearSimAutGroup h ha le_rfl).map (QuotientGroup.mk' (inner (hypPSU h a 1))) :=
      Subgroup.map_mono hDI
    have := Subgroup.isCyclic_of_le hmap
    obtain ⟨d, hdD, hd1, hdker⟩ := exists_ne_one_ker_of_isCyclic hp hDp hcard _ this
    intro hbot
    have hdInn : d ∈ Inn := (QuotientGroup.eq_one_iff d).1 hdker
    have hmem : d ∈ D ⊓ Inn := Subgroup.mem_inf.2 ⟨hdD, hdInn⟩
    rw [hbot] at hmem
    exact hd1 hmem
  refine ⟨hDInn, fun d hd hd1 => ?_⟩
  obtain ⟨hdD, ⟨s, hs⟩⟩ := Subgroup.mem_inf.1 hd
  obtain ⟨g, rfl⟩ := hypProj_surjective h a 1 s
  have hcardI : Fintype.card (HypIndex a 1) = p := by
    change Fintype.card (Fin a ⊕ Fin 1 ⊕ Fin a) = p
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  set e : HypIndex a 1 ≃ Fin p := Fintype.equivFinOfCardEq hcardI
  set τ : linearSimilitudes h a 1 →* GL (Fin p) K :=
    (glReindex e).toMonoidHom.comp (linearSimilitudes h a 1).subtype with hτdef
  have hτ : Function.Injective τ :=
    (glReindex e).injective.comp (linearSimilitudes h a 1).subtype_injective
  have hker : ∀ x, linearSimAut h ha le_rfl x = 1 ↔
      ∃ u : Kˣ, τ x = GeneralLinearGroup.scalar (Fin p) u :=
    fun x => linearSimAut_eq_one_iff_reindex h ha le_rfl hn e x
  set A : linearSimilitudes h a 1 :=
    ⟨g, hypUnitary_le_linearSimilitudes h (hypSU_le_hypUnitary h g.2)⟩ with hAdef
  have hAd : linearSimAut h ha le_rfl A = MulAut.conj (hypProj h a 1 g) :=
    linearSimAut_hypSU h ha le_rfl g
  rw [hs] at hAd
  have hAdet : ((τ A : GL (Fin p) K) : Matrix (Fin p) (Fin p) K).det = 1 := by
    change (reindex e e ((g : GL (HypIndex a 1) K) : Matrix (HypIndex a 1) (HypIndex a 1) K)).det
      = 1
    rw [det_reindex_self]
    exact g.2.2
  have hframe : ∀ (P : GL (Fin p) K) (ζ : K) (B : linearSimilitudes h a 1), IsPrimitiveRoot ζ p →
      ((τ A : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) * (τ B : GL (Fin p) K) =
        ζ • (((τ B : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) * (τ A : GL (Fin p) K)) →
      ((τ A : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) = (P : Matrix (Fin p) (Fin p) K) *
        diagonal (fun i : Fin p => ζ ^ (i : ℕ)) *
          ((P⁻¹ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) →
      ∃ P' : GL (Fin p) K, ((τ A : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) =
          (P' : Matrix (Fin p) (Fin p) K) * diagonal (fun i : Fin p => ζ ^ (i : ℕ)) *
            ((P'⁻¹ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) ∧
        omegaTorus P' ≤ (projHom τ).range ∧
        ∀ y ∈ detOneTorus P', ∀ hy : y ∈ (projHom τ).range,
          rangeLift (linearSimAut h ha le_rfl) τ hker ⟨y, hy⟩ ∈ Inn := by
    intro P ζ B hζ hAB hP
    have hX : (((τ A : GL (Fin p) K) : Matrix (Fin p) (Fin p) K).map h.bar)ᵀ *
        reindex e e (hypGram a 1 K) * (τ A : GL (Fin p) K) = reindex e e (hypGram a 1 K) :=
      reindex_isometry h e (hypSU_le_hypUnitary h g.2)
    obtain ⟨μ, hμ0, hY⟩ := reindex_similitude h e B.2
    have hNζ : h.norm ζ = 1 :=
      norm_eq_one_of_commutator h 0 (reindex_hypGram_mul_self e) hX hμ0 hY hAB
    have hGG := reindex_hypGram_mul_self (K := K) e
    obtain ⟨P', hP', hP'G⟩ := exists_orthonormal_frame h (conjT_reindex_hypGram h e)
      ⟨⟨_, _, hGG, hGG⟩, rfl⟩ hX hζ hNζ hP
    have hpull : ∀ x : Fin p → Kˣ, (∀ i, ((x i : Kˣ) : K) ^ p = 1) →
        (glReindex e).symm (P' * TauCeti.diagGL x * P'⁻¹) ∈ hypUnitary h a 1 := fun x hx =>
      symm_glReindex_mem_hypUnitary h e (isometry_conj_diagGL h hP'G fun i =>
        norm_eq_one_of_pow_eq_one h hζ hNζ (hx i))
    refine ⟨P', hP', ?_, ?_⟩
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := mem_omegaTorus.1 hy
      obtain ⟨x', hx'def⟩ : ∃ x' : Fin p → Kˣ, x' = x * fun _ => (x 0)⁻¹ := ⟨_, rfl⟩
      have hx' : ∀ i, ((x' i : Kˣ) : K) ^ p = 1 := fun i => by
        rw [hx'def, ← Units.val_pow_eq_pow_val]
        simp only [Pi.mul_apply, mul_pow, inv_pow, hx i 0, mul_inv_cancel, Units.val_one]
      have hxx' : torusHom P' x = torusHom P' x' := by
        rw [hx'def, map_mul, (torusHom_eq_one_iff P' (fun _ => (x 0)⁻¹)).2 fun _ _ => rfl,
          mul_one]
      refine ⟨⟨_, hypUnitary_le_linearSimilitudes h (hpull _ hx')⟩, ?_⟩
      rw [hxx', torusHom_apply]
      change mk (glReindex e ((glReindex e).symm _)) = _
      rw [MulEquiv.apply_symm_apply]
    · intro y hy hyJ
      obtain ⟨f₀, hf₀, rfl⟩ := mem_detOneTorus hy
      have hMU := hpull (fun i => (f₀ i : Kˣ)) fun i => by
        show ((f₀ i : Kˣ) : K) ^ p = 1
        rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 (f₀ i).2, Units.val_one]
      have hMdet : (((glReindex e).symm (P' * TauCeti.diagGL (fun i => (f₀ i : Kˣ)) * P'⁻¹) :
          GL (HypIndex a 1) K) : Matrix (HypIndex a 1) (HypIndex a 1) K).det = 1 := by
        rw [det_symm_glReindex, Units.val_mul, Units.val_mul, Matrix.coe_units_inv,
          det_conj P'.isUnit, TauCeti.diagGL_coe, det_diagonal]
        exact hf₀
      have hSU : (glReindex e).symm (P' * TauCeti.diagGL (fun i => (f₀ i : Kˣ)) * P'⁻¹) ∈
          hypSU h a 1 := ⟨hMU, hMdet⟩
      have hlift : (⟨_, hyJ⟩ : (projHom τ).range) =
          (projHom τ).rangeRestrict ⟨_, hypUnitary_le_linearSimilitudes h hMU⟩ := by
        apply Subtype.ext
        change _ = mk (glReindex e ((glReindex e).symm _))
        rw [MulEquiv.apply_symm_apply]
      rw [hlift, rangeLift_apply]
      exact ⟨hypProj h a 1 ⟨_, hSU⟩, (linearSimAut_hypSU h ha le_rfl ⟨_, hSU⟩).symm⟩
  obtain ⟨U, hUC, hUab, hUp, hUcard, hchar, hnormal, hdU, hVrank, hΔ, hΔH⟩ :=
    large_torus_of_frame hp hp5 (linearSimAut h ha le_rfl) τ hτ hker Inn hInnN hIN D hDI hDab
      hDp hcard hna hdD hd1 hAd hAdet hframe
  exact ⟨U, hUC, hUab, hUp, hUcard, hchar, hnormal, hdU, hVrank, hΔ, hΔH⟩

end CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane
