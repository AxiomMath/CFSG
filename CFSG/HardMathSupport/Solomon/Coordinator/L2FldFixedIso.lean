module

public import CFSG.HardMathSupport.Solomon.Coordinator.L2FldFixedBasic
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open (StatedProj StatedSL StatedScalars)
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns

section

variable {F : Type} [Field F]

theorem l2fld_det_statedSL_two {A : Matrix.GeneralLinearGroup (Fin 2) F} (h : A ∈ StatedSL 2 F) :
    (A : Matrix (Fin 2) (Fin 2) F).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSL h

@[expose] noncomputable def l2fld_subGL2 (K₀ : Subfield F) :
    Matrix.GeneralLinearGroup (Fin 2) K₀ →* Matrix.GeneralLinearGroup (Fin 2) F :=
  Matrix.GeneralLinearGroup.map K₀.subtype

theorem l2fld_subGL2_mem (K₀ : Subfield F) {g : Matrix.GeneralLinearGroup (Fin 2) K₀}
    (hg : g ∈ StatedSL 2 K₀) : l2fld_subGL2 K₀ g ∈ StatedSL 2 F := by
  have hmap : (StatedSL 2 K₀).map (l2fld_subGL2 K₀) ≤ StatedSL 2 F := by
    rw [StatedSL, MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨B, hB, rfl⟩
    have h1 : (B : Matrix (Fin 2) (Fin 2) K₀).det = 1 := hB
    show ((l2fld_subGL2 K₀ B : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1
    have : ((l2fld_subGL2 K₀ B : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        (K₀.subtype.mapMatrix (B : Matrix (Fin 2) (Fin 2) K₀)) := rfl
    rw [this, ← RingHom.map_det, h1, map_one]
  exact hmap ⟨g, hg, rfl⟩

@[expose] noncomputable def l2fld_subSL2 (K₀ : Subfield F) : ↥(StatedSL 2 K₀) →* ↥(StatedSL 2 F) :=
  ((l2fld_subGL2 K₀).comp (StatedSL 2 K₀).subtype).codRestrict (StatedSL 2 F)
    fun x => l2fld_subGL2_mem K₀ x.2

theorem l2fld_subSL2_apply (K₀ : Subfield F) (x : ↥(StatedSL 2 K₀)) (i j : Fin 2) :
    (((l2fld_subSL2 K₀ x : ↥(StatedSL 2 F)) : Matrix.GeneralLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) i j =
      (((x : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) i j : F) := rfl

@[expose] noncomputable def l2fld_nuSL2 (K₀ : Subfield F) :
    ↥(StatedSL 2 K₀) →* StatedProj (StatedSL 2 F) :=
  (QuotientGroup.mk' ((StatedScalars (Fin 2) F).subgroupOf (StatedSL 2 F))).comp (l2fld_subSL2 K₀)

theorem l2fld_entries_fixed_of_smul {σ : F ≃+* F} (hσ3 : σ ^ 3 = 1) (A : ↥(StatedSL 2 F)) (c : Fˣ)
    (hc : ((A : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).map σ =
      (c : F) • ((A : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) :
    ∀ i j, σ (((A : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j) =
      ((A : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j := by
  have hdet := l2fld_det_statedSL_two A.2
  set M := ((A : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) with hM
  have hc2 : (c : F) ^ 2 = 1 := by
    have h1 : (M.map σ).det = σ M.det := by
      have := RingHom.map_det σ.toRingHom M
      simpa using this.symm
    rw [hc, Matrix.det_smul, hdet] at h1
    simpa using h1
  have hij : ∃ i j, M i j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    rw [Matrix.det_fin_two, hcon 0 0, hcon 1 1, hcon 0 1, hcon 1 0] at hdet
    simp at hdet
  obtain ⟨i₀, j₀, hne⟩ := hij
  have hc1 : (c : F) = 1 := by
    rcases eq_or_eq_neg_of_sq_eq_sq (c : F) 1 (by rw [hc2, one_pow]) with h | h
    · exact h
    · have h1 : σ (M i₀ j₀) = -M i₀ j₀ := by
        have := congrFun (congrFun hc i₀) j₀
        simpa [h] using this
      have h2 : (σ ^ 3) (M i₀ j₀) = -M i₀ j₀ := by
        have e3 : (σ ^ 3) (M i₀ j₀) = σ (σ (σ (M i₀ j₀))) := by simp [pow_succ]
        rw [e3]; simp [h1]
      rw [hσ3] at h2
      have h3 : (2 : F) * M i₀ j₀ = 0 := by
        have : M i₀ j₀ = -M i₀ j₀ := h2
        linear_combination this
      have h4 : (2 : F) = 0 := by
        rcases mul_eq_zero.1 h3 with h | h
        · exact h
        · exact absurd h hne
      rw [h]
      linear_combination (-1 : F) * h4
  intro i j
  have := congrFun (congrFun hc i) j
  simpa [hc1] using this

theorem l2fld_exists_subSL2_eq {σ : F ≃+* F} (K₀ : Subfield F) (hK₀ : ∀ c, c ∈ K₀ ↔ σ c = c)
    (A : ↥(StatedSL 2 F))
    (hfix : ∀ i j, σ (((A : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j) =
      ((A : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j) :
    ∃ x : ↥(StatedSL 2 K₀), l2fld_subSL2 K₀ x = A := by
  set M : Matrix (Fin 2) (Fin 2) K₀ := Matrix.of fun i j =>
    ⟨((A : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j,
      (hK₀ _).2 (hfix i j)⟩ with hMdef
  have hMA : K₀.subtype.mapMatrix M =
      ((A : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    ext i j; rfl
  have hdet : M.det = 1 := by
    apply K₀.subtype.injective
    rw [RingHom.map_det K₀.subtype M, hMA, l2fld_det_statedSL_two A.2, map_one]
  have hne : M.det ≠ 0 := by rw [hdet]; exact one_ne_zero
  refine ⟨⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hne, Subgroup.subset_closure ?_⟩, ?_⟩
  · show (Matrix.GeneralLinearGroup.mkOfDetNeZero M hne : Matrix (Fin 2) (Fin 2) K₀).det = 1
    exact hdet
  · apply Subtype.ext
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rfl

theorem l2fld_range_nuSL2 {σ : F ≃+* F} (hσ3 : σ ^ 3 = 1) (K₀ : Subfield F)
    (hK₀ : ∀ c, c ∈ K₀ ↔ σ c = c) {φ : MulAut (StatedProj (StatedSL 2 F))}
    (hφ : IsEntrywiseAutPSLn 2 σ φ) : (l2fld_nuSL2 K₀).range = fixSub φ := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [mem_fixSub]
    show φ (QuotientGroup.mk (l2fld_subSL2 K₀ x)) = QuotientGroup.mk (l2fld_subSL2 K₀ x)
    apply hφ (l2fld_subSL2 K₀ x) (l2fld_subSL2 K₀ x)
    ext i j
    simp only [Matrix.map_apply]
    rw [l2fld_subSL2_apply]
    exact ((hK₀ _).1 (((x : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) i j).2).symm
  · intro y hy
    obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective y
    have hmem : Matrix.GeneralLinearGroup.map σ.toRingHom (A : Matrix.GeneralLinearGroup (Fin 2) F) ∈
        StatedSL 2 F := by
      refine Subgroup.subset_closure ?_
      show ((Matrix.GeneralLinearGroup.map σ.toRingHom (A : Matrix.GeneralLinearGroup (Fin 2) F) :
        Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1
      have : ((Matrix.GeneralLinearGroup.map σ.toRingHom (A : Matrix.GeneralLinearGroup (Fin 2) F) :
        Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
          σ.toRingHom.mapMatrix ((A : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) :=
        rfl
      rw [this, ← RingHom.map_det, l2fld_det_statedSL_two A.2, map_one]
    let A' : ↥(StatedSL 2 F) := ⟨_, hmem⟩
    have h1 : φ (QuotientGroup.mk A) = QuotientGroup.mk A' := hφ A A' rfl
    have h2 : φ (QuotientGroup.mk A) = QuotientGroup.mk A := mem_fixSub.1 hy
    obtain ⟨c, hc⟩ := (l2fld_mk_eq_iff_smul A A').1 (h2.symm.trans h1)
    have hfix := l2fld_entries_fixed_of_smul hσ3 A c hc
    obtain ⟨x, hx⟩ := l2fld_exists_subSL2_eq K₀ hK₀ A hfix
    exact ⟨x, by simp [l2fld_nuSL2, hx]⟩

theorem l2fld_ker_nuSL2 (K₀ : Subfield F) :
    (l2fld_nuSL2 K₀).ker = (StatedScalars (Fin 2) K₀).subgroupOf (StatedSL 2 K₀) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    have h1 : ((l2fld_subSL2 K₀ x : ↥(StatedSL 2 F)) : Matrix.GeneralLinearGroup (Fin 2) F) ∈
        StatedScalars (Fin 2) F :=
      Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h)
    obtain ⟨c, hc⟩ := h1
    have hentry : ∀ i j, ((((x : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀)
        i j : K₀) : F) = if i = j then (c : F) else 0 := by
      intro i j
      have := (Matrix.GeneralLinearGroup.ext_iff _ _).1 hc i j
      rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply] at this
      rw [← l2fld_subSL2_apply]
      exact this.symm
    have h00 := hentry 0 0
    simp only [ite_true] at h00
    have hcK : (c : F) ∈ K₀ := by rw [← h00]; exact (((x : Matrix.GeneralLinearGroup (Fin 2) K₀) :
      Matrix (Fin 2) (Fin 2) K₀) 0 0).2
    have hc0 : (⟨(c : F), hcK⟩ : K₀) ≠ 0 := fun h => c.ne_zero (congrArg Subtype.val h)
    refine ⟨Units.mk0 ⟨(c : F), hcK⟩ hc0, ?_⟩
    apply Units.ext
    ext i j
    rw [hentry i j, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs <;> simp
  · rintro ⟨c, hc⟩
    apply (QuotientGroup.eq_one_iff _).2
    refine Subgroup.mem_subgroupOf.2 ⟨Units.map (K₀.subtype : K₀ →+* F).toMonoidHom c, ?_⟩
    apply Units.ext
    ext i j
    have := (Matrix.GeneralLinearGroup.ext_iff _ _).1 hc i j
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply] at this ⊢
    show _ = (((x : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) i j : F)
    rw [← this]
    split_ifs <;> simp

theorem l2fld_fixSub_entrywise_iso {σ : F ≃+* F} (hσ3 : σ ^ 3 = 1) (K₀ : Subfield F)
    (hK₀ : ∀ c, c ∈ K₀ ↔ σ c = c) {φ : MulAut (StatedProj (StatedSL 2 F))}
    (hφ : IsEntrywiseAutPSLn 2 σ φ) :
    Nonempty (StatedProj (StatedSL 2 ↥K₀) ≃* ↥(fixSub φ)) :=
  ⟨((QuotientGroup.quotientMulEquivOfEq (l2fld_ker_nuSL2 K₀).symm).trans
    (QuotientGroup.quotientKerEquivRange (l2fld_nuSL2 K₀))).trans
      (MulEquiv.subgroupCongr (l2fld_range_nuSL2 hσ3 K₀ hK₀ hφ))⟩

end

end CFSG.HardMathSupport.Solomon.Coordinator
