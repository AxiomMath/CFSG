module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15InnerField
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldFixedBasis

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

private def descent_restrictAddEquiv {F M : Type*} [Field F] [AddCommGroup M] [Module F M]
    (T : M ≃+ M) (hT2 : ∀ m : M, T (T m) = m) (Y : Submodule F M)
    (hY : ∀ y ∈ Y, T y ∈ Y) : Y ≃+ Y where
  toFun y := ⟨T y, hY y y.2⟩
  invFun y := ⟨T y, hY y y.2⟩
  left_inv y := by
    apply Subtype.ext
    exact hT2 (y : M)
  right_inv y := by
    apply Subtype.ext
    exact hT2 (y : M)
  map_add' y z := by
    apply Subtype.ext
    exact map_add T (y : M) (z : M)

@[simp] private lemma descent_restrictAddEquiv_apply {F M : Type*} [Field F] [AddCommGroup M] [Module F M]
    (T : M ≃+ M) (hT2 : ∀ m : M, T (T m) = m) (Y : Submodule F M)
    (hY : ∀ y ∈ Y, T y ∈ Y) (y : Y) :
    ((descent_restrictAddEquiv T hT2 Y hY y : Y) : M) = T y :=
  rfl

private lemma descent_restrictAddEquiv_involutive {F M : Type*} [Field F] [AddCommGroup M] [Module F M]
    (T : M ≃+ M) (hT2 : ∀ m : M, T (T m) = m) (Y : Submodule F M)
    (hY : ∀ y ∈ Y, T y ∈ Y) :
    ∀ y : Y, descent_restrictAddEquiv T hT2 Y hY (descent_restrictAddEquiv T hT2 Y hY y) = y := by
  intro y
  apply Subtype.ext
  exact hT2 (y : M)

private lemma descent_restrictAddEquiv_smul {F M : Type*} [Field F] [AddCommGroup M] [Module F M]
    (T : M ≃+ M) (hT2 : ∀ m : M, T (T m) = m) (Y : Submodule F M)
    (hY : ∀ y ∈ Y, T y ∈ Y) (σ : F ≃+* F)
    (hT : ∀ (c : F) (m : M), T (c • m) = σ c • T m) (c : F) (y : Y) :
    descent_restrictAddEquiv T hT2 Y hY (c • y) =
      σ c • descent_restrictAddEquiv T hT2 Y hY y := by
  apply Subtype.ext
  simpa using hT c (y : M)

theorem card_submodule_eq_sq_card_fixed {F : Type*} [Field F] [Finite F] [CharP F 2]
    {σ : F ≃+* F} (hσ : ∃ c : F, σ c ≠ c) (hσ2 : ∀ c : F, σ (σ c) = c)
    {M : Type*} [AddCommGroup M] [Module F M] [Finite M] (T : M ≃+ M)
    (hT : ∀ (c : F) (m : M), T (c • m) = σ c • T m) (hT2 : ∀ m : M, T (T m) = m)
    (Y : Submodule F M) (hY : ∀ y ∈ Y, T y ∈ Y) :
    Nat.card Y = Nat.card {y : M // y ∈ Y ∧ T y = y} ^ 2 := by
  exact (CFSG.LocalAnalysis.RankThreeUC.S15.InnerField.card_fix_sq_of_stable
    (K := F) (V := M) (σ : F →+* F) hσ2 hσ T hT hT2 Y hY).symm

theorem span_fixed_eq_of_semilinear_involution {F : Type*} [Field F] [Finite F] [CharP F 2]
    {σ : F ≃+* F} (hσ : ∃ c : F, σ c ≠ c) (hσ2 : ∀ c : F, σ (σ c) = c)
    {M : Type*} [AddCommGroup M] [Module F M] [Finite M] (T : M ≃+ M)
    (hT : ∀ (c : F) (m : M), T (c • m) = σ c • T m) (hT2 : ∀ m : M, T (T m) = m)
    (Y : Submodule F M) (hY : ∀ y ∈ Y, T y ∈ Y) :
    Submodule.span F {m : M | m ∈ Y ∧ T m = m} = Y := by
  classical
  let s : Y ≃+ Y := descent_restrictAddEquiv T hT2 Y hY
  have hss : ∀ y : Y, s (s y) = y := descent_restrictAddEquiv_involutive T hT2 Y hY
  have hs : ∀ (c : F) (y : Y), s (c • y) = σ c • s y :=
    descent_restrictAddEquiv_smul T hT2 Y hY σ hT
  have hsigma : σ ^ 2 = 1 := by
    ext c
    simpa [pow_two] using hσ2 c
  have hne : σ ≠ 1 := by
    obtain ⟨c, hc⟩ := hσ
    intro h
    exact hc (by simpa using congrArg (fun τ : F ≃+* F => τ c) h)
  have hspan : Submodule.span F {y : Y | s y = y} = ⊤ :=
    CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField.semilinear_fixed_span_eq_top
      σ hsigma hne s hss hs
  have hmap := congrArg (Submodule.map (Y.subtype : Y →ₗ[F] M)) hspan
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype] at hmap
  have himage : (Y.subtype '' {y : Y | s y = y}) = {m : M | m ∈ Y ∧ T m = m} := by
    ext m
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      have h := congrArg (fun z : Y => (z : M)) hy
      simpa [s] using h
    · rintro ⟨hmY, hmT⟩
      refine ⟨⟨m, hmY⟩, ?_, rfl⟩
      apply Subtype.ext
      simpa [s] using hmT
  rw [himage] at hmap
  exact hmap

end CFSG.LocalAnalysis.RankThreeUC.S15

end
