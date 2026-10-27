module

public import CFSG.Quasithin.Background.SmithB42Sp4Ident
public import CFSG.Quasithin.Background.SmithB42Sp4Nat

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open
open CFSG.Quasithin.B42Sp4 (spM)
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain

private noncomputable def b2natural_piAntiIdx (F : Type) [AddCommGroup F] :
    (Fin 4 → F) ≃+ (Fin 2 ⊕ Fin 2 → F) where
  toFun x := x ∘ antiIdx
  invFun x := x ∘ antiIdx.symm
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp
  map_add' x y := rfl

private theorem b2natural_piAntiIdx_apply {F : Type} [AddCommGroup F]
    (x : Fin 4 → F) (a : Fin 2 ⊕ Fin 2) :
    b2natural_piAntiIdx F x a = x (antiIdx a) := rfl

private theorem b2natural_submatrix_mulVec_antiIdx {F : Type} [Field F]
    (M : Matrix (Fin 4) (Fin 4) F) (v : Fin 4 → F) :
    (M.submatrix antiIdx antiIdx).mulVec (b2natural_piAntiIdx F v) = (M.mulVec v) ∘ antiIdx := by
  funext a
  rw [Matrix.submatrix_mulVec_equiv M (b2natural_piAntiIdx F v) antiIdx antiIdx]
  have h : (b2natural_piAntiIdx F v) ∘ antiIdx.symm = v := by funext i; simp [b2natural_piAntiIdx]
  rw [h]

private theorem b2natural_spM_antiSpEquiv {F : Type} [Field F] [CharP F 2] (γ : antiSp F) :
    spM (antiSpEquiv F γ) = (glMat γ).submatrix antiIdx antiIdx :=
  spMat_antiSpEquiv γ

theorem exists_natural_statedSp_of_offender
    {F : Type} [Field F] [CharP F 2] [Fintype F] {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
    (π : StatedSp 2 F →* (M ≃ₗ[ZMod 2] M)) (hπ : Function.Injective π) (hnt : Nontrivial M)
    (hirr : ∀ U : Submodule (ZMod 2) M, (∀ g, ∀ u ∈ U, π g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (A : Subgroup (M ≃ₗ[ZMod 2] M)) (hnorm : ∀ a ∈ A, ∀ x, ∃ y, a * π x * a⁻¹ = π y)
    (hAe : CFSG.IsElementaryAbelian 2 A) (hA1 : A ≠ ⊥)
    (hoff : Nat.card M ≤ Nat.card A * Nat.card {m : M // ∀ a ∈ A, a m = m}) :
    ∃ (α : MulAut (StatedSp 2 F)) (φ : M ≃+ (Fin 2 ⊕ Fin 2 → F)),
      ∀ g w, φ (π g w) = (spM (α g)).mulVec (φ w) := by
  let π' : antiSp F →* (M ≃ₗ[ZMod 2] M) := π.comp (antiSpEquiv F).toMonoidHom
  have hπ' : Function.Injective π' := by
    intro g g' h
    apply (antiSpEquiv F).injective
    apply hπ
    simpa [π'] using h
  have hirr' : ∀ U : Submodule (ZMod 2) M,
      (∀ g, ∀ u ∈ U, π' g u ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    refine hirr U ?_
    intro x u hu
    have h := hU ((antiSpEquiv F).symm x) u hu
    simpa [π'] using h
  have hnorm' : ∀ a ∈ A, ∀ x : antiSp F, ∃ y, a * π' x * a⁻¹ = π' y := by
    intro a ha x
    obtain ⟨y, hy⟩ := hnorm a ha (antiSpEquiv F x)
    exact ⟨(antiSpEquiv F).symm y, by simpa [π'] using hy⟩
  obtain ⟨i, φ₀, hφ₀⟩ :=
    CFSG.Quasithin.B42Sp4.exists_natural_of_offender (F := F) (M := M) (f := n)
      hn hF π' hπ' hnt hirr' A hnorm' hAe hA1 hoff
  let α : MulAut (StatedSp 2 F) :=
    ((antiSpEquiv F).symm).trans (((minorAut F) ^ i).trans (antiSpEquiv F))
  refine ⟨α, φ₀.trans (b2natural_piAntiIdx F), ?_⟩
  intro g w
  let g' : antiSp F := (antiSpEquiv F).symm g
  have hg : antiSpEquiv F g' = g := (antiSpEquiv F).apply_symm_apply g
  have hπg : π g w = π' g' w := by rw [← hg]; rfl
  have hα : α g = antiSpEquiv F ((minorAut F ^ i) g') := rfl
  have hsp : spM (α g) =
      (glMat (((minorAut F ^ i) g' : antiSp F) : GL (Fin 4) F)).submatrix antiIdx antiIdx := by
    rw [hα]
    exact b2natural_spM_antiSpEquiv _
  rw [hπg]
  funext a
  change b2natural_piAntiIdx F (φ₀ (π' g' w)) a =
    (spM (α g)).mulVec (b2natural_piAntiIdx F (φ₀ w)) a
  rw [b2natural_piAntiIdx_apply, hsp, b2natural_submatrix_mulVec_antiIdx, hφ₀ g' w]
  rfl

end CFSG.LocalAnalysis.RankThreeUC.S15

end
