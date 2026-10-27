module

public import CFSG.LinearAlgebra.RootGroupSL.ModelBasic
public import CFSG.LinearAlgebra.RootGroupSL.AutAbs
public import CFSG.LinearAlgebra.RootGroupSL.SchurSL
public import CFSG.LinearAlgebra.RootGroupSL.NotDual

public section

namespace CFSG.LinearAlgebra.RootGroupSL

variable {k E VJ V₀ : Type} [Field k] [Field E] [Algebra k E]
  [AddCommGroup VJ] [Module k VJ] [Module E VJ] [IsScalarTower k E VJ]
  [AddCommGroup V₀] [Module k V₀] [Finite k] [Finite E]
  [Module.Finite k E] [Module.Finite E VJ] [Module.Finite k VJ] [Module.Finite k V₀]

private lemma finrank_k_ge_three (hm : 3 ≤ Module.finrank E VJ) :
    3 ≤ Module.finrank k VJ := by
  have htower : Module.finrank k E * Module.finrank E VJ = Module.finrank k VJ :=
    Module.finrank_mul_finrank k E VJ
  have hE : 1 ≤ Module.finrank k E := Module.finrank_pos
  calc
    3 ≤ Module.finrank E VJ := hm
    _ = 1 * Module.finrank E VJ := (one_mul _).symm
    _ ≤ Module.finrank k E * Module.finrank E VJ := Nat.mul_le_mul_right _ hE
    _ = Module.finrank k VJ := htower

private noncomputable def modelK1Equiv :
    SpecialLinearGroup k VJ ≃* ↥(modelK1 k VJ V₀) :=
  (MonoidHom.ofInjective (blockSLk_injective (k := k) (VJ := VJ) (V₀ := V₀))).trans
    (MulEquiv.subgroupCongr (modelK1_eq_range (k := k) (VJ := VJ) (V₀ := V₀))).symm

private lemma modelK1Equiv_coe (B : SpecialLinearGroup k VJ) :
    ((modelK1Equiv (k := k) (VJ := VJ) (V₀ := V₀) B : ↥(modelK1 k VJ V₀)) :
        SpecialLinearGroup k (VJ × V₀)) = blockSLk k V₀ B := by
  rw [modelK1Equiv, MulEquiv.trans_apply, MulEquiv.subgroupCongr_symm_apply]
  exact MonoidHom.ofInjective_apply _

private lemma diagE_apply (s : Eˣ) (v : VJ) (w : V₀) :
    diagE (k := k) (VJ := VJ) (V₀ := V₀) s (v, w) = ((s : E) • v, w) := rfl

private lemma diagE_inv_apply (s : Eˣ) (v : VJ) (w : V₀) :
    (diagE (k := k) (VJ := VJ) (V₀ := V₀) s)⁻¹ (v, w) =
      (((s⁻¹ : Eˣ) : E) • v, w) := rfl

private lemma diagE_conj_blockSLk_apply (s : Eˣ) (B : SpecialLinearGroup k VJ)
    (v : VJ) (w : V₀) :
    (diagE (k := k) (VJ := VJ) (V₀ := V₀) s * SpecialLinearGroup.toLinearEquiv (blockSLk k V₀ B) *
        (diagE (k := k) (VJ := VJ) (V₀ := V₀) s)⁻¹) (v, w) =
      ((s : E) • B (((s⁻¹ : Eˣ) : E) • v), w) := by
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, diagE_inv_apply, diagE_apply,
    SpecialLinearGroup.toLinearEquiv_apply, blockSLk_apply]

private lemma units_mk0_val (s : E) (hs : s ≠ 0) :
    ((Units.mk0 s hs : Eˣ) : E) = s := rfl

private lemma units_mk0_inv_val (s : E) (hs : s ≠ 0) :
    (((Units.mk0 s hs)⁻¹ : Eˣ) : E) = s⁻¹ := rfl

theorem exists_diagE_of_mulAut_modelK1 (hm : 3 ≤ Module.finrank E VJ)
    (β : MulAut ↥(modelK1 k VJ V₀))
    (hβ : ∀ j : ↥(modelK1 k VJ V₀),
      (j : SpecialLinearGroup k (VJ × V₀)) ∈ modelJ k E VJ V₀ → β j = j) :
    ∃ s : Eˣ, ∀ g : ↥(modelK1 k VJ V₀),
      SpecialLinearGroup.toLinearEquiv ((β g : ↥(modelK1 k VJ V₀)) :
        SpecialLinearGroup k (VJ × V₀)) =
        diagE s * SpecialLinearGroup.toLinearEquiv (g : SpecialLinearGroup k (VJ × V₀)) *
          (diagE s)⁻¹ := by
  classical
  have hk3 : 3 ≤ Module.finrank k VJ := finrank_k_ge_three (k := k) (E := E) (VJ := VJ) hm
  let e : SpecialLinearGroup k VJ ≃* ↥(modelK1 k VJ V₀) :=
    modelK1Equiv (k := k) (VJ := VJ) (V₀ := V₀)
  let α : MulAut (SpecialLinearGroup k VJ) := e.trans (β.trans e.symm)
  have e_alpha : ∀ g : SpecialLinearGroup k VJ, e (α g) = β (e g) := by
    intro g
    simp [α, MulEquiv.trans_apply]
  have e_coe : ∀ B : SpecialLinearGroup k VJ,
      ((e B : ↥(modelK1 k VJ V₀)) : SpecialLinearGroup k (VJ × V₀)) =
        blockSLk k V₀ B := fun B =>
    modelK1Equiv_coe (k := k) (VJ := VJ) (V₀ := V₀) B
  have alpha_restrict : ∀ B : SpecialLinearGroup E VJ,
      α (restrictSL (E := E) (VJ := VJ) k B) = restrictSL (E := E) (VJ := VJ) k B := by
    intro B
    apply e.injective
    rw [e_alpha]
    have hJ : ((e (restrictSL (E := E) (VJ := VJ) k B) : ↥(modelK1 k VJ V₀)) :
        SpecialLinearGroup k (VJ × V₀)) ∈ modelJ k E VJ V₀ := by
      rw [e_coe]
      exact ⟨B, rfl⟩
    have hfix := hβ (e (restrictSL (E := E) (VJ := VJ) k B)) hJ
    rw [hfix]
  obtain ⟨σ, hcase⟩ :=
    exists_semilinear_form_of_mulAut_sl (F := k) (V := VJ) hk3 α
  rcases hcase with ⟨T, hTlin, hTeq⟩ | ⟨T, hTlin, hTeq⟩
  · have hcomm : ∀ (B : SpecialLinearGroup E VJ) (v : VJ), T (B v) = B (T v) := by
      intro B v
      have h1 := hTeq (restrictSL (E := E) (VJ := VJ) k B) v
      rw [alpha_restrict B] at h1
      have h2 : (restrictSL (E := E) (VJ := VJ) k B) (T v) = B (T v) := rfl
      have h3 : (restrictSL (E := E) (VJ := VJ) k B) v = B v := rfl
      rw [h3, h2] at h1
      exact h1.symm
    let S : VJ →+ VJ :=
      { toFun := T
        map_zero' := map_zero T
        map_add' := map_add T }
    have hS : ∀ (g : SpecialLinearGroup E VJ) (v : VJ), S (g v) = g (S v) := by
      intro g v
      exact hcomm g v
    obtain ⟨s, hs⟩ :=
      exists_smul_of_commute_specialLinear (F := E) (V := VJ) (by omega) S hS
    have hsne : s ≠ 0 := by
      intro hs0
      have hnt : Nontrivial VJ :=
        Module.nontrivial_of_finrank_pos (R := E) (M := VJ) (by omega)
      obtain ⟨v, hv⟩ := exists_ne (0 : VJ)
      have hsv : T v = s • v := hs v
      have hTv : T v = T 0 := by
        rw [hsv, hs0, zero_smul, map_zero]
      exact hv (T.injective hTv)
    let u : Eˣ := Units.mk0 s hsne
    refine ⟨u, ?_⟩
    intro g
    set B : SpecialLinearGroup k VJ := e.symm g with hB
    have hg : e B = g := e.apply_symm_apply g
    rw [← hg]
    have hbeta : β (e B) = e (α B) := (e_alpha B).symm
    rw [hbeta]
    rw [show ((e B : ↥(modelK1 k VJ V₀)) : SpecialLinearGroup k (VJ × V₀)) =
        blockSLk k V₀ B from e_coe B]
    apply LinearEquiv.ext
    intro p
    obtain ⟨v, w⟩ := p
    rw [SpecialLinearGroup.toLinearEquiv_apply]
    rw [show ((e (α B) : ↥(modelK1 k VJ V₀)) : SpecialLinearGroup k (VJ × V₀)) =
        blockSLk k V₀ (α B) from e_coe (α B)]
    rw [blockSLk_apply]
    rw [diagE_conj_blockSLk_apply]
    have hcoord : (α B) v = s • B (s⁻¹ • v) := by
      have h1 := hTeq B (s⁻¹ • v)
      have hTinv : T (s⁻¹ • v) = v := by
        have hstep : T (s⁻¹ • v) = s • (s⁻¹ • v) := hs (s⁻¹ • v)
        rw [hstep, smul_smul, mul_inv_cancel₀ hsne, one_smul]
      have hTB : T (B (s⁻¹ • v)) = s • B (s⁻¹ • v) := hs _
      rw [hTinv, hTB] at h1
      exact h1
    rw [hcoord]
    refine Prod.ext ?_ rfl
    simp only [u, units_mk0_val, units_mk0_inv_val]
  · exfalso
    apply not_exists_equivariant_dual_addEquiv (k := k) (E := E) (VJ := VJ) hm T
    intro B f
    have h1 := hTeq (restrictSL (E := E) (VJ := VJ) k B) f
    rw [alpha_restrict B] at h1
    rw [map_inv] at h1
    have hlin : SpecialLinearGroup.toLinearEquiv
        (restrictSL (E := E) (VJ := VJ) k B⁻¹) =
        (SpecialLinearGroup.toLinearEquiv
          (restrictSL (E := E) (VJ := VJ) k B))⁻¹ := by
      rw [map_inv (restrictSL (E := E) (VJ := VJ) k) B, map_inv]
    rw [hlin, ← h1]
    rfl

end CFSG.LinearAlgebra.RootGroupSL
