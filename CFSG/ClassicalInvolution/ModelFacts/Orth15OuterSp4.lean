module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterSp4Mat
public import CFSG.ClassicalInvolution.ModelFacts.Orth15ChainUModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticTwoGeneration
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticTwoTypePreservation
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.RootSp2

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterSp4

open Matrix CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_apply mat_elt_positiveLong
  mat_elt_negativeLong)
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem exists_conjAut_fieldAut_sp4 [Finite F] (h2 : (2 : F) ≠ 0)
    (β : MulAut (StatedProj (StatedSp 2 F))) :
    ∃ (A : gsp 2 F) (σ : F ≃+* F), β = conjAut 2 F A * fieldAut 2 F σ := by
  have hodd : ringChar F ≠ 2 := by
    intro h
    have h3 : ((2 : ℕ) : F) = 0 := (ringChar.spec F 2).mpr (by rw [h])
    exact h2 (by simpa using h3)
  obtain ⟨-, htop, -⟩ :=
    CFSG.ComponentClassification.CatalogueBSymplecticTwo.odd_symplectic_two_type_preservation
      (K := F) hodd
  have hβ : β ∈ CFSG.ComponentClassification.CatalogueBSymplecticTwo.typeKernel F := by
    rw [htop]
    trivial
  exact (CFSG.ComponentClassification.CatalogueBSymplecticTwo.kernel_generation
    (K := F)).2.1 β hβ

theorem rel_of_fixed (A : gsp 2 F) (σ : F ≃+* F) (g : StatedSp 2 F)
    (h : conjSp 2 F A (fieldSp 2 F σ g) = g) :
    ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
        (mat 2 F g).map σ = mat 2 F g *
      ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
  have h1 : ((A : GL (Fin 2 ⊕ Fin 2) F) * ((fieldSp 2 F σ g : StatedSp 2 F) : GL _ F) *
      (A : GL (Fin 2 ⊕ Fin 2) F)⁻¹ : GL (Fin 2 ⊕ Fin 2) F) = (g : GL _ F) := by
    rw [← coe_conjSp, h]
  have h2 : (A : GL (Fin 2 ⊕ Fin 2) F) * ((fieldSp 2 F σ g : StatedSp 2 F) : GL _ F) =
      (g : GL _ F) * (A : GL (Fin 2 ⊕ Fin 2) F) := by
    calc (A : GL (Fin 2 ⊕ Fin 2) F) * ((fieldSp 2 F σ g : StatedSp 2 F) : GL _ F)
        = ((A : GL (Fin 2 ⊕ Fin 2) F) * ((fieldSp 2 F σ g : StatedSp 2 F) : GL _ F) *
            (A : GL (Fin 2 ⊕ Fin 2) F)⁻¹) * (A : GL (Fin 2 ⊕ Fin 2) F) := by group
      _ = (g : GL _ F) * (A : GL (Fin 2 ⊕ Fin 2) F) := by rw [h1]
  have h3 := congrArg
    (fun u : GL (Fin 2 ⊕ Fin 2) F => (u : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) h2
  simpa [coe_fieldSp, mat_apply] using h3

theorem sp4_aut_blocks [Finite F] (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F)
    (β : MulAut (StatedProj (StatedSp 2 F)))
    (hfix : ∀ k : Fin 2, ∀ r ∈ (longBlock F 2 k).range, β (proj 2 F r) = proj 2 F r) :
    β * β = 1 := by
  obtain ⟨A, σ, hβ⟩ := exists_conjAut_fieldAut_sp4 h2 β
  set α : MulAut (StatedSp 2 F) := conjSp 2 F A * fieldSp 2 F σ with hα
  have hαproj : ∀ g, proj 2 F (α g) = β (proj 2 F g) := fun g => by rw [hβ]; rfl
  have hfixα : ∀ k : Fin 2, ∀ r ∈ (longBlock F 2 k).range, α r = r := by
    intro k
    have : Group.IsPerfect (longRootSp2 F 2 k) := (isClassicalSL2_longRootSp2 h2 k).isPerfect h4
    refine eq_of_central_ratio (longRootSp2 F 2 k) α.toMonoidHom (fun r hr => ?_)
    have h : α r * r⁻¹ ∈ spScalars 2 F := by
      rw [← ker_proj, MonoidHom.mem_ker, map_mul, map_inv, hαproj, hfix k r hr, mul_inv_cancel]
    rw [CFSG.LieType.Universal.Symplectic.center_eq 2 F]
    exact h
  have hu : ∀ (k : Fin 2) (t : F),
      ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
          Matrix.transvection (Sum.inl k) (Sum.inr k) (σ t) =
        Matrix.transvection (Sum.inl k) (Sum.inr k) t *
          ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
    intro k t
    have hg := hfixα k (longBlock F 2 k (sl2Upper t)) ⟨_, rfl⟩
    have := rel_of_fixed A σ _ hg
    rwa [longBlock_sl2Upper, mat_elt_positiveLong, map_transvection] at this
  have hl : ∀ (k : Fin 2) (t : F),
      ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
          Matrix.transvection (Sum.inr k) (Sum.inl k) (σ t) =
        Matrix.transvection (Sum.inr k) (Sum.inl k) t *
          ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
    intro k t
    have hg := hfixα k (longBlock F 2 k (sl2Lower t)) ⟨_, rfl⟩
    have := rel_of_fixed A σ _ hg
    rwa [longBlock_sl2Lower, mat_elt_negativeLong, map_transvection] at this
  have hdet : ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (A : GL (Fin 2 ⊕ Fin 2) F).isUnit).ne_zero
  obtain ⟨hσ, a, b, ha, hb, hAab⟩ := sp4_shape σ _ hdet hu hl
  obtain ⟨μ, hμ⟩ := mem_gsp.mp A.2
  rw [hAab] at hμ
  have hAA : a * a = b * b := sp4_sq a b μ hμ
  subst hσ
  rw [show fieldAut 2 F (RingEquiv.refl F) = 1 from map_one _, mul_one] at hβ
  have hcen : ((A * A : gsp 2 F) : GL (Fin 2 ⊕ Fin 2) F) ∈
      Subgroup.center (GL (Fin 2 ⊕ Fin 2) F) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    refine ⟨Units.mk0 (a * a) (mul_ne_zero ha ha), ?_⟩
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_scalar, Subgroup.coe_mul, Units.val_mul, hAab,
      diag_sq a b hAA, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
    rfl
  have hconj : conjAut 2 F (A * A) = 1 := by
    ext p
    obtain ⟨g, rfl⟩ := proj_surjective (r := 2) (K := F) p
    show proj 2 F (conjSp 2 F (A * A) g) = proj 2 F g
    congr 1
    apply Subtype.ext
    rw [coe_conjSp, ← Subgroup.mem_center_iff.mp hcen (g : GL (Fin 2 ⊕ Fin 2) F),
      mul_inv_cancel_right]
  rw [hβ, ← map_mul, hconj]

theorem mat_longInv_rev (k : Fin 2) :
    mat 2 F (longInv F 2 (Fin.rev k)) = -mat 2 F (longInv F 2 k) := by
  rw [mat_longInv, mat_longInv, Matrix.diagonal_neg]
  congr 1
  funext a
  rcases a with a | a <;> fin_cases k <;> fin_cases a <;> simp [mem_coords]

theorem twin_std_sp (h2 : (2 : F) ≠ 0) {R R' : Subgroup (StatedSp 2 F)}
    (hR : ∃ i, IsLongRootSp2 R i) (hR' : ∃ i, IsLongRootSp2 R' i) (hne : R ≠ R')
    {x x' : StatedSp 2 F} (hxR : x ∈ R) (hx2 : x * x = 1) (hx1 : x ≠ 1) (hx'R' : x' ∈ R')
    (hx'2 : x' * x' = 1) (hx'1 : x' ≠ 1) (hc : x' * x⁻¹ ∈ Subgroup.center (StatedSp 2 F)) :
    ∃ (g : StatedSp 2 F) (k : Fin 2),
      R = (longBlock F 2 k).range.map (MulAut.conj g).toMonoidHom ∧
      R' = (longBlock F 2 (Fin.rev k)).range.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨i, hi⟩ := hR
  obtain ⟨i', hi'⟩ := hR'
  have hxi : x = i := hi.eq_of_orderOf_eq_two h2 hxR (orderOf_eq_prime (by rwa [pow_two]) hx1)
  have hxi' : x' = i' :=
    hi'.eq_of_orderOf_eq_two h2 hx'R' (orderOf_eq_prime (by rwa [pow_two]) hx'1)
  have hRlr := hi.eq_longRootGroup h2
  have hR'lr := hi'.eq_longRootGroup h2
  obtain ⟨k, g, hRg, hig⟩ := hi
  have hc' := hc
  rw [CFSG.LieType.Universal.Symplectic.center_eq 2 F, Subgroup.mem_subgroupOf, StatedScalars,
    MonoidHom.mem_range] at hc'
  obtain ⟨r, hr⟩ := hc'
  have hr' : mat 2 F (x' * x⁻¹) = Matrix.scalar _ (r : F) := by
    rw [mat_apply, ← hr, Matrix.GeneralLinearGroup.coe_scalar]
  have hxx : mat 2 F x * mat 2 F x = 1 := by rw [← map_mul, hx2, map_one]
  have hxx' : mat 2 F x' * mat 2 F x' = 1 := by rw [← map_mul, hx'2, map_one]
  have hx'x : mat 2 F x' = (r : F) • mat 2 F x := by
    calc mat 2 F x' = mat 2 F (x' * x⁻¹) * mat 2 F x := by
          rw [← map_mul, inv_mul_cancel_right]
      _ = (r : F) • mat 2 F x := by
          rw [hr', Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul,
            Matrix.one_mul]
  have hr2 : (r : F) * r = 1 := by
    have h1 : mat 2 F x' * mat 2 F x' = ((r : F) * r) • (1 : Matrix (Fin 2 ⊕ Fin 2) _ F) := by
      rw [hx'x, Matrix.smul_mul, Matrix.mul_smul, hxx, smul_smul]
    rw [hxx'] at h1
    have := congrFun (congrFun h1 (Sum.inl 0)) (Sum.inl 0)
    simpa using this.symm
  rcases mul_self_eq_one_iff.mp hr2 with hr1 | hr1
  · exfalso
    apply hne
    have hxx'' : x' = x := by
      apply mat_injective
      rw [hx'x, hr1, one_smul]
    rw [hRlr, hR'lr, ← hxi, ← hxi', hxx'']
  · refine ⟨g, k, hRg, ?_⟩
    have hx'g : x' = g * longInv F 2 (Fin.rev k) * g⁻¹ := by
      apply mat_injective
      rw [hx'x, hr1, neg_one_smul, hxi, hig, map_mul, map_mul, map_mul, map_mul,
        mat_longInv_rev, Matrix.mul_neg, Matrix.neg_mul]
    have hi'' := (isLongRootSp2_standard (K := F) (n := 2) (Fin.rev k)).conj g
    rw [hR'lr, ← hxi', hx'g]
    exact (hi''.eq_longRootGroup h2).symm

theorem psp4_autVac [Finite F] (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F)
    {R R' : Subgroup (StatedSp 2 F)} (hR : ∃ i, IsLongRootSp2 R i) (hR' : ∃ i, IsLongRootSp2 R' i)
    (hne : R ≠ R') {x x' : StatedSp 2 F} (hxR : x ∈ R) (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (hx'R' : x' ∈ R') (hx'2 : x' * x' = 1) (hx'1 : x' ≠ 1)
    (hc : x' * x⁻¹ ∈ Subgroup.center (StatedSp 2 F)) (β : MulAut (StatedProj (StatedSp 2 F)))
    (hβ : ∀ r ∈ R, β (proj 2 F r) = proj 2 F r) (hβ' : ∀ r ∈ R', β (proj 2 F r) = proj 2 F r) :
    β * β = 1 := by
  obtain ⟨g, k, hRg, hR'g⟩ := twin_std_sp h2 hR hR' hne hxR hx2 hx1 hx'R' hx'2 hx'1 hc
  set c : MulAut (StatedProj (StatedSp 2 F)) := MulAut.conj (proj 2 F g) with hcdef
  have hcp : ∀ s, c (proj 2 F s) = proj 2 F (g * s * g⁻¹) := fun s => by
    rw [hcdef, MulAut.conj_apply, map_mul, map_mul, map_inv]
  set β' : MulAut (StatedProj (StatedSp 2 F)) := c⁻¹ * β * c with hβ'def
  have hβ'p : ∀ s, β' (proj 2 F s) = (c⁻¹) (β (c (proj 2 F s))) := fun s => rfl
  have hfixβ' : ∀ (S T : Subgroup (StatedSp 2 F)), T = S.map (MulAut.conj g).toMonoidHom →
      (∀ r ∈ T, β (proj 2 F r) = proj 2 F r) → ∀ r ∈ S, β' (proj 2 F r) = proj 2 F r := by
    intro S T hT hfix r hr
    have hmem : g * r * g⁻¹ ∈ S.map (MulAut.conj g).toMonoidHom := ⟨r, hr, rfl⟩
    rw [← hT] at hmem
    rw [hβ'p, hcp, hfix _ hmem, ← hcp]
    simp
  have hk : ∀ k k₀ : Fin 2, k₀ = k ∨ k₀ = Fin.rev k := by decide
  have hfix : ∀ k₀ : Fin 2, ∀ r ∈ (longBlock F 2 k₀).range, β' (proj 2 F r) = proj 2 F r := by
    intro k₀
    rcases hk k k₀ with rfl | rfl
    · exact hfixβ' _ R hRg hβ
    · exact hfixβ' _ R' hR'g hβ'
  have hsq : β * β = c * (β' * β') * c⁻¹ := by rw [hβ'def]; group
  rw [hsq, sp4_aut_blocks h2 h4 β' hfix]
  group

end CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterSp4
