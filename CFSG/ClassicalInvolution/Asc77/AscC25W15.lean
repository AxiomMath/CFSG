module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterSp4

public section

open CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterSp4
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.Assembly.LowTwoRank
open scoped Matrix
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU (eq_of_central_ratio)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_elt_positiveLong
  mat_elt_negativeLong)
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open CFSG.ClassicalInvolution.Generic

namespace CFSG.ClassicalInvolution.Asc77.C25W.Sp

variable {F : Type} [Field F]

theorem conjSp_eq_conj_longInv (A : gsp 2 F) (a : F) (ha : a ≠ 0) (k : Fin 2)
    (hA : ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      a • mat 2 F (longInv F 2 k)) (g : StatedSp 2 F) :
    conjSp 2 F A g = longInv F 2 k * g * (longInv F 2 k)⁻¹ := by
  apply Subtype.ext
  rw [coe_conjSp]
  set L := longInv F 2 k with hL
  set c := Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) (Units.mk0 a ha) with hc
  have hAL : (A : GL (Fin 2 ⊕ Fin 2) F) = c * ((L : StatedSp 2 F) : GL _ F) := by
    apply Units.ext
    rw [Units.val_mul, hc, Matrix.GeneralLinearGroup.coe_scalar, hA, Matrix.scalar_apply,
      Matrix.smul_eq_diagonal_mul, mat_apply]
    rfl
  have hcc : ∀ x : GL (Fin 2 ⊕ Fin 2) F, c * x = x * c := fun x => by
    have : c ∈ Subgroup.center (GL (Fin 2 ⊕ Fin 2) F) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨_, rfl⟩
    exact (Subgroup.mem_center_iff.mp this x).symm
  rw [hAL]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev]
  calc c * (L : GL _ F) * (g : GL _ F) * ((L : GL _ F)⁻¹ * c⁻¹)
      = c * ((L : GL _ F) * (g : GL _ F) * (L : GL _ F)⁻¹) * c⁻¹ := by group
    _ = ((L : GL _ F) * (g : GL _ F) * (L : GL _ F)⁻¹) * c * c⁻¹ := by rw [hcc]
    _ = _ := by group

theorem conjAut_eq_conj_longInv (A : gsp 2 F) (a : F) (ha : a ≠ 0) (k : Fin 2)
    (hA : ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      a • mat 2 F (longInv F 2 k)) :
    conjAut 2 F A = MulAut.conj (proj 2 F (longInv F 2 k)) := by
  ext p
  obtain ⟨g, rfl⟩ := proj_surjective (r := 2) (K := F) p
  rw [conjAut_proj, conjSp_eq_conj_longInv A a ha k hA g, MulAut.conj_apply, map_mul, map_mul,
    map_inv]

theorem sp4_blocks_shape [Finite F] (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F)
    (β : MulAut (StatedProj (StatedSp 2 F)))
    (hfix : ∀ k : Fin 2, ∀ r ∈ (longBlock F 2 k).range, β (proj 2 F r) = proj 2 F r) :
    ∃ (A : gsp 2 F) (a b : F), a ≠ 0 ∧ b ≠ 0 ∧ a * a = b * b ∧
      ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
        Matrix.diagonal (Sum.elim ![a, b] ![a, b]) ∧ β = conjAut 2 F A := by
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
  exact ⟨A, a, b, ha, hb, hAA, hAab, hβ⟩

theorem sp4_aut_blocks_fine [Finite F] (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F)
    (β : MulAut (StatedProj (StatedSp 2 F)))
    (hfix : ∀ k : Fin 2, ∀ r ∈ (longBlock F 2 k).range, β (proj 2 F r) = proj 2 F r) :
    β = 1 ∨ β = MulAut.conj (proj 2 F (longInv F 2 1)) := by
  obtain ⟨A, a, b, ha, hb, hab, hAab, hβ⟩ := sp4_blocks_shape h2 h4 β hfix
  rcases mul_self_eq_mul_self_iff.mp hab with h | h
  ·
    left
    subst h
    have hcen : (A : GL (Fin 2 ⊕ Fin 2) F) ∈ Subgroup.center (GL (Fin 2 ⊕ Fin 2) F) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      refine ⟨Units.mk0 a ha, ?_⟩
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.coe_scalar, hAab, Matrix.scalar_apply]
      congr 1
      funext i
      rcases i with i | i <;> fin_cases i <;> rfl
    have hconj : conjAut 2 F A = 1 := by
      ext p
      obtain ⟨g, rfl⟩ := proj_surjective (r := 2) (K := F) p
      show proj 2 F (conjSp 2 F A g) = proj 2 F g
      congr 1
      apply Subtype.ext
      rw [coe_conjSp, ← Subgroup.mem_center_iff.mp hcen (g : GL (Fin 2 ⊕ Fin 2) F),
        mul_inv_cancel_right]
    rw [hβ, hconj]
  ·
    right
    rw [hβ]
    apply conjAut_eq_conj_longInv A a ha 1
    rw [hAab, mat_longInv, ← Matrix.diagonal_smul]
    congr 1
    funext i
    rcases i with i | i <;> fin_cases i <;> simp [h, mem_coords]

theorem proj_longInv_rev (k : Fin 2) :
    proj 2 F (longInv F 2 (Fin.rev k)) = proj 2 F (longInv F 2 k) := by
  set L := longInv F 2 k with hL
  set L' := longInv F 2 (Fin.rev k) with hL'
  have hGL : ((L' : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) =
      Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) (-1 : Fˣ) *
        ((L : StatedSp 2 F) : GL _ F) := by
    apply Units.ext
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
    have h := mat_longInv_rev (F := F) k
    rw [mat_apply, mat_apply] at h
    rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
    rw [← hL, ← hL'] at h
    rw [h]
    simp
  have hz : L' * L⁻¹ ∈ spScalars 2 F := by
    rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range]
    refine ⟨-1, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hGL]
    group
  have h1 : proj 2 F (L' * L⁻¹) = 1 := by
    rw [← MonoidHom.mem_ker, ker_proj]
    exact hz
  rw [map_mul, map_inv, mul_inv_eq_one] at h1
  exact h1

theorem psp4_cent [Finite F] (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F)
    {R R' : Subgroup (StatedSp 2 F)} (hR : ∃ i, IsLongRootSp2 R i) (hR' : ∃ i, IsLongRootSp2 R' i)
    (hne : R ≠ R') {x x' : StatedSp 2 F} (hxR : x ∈ R) (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (hx'R' : x' ∈ R') (hx'2 : x' * x' = 1) (hx'1 : x' ≠ 1)
    (hc : x' * x⁻¹ ∈ Subgroup.center (StatedSp 2 F)) (β : MulAut (StatedProj (StatedSp 2 F)))
    (hβ : ∀ r ∈ R, β (proj 2 F r) = proj 2 F r) (hβ' : ∀ r ∈ R', β (proj 2 F r) = proj 2 F r) :
    β = 1 ∨ β = MulAut.conj (proj 2 F x) := by
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
  have hβc : β = c * β' * c⁻¹ := by rw [hβ'def]; group
  have hxg : x = g * longInv F 2 k * g⁻¹ := by
    have hxL : x ∈ (longBlock F 2 k).range.map (MulAut.conj g).toMonoidHom := by
      rw [← hRg]; exact hxR
    obtain ⟨y, hy, hyx⟩ := hxL
    have hyx' : g * y * g⁻¹ = x := hyx
    have hy2 : y * y = 1 := by
      have : g * (y * y) * g⁻¹ = 1 := by
        calc g * (y * y) * g⁻¹ = (g * y * g⁻¹) * (g * y * g⁻¹) := by group
          _ = x * x := by rw [hyx']
          _ = 1 := hx2
      have h1 : y * y = g⁻¹ * (g * (y * y) * g⁻¹) * g := by group
      rw [h1, this]; group
    have hy1 : y ≠ 1 := by
      intro h
      apply hx1
      rw [← hyx', h]; group
    have hyL : y = longInv F 2 k := by
      have hstd := isLongRootSp2_standard (K := F) (n := 2) k
      refine hstd.eq_of_orderOf_eq_two h2 ?_ (orderOf_eq_prime (by rwa [pow_two]) hy1)
      rw [longRootSp2]
      exact hy
    rw [← hyx', hyL]
  rcases sp4_aut_blocks_fine h2 h4 β' hfix with h | h
  · left
    rw [hβc, h]
    group
  · right
    have hL1 : proj 2 F (longInv F 2 1) = proj 2 F (longInv F 2 k) := by
      rcases hk k 1 with rfl | hk1
      · rfl
      · rw [hk1]
        exact proj_longInv_rev k
    have hcL : c (proj 2 F (longInv F 2 k)) = proj 2 F x := by rw [hcp, hxg]
    rw [hβc, h, hL1]
    ext p
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hcL,
      MulAut.apply_inv_self]

end CFSG.ClassicalInvolution.Asc77.C25W.Sp
