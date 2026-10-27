module

public import CFSG.ClassicalInvolution.Q3.Q3TIYPOutGen
public import CFSG.ClassicalInvolution.Q3.Q3WASNorm
public import CFSG.ClassicalInvolution.Q3.Q3ZModel

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TIY

open Matrix CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU
  CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterSp4
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_apply mat_elt_positiveLong
  mat_elt_negativeLong)
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open CFSG.ClassicalInvolution.ModelFacts (modelClauseZero)
open CFSG.ClassicalInvolution.Q3 (CompData)
open scoped MatrixGroups

section Aut

variable {F : Type} [Field F]

theorem sp4_aut_blocks3 [Finite F] (hF : Nat.card F = 3) (h2 : (2 : F) ≠ 0)
    (β : MulAut (StatedProj (StatedSp 2 F)))
    (hfix : ∀ k : Fin 2, ∀ r ∈ (longBlock F 2 k).range, β (proj 2 F r) = proj 2 F r) :
    β * β = 1 := by
  obtain ⟨A, σ, hβ⟩ := exists_conjAut_fieldAut_sp4 h2 β
  set α : MulAut (StatedSp 2 F) := conjSp 2 F A * fieldSp 2 F σ with hα
  have hαproj : ∀ g, proj 2 F (α g) = β (proj 2 F g) := fun g => by rw [hβ]; rfl
  have hfixα : ∀ k : Fin 2, ∀ r ∈ (longBlock F 2 k).range, α r = r := by
    intro k
    have hpow : Q3W.Pow3 (longBlock F 2 k).range := Q3W.pow3_range_sl2 hF (longBlock F 2 k)
    refine Q3W.fixed_of_pow3_of_central α.toMonoidHom hpow
      (Z := Subgroup.center (StatedSp 2 F)) le_rfl ?_ ?_
    · intro c hc h3
      have hsq : c * c = 1 := mul_self_eq_one_of_mem_center (n := 2) (by norm_num) hc
      have h23 : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
      have := h3.trans h23
      omega
    · intro r hr
      have h : α r * r⁻¹ ∈ spScalars 2 F := by
        rw [← ker_proj, MonoidHom.mem_ker, map_mul, map_inv, hαproj, hfix k r hr, mul_inv_cancel]
      have hc : α r * r⁻¹ ∈ Subgroup.center (StatedSp 2 F) := by
        rw [CFSG.LieType.Universal.Symplectic.center_eq 2 F]
        exact h
      have hc' := Subgroup.mem_center_iff.mp hc r⁻¹
      have e : r⁻¹ * α.toMonoidHom r = α r * r⁻¹ :=
        calc r⁻¹ * (α.toMonoidHom r) = r⁻¹ * (α r * r⁻¹) * r := by
              show r⁻¹ * α r = r⁻¹ * (α r * r⁻¹) * r
              group
          _ = (α r * r⁻¹) * r⁻¹ * r := by rw [hc']
          _ = α r * r⁻¹ := by group
      rw [e]
      exact hc
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

theorem psp4_autVac3 [Finite F] (hF : Nat.card F = 3) (h2 : (2 : F) ≠ 0)
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
  rw [hsq, sp4_aut_blocks3 hF h2 β' hfix]
  group

end Aut


theorem sqDichotomyC_psp2 : SqDichotomyC (CompData.model .PSp 2) := by
  have hadm : StatedLieAdmissible .PSp 2 3 1 := Q3Z.statedLieAdmissible_psp2
  have h2 : (2 : GaloisField 3 1) ≠ 0 := Q3W.two_ne_zero_gf3
  have : Group.IsPerfect (CFSG.ClassicalInvolution.Generic.modelUniv .PSp 2 3 1
      Nat.prime_three).K :=
    Group.isPerfect_def.2 (modelClauseZero .PSp 2 3 1 Nat.prime_three trivial hadm).1.1
  refine sqDichotomyC_of_autVac (CompData.model .PSp 2) (proj 2 (GaloisField 3 1))
    proj_surjective ?_ ?_
  · exact ker_proj.trans (CFSG.LieType.Universal.Symplectic.center_eq 2 _).symm
  · intro R R' hR hR' hne x x' hxR hx2 hx1 hx'R' hx'2 hx'1 hc φ hφ hφ' _
    left
    exact psp4_autVac3 Q3W.card_gf3 h2
      ((exists_isLongRootSp2_iff h2 R).mpr ((mem_fundamentalSubgroups_PSp_iff hadm R).mp hR))
      ((exists_isLongRootSp2_iff h2 R').mpr ((mem_fundamentalSubgroups_PSp_iff hadm R').mp hR'))
      hne hxR hx2 hx1 hx'R' hx'2 hx'1 hc φ hφ hφ'

end CFSG.ClassicalInvolution.Q3.Q3TIY
