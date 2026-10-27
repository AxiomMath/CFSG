module

public import CFSG.ClassicalInvolution.Asc77.AscC5OM4

public section

namespace CFSG.ClassicalInvolution.Asc77.C5O.M

open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterSp4 (rel_of_fixed rel_facts
  map_transvection)
open CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU (eq_of_central_ratio)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective mat_elt_positiveLong
  mat_elt_negativeLong)
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open scoped Matrix MatrixGroups

variable {F : Type} [Field F]

theorem conjSp_eq_conj_of_eq_smul (A : gsp 2 F) (a : F) (ha : a ≠ 0) (s : StatedSp 2 F)
    (hA : ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      a • mat 2 F s) (g : StatedSp 2 F) :
    conjSp 2 F A g = s * g * s⁻¹ := by
  apply Subtype.ext
  rw [coe_conjSp]
  set c := Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) (Units.mk0 a ha) with hc
  have hAL : (A : GL (Fin 2 ⊕ Fin 2) F) = c * ((s : StatedSp 2 F) : GL _ F) := by
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
  calc c * (s : GL _ F) * (g : GL _ F) * ((s : GL _ F)⁻¹ * c⁻¹)
      = c * ((s : GL _ F) * (g : GL _ F) * (s : GL _ F)⁻¹) * c⁻¹ := by group
    _ = ((s : GL _ F) * (g : GL _ F) * (s : GL _ F)⁻¹) * c * c⁻¹ := by rw [hcc]
    _ = _ := by group

theorem shape_of_fix_L0 [Finite F] (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F) (M : gsp 2 F)
    (σ : F ≃+* F)
    (hfix : ∀ r ∈ longRootSp2 F 2 0, conjSp 2 F M (fieldSp 2 F σ r) * r⁻¹ ∈ spScalars 2 F) :
    σ = RingEquiv.refl F ∧ ∃ (a : F) (b : SL(2, F)), a ≠ 0 ∧
      ((M : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
        a • mat 2 F (longBlock F 2 1 b) := by
  set α : MulAut (StatedSp 2 F) := conjSp 2 F M * fieldSp 2 F σ with hα
  have hperf : Group.IsPerfect (longRootSp2 F 2 0) :=
    (isClassicalSL2_longRootSp2 (K := F) (n := 2) h2 0).isPerfect h4
  have hfixα : ∀ r ∈ longRootSp2 F 2 0, α r = r :=
    eq_of_central_ratio (longRootSp2 F 2 0) α.toMonoidHom (fun r hr => by
      rw [CFSG.LieType.Universal.Symplectic.center_eq]
      exact hfix r hr)
  set Mm := ((M : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) with hMm
  have hu : ∀ t : F, Mm * Matrix.transvection (Sum.inl 0) (Sum.inr 0) (σ t) =
      Matrix.transvection (Sum.inl 0) (Sum.inr 0) t * Mm := by
    intro t
    have hg := hfixα (longBlock F 2 0 (sl2Upper t)) ⟨_, rfl⟩
    have := rel_of_fixed M σ _ hg
    rwa [longBlock_sl2Upper, mat_elt_positiveLong, map_transvection] at this
  have hl : ∀ t : F, Mm * Matrix.transvection (Sum.inr 0) (Sum.inl 0) (σ t) =
      Matrix.transvection (Sum.inr 0) (Sum.inl 0) t * Mm := by
    intro t
    have hg := hfixα (longBlock F 2 0 (sl2Lower t)) ⟨_, rfl⟩
    have := rel_of_fixed M σ _ hg
    rwa [longBlock_sl2Lower, mat_elt_negativeLong, map_transvection] at this
  have h1 : (1 : F) ≠ 0 := one_ne_zero
  obtain ⟨hr1, hc1, hd1⟩ := rel_facts σ Mm 1 h1 (hu 1)
  obtain ⟨hr2, hc2, -⟩ := rel_facts σ Mm 1 h1 (hl 1)
  rw [map_one, mul_one, one_mul] at hd1
  have hμ := multiplier_spec M
  rw [← hMm] at hμ
  set μ : F := ((multiplier 2 F M : Fˣ) : F) with hμdef
  have e00 := congrFun (congrFun hμ (Sum.inl 0)) (Sum.inr 0)
  have e11 := congrFun (congrFun hμ (Sum.inl 1)) (Sum.inr 1)
  rw [show (formJ 2 F) = gram F 2 from rfl, transpose_mul_gram_mul_apply] at e00 e11
  simp only [Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul, gram,
    Matrix.fromBlocks_apply₁₂, Matrix.one_apply_eq, mul_one] at e00 e11
  have z1 : Mm (Sum.inl 0) (Sum.inl 1) = 0 := hr2 _ (by simp)
  have z2 : Mm (Sum.inr 0) (Sum.inl 1) = 0 := hr1 _ (by simp)
  have z3 : Mm (Sum.inl 1) (Sum.inr 0) = 0 := hc2 _ (by simp)
  have z4 : Mm (Sum.inr 1) (Sum.inr 0) = 0 := hc2 _ (by simp)
  have z5 : Mm (Sum.inl 1) (Sum.inl 0) = 0 := hc1 _ (by simp)
  have z6 : Mm (Sum.inr 1) (Sum.inl 0) = 0 := hc1 _ (by simp)
  have z7 : Mm (Sum.inl 0) (Sum.inr 1) = 0 := hr2 _ (by simp)
  have z8 : Mm (Sum.inr 0) (Sum.inr 1) = 0 := hr1 _ (by simp)
  have z9 : Mm (Sum.inr 0) (Sum.inl 0) = 0 := hr1 _ (by simp)
  have z10 : Mm (Sum.inl 0) (Sum.inr 0) = 0 := hr2 _ (by simp)
  simp [sgn, par, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, ← hd1] at e00 e11
  set a := Mm (Sum.inl 0) (Sum.inl 0) with ha_def
  have ha0 : a ≠ 0 := by
    intro h
    have hμ0 : μ ≠ 0 := Units.ne_zero _
    rw [← e00, h, mul_zero] at hμ0
    exact hμ0 rfl
  have hσ : σ = RingEquiv.refl F := by
    refine RingEquiv.ext fun t => ?_
    by_cases ht : t = 0
    · rw [ht, map_zero]
      rfl
    · have h3 := (rel_facts σ Mm t ht (hu t)).2.2
      rw [← hd1] at h3
      have h4 : a * (σ t - t) = 0 := by linear_combination h3
      exact sub_eq_zero.mp ((mul_eq_zero.mp h4).resolve_left ha0)
  have hdet : (a⁻¹ • stdBlock 1 Mm).det = 1 := by
    rw [Matrix.det_smul, Matrix.det_fin_two]
    simp only [stdBlock, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fintype.card_fin]
    rw [show Mm (Sum.inl 1) (Sum.inl 1) * Mm (Sum.inr 1) (Sum.inr 1) -
        Mm (Sum.inl 1) (Sum.inr 1) * Mm (Sum.inr 1) (Sum.inl 1) = a * a by
      rw [e00]; linear_combination e11]
    field_simp
  refine ⟨hσ, a, mkSL (a⁻¹ • stdBlock 1 Mm) hdet, ha0, ?_⟩
  ext r t
  rw [Matrix.smul_apply, mat_longBlock, coe_mkSL]
  rcases r with r | r <;> rcases t with t | t <;> fin_cases r <;> fin_cases t <;>
    simp [CFSG.LieType.Steinberg.Sp.blockMat, stdBlock, z1, z2, z3, z4, z5, z6, z7, z8, z9,
      z10, ← hd1, ← ha_def, ha0]

namespace Frame

variable {Y : Type} [Group Y] {Φ : Set (Subgroup Y)} {A A' : Subgroup Y} {z' : Y}
  (fr : Frame F Y Φ A A' z')
include fr

theorem mem_A {r : StatedSp 2 F} (hr : r ∈ longRootSp2 F 2 0) : fr.ψ r ∈ A := by
  have h : fr.ψ r ∈ (longRootSp2 F 2 0).map fr.ψ := Subgroup.mem_map_of_mem _ hr
  rwa [← fr.hA] at h

theorem mem_A' {r : StatedSp 2 F} (hr : r ∈ longRootSp2 F 2 1) : fr.ψ r ∈ A' := by
  have h : fr.ψ r ∈ (longRootSp2 F 2 1).map fr.ψ := Subgroup.mem_map_of_mem _ hr
  rwa [← fr.hA'] at h

theorem inner_of_fix_A [Finite F] (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F) (β : Y ≃* Y)
    (hβ : ∀ x ∈ A, β x = x) : ∃ y ∈ A', ∀ x : Y, β x = y * x * y⁻¹ := by
  obtain ⟨M, σ, hβM⟩ := fr.exists_lift_aut h2 β
  have hfix : ∀ r ∈ longRootSp2 F 2 0, conjSp 2 F M (fieldSp 2 F σ r) * r⁻¹ ∈ spScalars 2 F := by
    intro r hr
    rw [← fr.ker, MonoidHom.mem_ker, map_mul, map_inv, ← hβM,
      hβ _ (fr.mem_A hr), mul_inv_cancel]
  obtain ⟨hσ, a, b, ha, hMb⟩ := shape_of_fix_L0 h2 h4 M σ hfix
  subst hσ
  refine ⟨fr.ψ (longBlock F 2 1 b), fr.mem_A' ⟨b, rfl⟩, ?_⟩
  intro y
  obtain ⟨x, rfl⟩ := fr.surj y
  rw [hβM, show fieldSp 2 F (RingEquiv.refl F) = 1 from map_one _, MulAut.one_apply,
    conjSp_eq_conj_of_eq_smul M a ha _ hMb, map_mul, map_mul, map_inv]

theorem innerOfTwin [Finite F] (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F) (β : Y ≃* Y)
    (hin : ∃ g ∈ A, ∀ x ∈ A, β x = g * x * g⁻¹) : ∃ y : Y, ∀ x : Y, β x = y * x * y⁻¹ := by
  obtain ⟨g, -, hg⟩ := hin
  let β₁ : Y ≃* Y := β.trans (MulAut.conj g⁻¹)
  have hβ₁ : ∀ x ∈ A, β₁ x = x := by
    intro x hx
    change g⁻¹ * β x * g⁻¹⁻¹ = x
    rw [hg x hx]
    group
  obtain ⟨y, -, hy⟩ := fr.inner_of_fix_A h2 h4 β₁ hβ₁
  refine ⟨g * y, fun x => ?_⟩
  have h1 : g⁻¹ * β x * g⁻¹⁻¹ = y * x * y⁻¹ := hy x
  calc β x = g * (g⁻¹ * β x * g⁻¹⁻¹) * g⁻¹ := by group
    _ = g * y * x * (g * y)⁻¹ := by rw [h1]; group

end Frame

end CFSG.ClassicalInvolution.Asc77.C5O.M
