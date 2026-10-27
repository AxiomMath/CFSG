module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LeviJZeroSLThree
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup Matrix
open scoped commutatorElement MatrixGroups

section SL3

variable {F : Type} [Field F]

@[expose] def slTrans {i j : Fin 3} (hij : i ≠ j) (c : F) : SL(3, F) :=
  ⟨transvection i j c, det_transvection_of_ne i j hij c⟩

theorem coe_slTrans {i j : Fin 3} (hij : i ≠ j) (c : F) :
    ((slTrans hij c : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = transvection i j c :=
  rfl

@[expose] def slN₀₁ (t : F) : SL(3, F) :=
  slTrans (show (0 : Fin 3) ≠ 1 by decide) t * slTrans (show (1 : Fin 3) ≠ 0 by decide) (-t⁻¹) *
    slTrans (show (0 : Fin 3) ≠ 1 by decide) t

@[expose] def slN₁₂ (t : F) : SL(3, F) :=
  slTrans (show (1 : Fin 3) ≠ 2 by decide) t * slTrans (show (2 : Fin 3) ≠ 1 by decide) (-t⁻¹) *
    slTrans (show (1 : Fin 3) ≠ 2 by decide) t

theorem coe_slN₀₁ {t : F} (ht : t ≠ 0) :
    ((slN₀₁ t : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = !![0, t, 0; -t⁻¹, 0, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [slN₀₁, coe_slTrans, transvection, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.one_apply, Matrix.single_apply, ht]

theorem coe_slN₁₂ {t : F} (ht : t ≠ 0) :
    ((slN₁₂ t : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = !![1, 0, 0; 0, 0, t; 0, -t⁻¹, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [slN₁₂, coe_slTrans, transvection, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.one_apply, Matrix.single_apply, ht]

theorem coe_slN₀₁_mul {t : F} (ht : t ≠ 0) :
    ((slN₀₁ t * slN₀₁ (-1 : F) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = diagonal ![t, t⁻¹, 1] := by
  rw [show ((slN₀₁ t * slN₀₁ (-1 : F) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
    (slN₀₁ t : Matrix (Fin 3) (Fin 3) F) * (slN₀₁ (-1 : F) : Matrix (Fin 3) (Fin 3) F) from rfl,
    coe_slN₀₁ ht, coe_slN₀₁ (neg_ne_zero.2 one_ne_zero)]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem coe_slN₁₂_mul {t : F} (ht : t ≠ 0) :
    ((slN₁₂ t * slN₁₂ (-1 : F) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = diagonal ![1, t, t⁻¹] := by
  rw [show ((slN₁₂ t * slN₁₂ (-1 : F) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
    (slN₁₂ t : Matrix (Fin 3) (Fin 3) F) * (slN₁₂ (-1 : F) : Matrix (Fin 3) (Fin 3) F) from rfl,
    coe_slN₁₂ ht, coe_slN₁₂ (neg_ne_zero.2 one_ne_zero)]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem scalar_eq_diag_mul {ω : F} (hω : ω ^ 3 = 1) :
    scalar (Fin 3) ω = diagonal ![ω, ω⁻¹, 1] * diagonal ![1, ω ^ 2, (ω ^ 2)⁻¹] := by
  have h0 : ω ≠ 0 := by
    rintro rfl
    simp at hω
  have h1 : ω⁻¹ * ω ^ 2 = ω := by
    rw [sq, ← mul_assoc, inv_mul_cancel₀ h0, one_mul]
  have h2 : (ω ^ 2)⁻¹ = ω := inv_eq_of_mul_eq_one_right (by rw [← pow_succ, hω])
  rw [diagonal_mul_diagonal, scalar_apply]
  congr 1
  funext i
  fin_cases i <;> simp [h1, h2]

end SL3

namespace TrialityD4Data

variable {X : Type*} [Group X] {q : ℕ} (d : TrialityD4Data X q)

noncomputable def a2Pres :
    PresentedGroup (CFSG.Open.steinbergSLRels 3 d.Γ₀) ≃* SL(3, d.Γ₀) :=
  Classical.choose (CFSG.LieType.Steinberg.SL.exists_steinbergSLRels_equiv (m := 2) (F := d.Γ₀)
    le_rfl)

theorem a2Pres_of {i j : Fin 3} (hij : i ≠ j) (c : d.Γ₀) :
    ((d.a2Pres (PresentedGroup.of (i, j, c)) : SL(3, d.Γ₀)) : Matrix (Fin 3) (Fin 3) d.Γ₀) =
      transvection i j c :=
  Classical.choose_spec (CFSG.LieType.Steinberg.SL.exists_steinbergSLRels_equiv (m := 2)
    (F := d.Γ₀) le_rfl) i j c hij

noncomputable def a2PresHom : PresentedGroup (CFSG.Open.steinbergSLRels 3 d.Γ₀) →* X :=
  PresentedGroup.toGroup (CFSG.DesarguesianPlanes.steinbergGen_rels d.isSteinbergFamily_a2)

noncomputable def a2Hom : SL(3, d.Γ₀) →* X :=
  d.a2PresHom.comp d.a2Pres.symm.toMonoidHom

theorem a2Hom_transvection {i j : Fin 3} (hij : i ≠ j) (c : d.Γ₀) :
    d.a2Hom (slTrans hij c) = d.a2 i j c := by
  have hA : slTrans hij c = d.a2Pres (PresentedGroup.of (i, j, c)) := by
    apply Subtype.ext
    rw [coe_slTrans, d.a2Pres_of hij]
  rw [hA, a2Hom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
    a2PresHom, PresentedGroup.toGroup.of, CFSG.DesarguesianPlanes.steinbergGen_of_ne _ hij]

@[expose] def a2Span : Subgroup X :=
  closure {g | ∃ (i j : Fin 3) (c : d.Γ₀), i ≠ j ∧ d.a2 i j c = g}

theorem range_a2Hom_eq_a2Span : d.a2Hom.range = d.a2Span := by
  apply le_antisymm
  · rintro _ ⟨A, rfl⟩
    obtain ⟨p, rfl⟩ := d.a2Pres.surjective A
    rw [a2Hom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    have hp : p ∈ closure (Set.range (PresentedGroup.of :
        Fin 3 × Fin 3 × d.Γ₀ → PresentedGroup (CFSG.Open.steinbergSLRels 3 d.Γ₀))) := by
      rw [PresentedGroup.closure_range_of]
      trivial
    induction hp using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨⟨i, j, c⟩, rfl⟩ := hx
      rw [a2PresHom, PresentedGroup.toGroup.of]
      by_cases hij : i = j
      · simp [CFSG.DesarguesianPlanes.steinbergGen, hij]
      · rw [CFSG.DesarguesianPlanes.steinbergGen_of_ne _ hij]
        exact subset_closure ⟨i, j, c, hij, rfl⟩
    | one => rw [map_one]; exact one_mem _
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
    | inv x _ hx => rw [map_inv]; exact inv_mem hx
  · rw [a2Span, closure_le]
    rintro _ ⟨i, j, c, hij, rfl⟩
    exact ⟨slTrans hij c, d.a2Hom_transvection hij c⟩

theorem u_conj_mem_a2Span {g : X} (hg : g ∈ d.a2Span) : d.u * g * d.u ∈ d.a2Span := by
  have h : d.a2Span ≤ d.a2Span.comap (MulAut.conj d.u).toMonoidHom := by
    rw [a2Span, closure_le]
    rintro _ ⟨i, j, c, hij, rfl⟩
    simp only [SetLike.mem_coe, mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, d.u_inv]
    rw [d.u_conj_a2 hij c]
    exact subset_closure ⟨_, _, c, fun e => hij (Fin.rev_inj.1 e).symm, rfl⟩
  simpa [d.u_inv] using h hg

theorem v_conj_mem_a2Span {g : X} (hg : g ∈ d.a2Span) : d.v * g * d.v ∈ d.a2Span := by
  have hinj : Function.Injective a2Swap := by decide
  have h : d.a2Span ≤ d.a2Span.comap (MulAut.conj d.v).toMonoidHom := by
    rw [a2Span, closure_le]
    rintro _ ⟨i, j, c, hij, rfl⟩
    simp only [SetLike.mem_coe, mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, d.v_inv]
    rw [d.v_conj_a2 hij c]
    exact subset_closure ⟨_, _, c, fun e => hij (hinj e), rfl⟩
  simpa [d.v_inv] using h hg

theorem a2Span_eq_leviJ₀ : d.a2Span = d.leviJ₀ := by
  apply le_antisymm
  · rw [a2Span, closure_le]
    rintro _ ⟨i, j, c, -, rfl⟩
    exact d.a2_mem_leviJ₀ i j c
  · have hU₂ : d.U₂ ≤ d.a2Span := by
      rintro _ ⟨c, rfl⟩
      exact subset_closure ⟨0, 1, c, by decide, rfl⟩
    have hv : d.v ∈ d.a2Span :=
      (d.J₄_le_and_v_mem_of hU₂ fun z hz => d.v_conj_mem_a2Span hz).2
    have huvu : d.u * d.v * d.u ∈ d.a2Span := d.u_conj_mem_a2Span hv
    rw [leviJ₀, closure_le]
    rintro g (((hg | hg) | hg) | hg)
    · exact hU₂ hg
    · obtain ⟨c, rfl⟩ := hg
      exact subset_closure ⟨1, 2, c, by decide, rfl⟩
    · obtain ⟨c, rfl⟩ := hg
      exact subset_closure ⟨0, 2, c, by decide, rfl⟩
    · rcases hg with rfl | rfl | rfl
      · exact hv
      · exact huvu
      · rw [show d.v * d.u * d.v * d.u * d.v = d.v * (d.u * d.v * d.u) * d.v by group]
        exact d.v_conj_mem_a2Span huvu

theorem range_a2Hom : d.a2Hom.range = d.leviJ₀ := by
  rw [range_a2Hom_eq_a2Span, a2Span_eq_leviJ₀]

theorem isQuasisimple_SL3_Γ₀ : CFSG.IsQuasisimple SL(3, d.Γ₀) :=
  CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple 3 d.Γ₀
    (by norm_num) (Or.inl (by norm_num)) (Or.inl (by norm_num))

theorem ker_a2Hom_le_center : d.a2Hom.ker ≤ center SL(3, d.Γ₀) := by
  have hq := d.isQuasisimple_SL3_Γ₀
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top
      (CFSG.ComponentClassification.CatalogueBAlternating.quasisimple_iff_native.mp hq)
      d.a2Hom.ker with h | h
  · exact h
  · exfalso
    have hmem : slTrans (show (0 : Fin 3) ≠ 1 by decide) (1 : d.Γ₀) ∈ d.a2Hom.ker :=
      h ▸ mem_top _
    rw [MonoidHom.mem_ker, d.a2Hom_transvection, a2_01] at hmem
    exact one_ne_zero (d.x₂_injective (hmem.trans d.x₂_zero.symm))

noncomputable def a2HomLevi : SL(3, d.Γ₀) →* d.leviJ₀ :=
  d.a2Hom.codRestrict d.leviJ₀ fun A => d.range_a2Hom ▸ ⟨A, rfl⟩

theorem a2HomLevi_surjective : Function.Surjective d.a2HomLevi := by
  rintro ⟨g, hg⟩
  rw [← d.range_a2Hom] at hg
  obtain ⟨A, rfl⟩ := hg
  exact ⟨A, rfl⟩

theorem ker_a2HomLevi : d.a2HomLevi.ker = d.a2Hom.ker := by
  ext A
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem isQuasisimple_leviJ₀ : CFSG.IsQuasisimple d.leviJ₀ :=
  CFSG.LocalCores.isQuasisimple_of_surjective d.isQuasisimple_SL3_Γ₀ d.a2HomLevi
    d.a2HomLevi_surjective (d.ker_a2HomLevi ▸ d.ker_a2Hom_le_center)

theorem leviLongRep_x₂ (a : d.Γ₀) : d.leviLongRep ⟨d.x₂ a, d.x₂_mem_leviLong a⟩ = d.slX₂ a :=
  d.sl_eq_of_yv fun w => by rw [← d.leviLongRep_spec, ← d.x₂_conj_yv]

theorem leviLongRep_v : d.leviLongRep ⟨d.v, d.v_mem_leviLong⟩ = d.slV :=
  d.sl_eq_of_yv fun w => by rw [← d.leviLongRep_spec, ← d.v_conj_yv]

theorem hA_mem_leviLong (b : (d.Γ₀)ˣ) : d.hA b ∈ d.leviLong :=
  d.J₄_le_leviLong (by rw [d.J₄_eq_range_hA]; exact ⟨b, rfl⟩)

@[expose] def slDiag (b : (d.Γ₀)ˣ) : Matrix.SpecialLinearGroup (Fin 2) d.Γ₀ :=
  ⟨!![((b⁻¹ : (d.Γ₀)ˣ) : d.Γ₀), 0; 0, (b : d.Γ₀)], by
    simp [Matrix.det_fin_two]⟩

theorem leviLongRep_hA (b : (d.Γ₀)ˣ) :
    d.leviLongRep ⟨d.hA b, d.hA_mem_leviLong b⟩ = d.slDiag b := by
  refine d.sl_eq_of_yv fun w => ?_
  rw [← d.leviLongRep_spec]
  change d.hA b * (d.x₅ (w 0) * d.x₆ (w 1)) * (d.hA b)⁻¹ = _
  rw [show d.hA b * (d.x₅ (w 0) * d.x₆ (w 1)) * (d.hA b)⁻¹ =
    (d.hA b * d.x₅ (w 0) * (d.hA b)⁻¹) * (d.hA b * d.x₆ (w 1) * (d.hA b)⁻¹) by group,
    d.hA_conj_x₅, d.hA_conj_x₆]
  simp [yv, slDiag, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem one_add_one_Γ₀ : (1 : d.Γ₀) + 1 = 0 :=
  d.add_self_Γ₀ 1

theorem coe_slX₂_slV_mul {s : d.Γ₀} (hs : s ≠ 0) :
    ((d.slX₂ s * (d.slV * d.slX₂ s⁻¹ * d.slV) * d.slX₂ s : Matrix.SpecialLinearGroup (Fin 2) d.Γ₀) :
      Matrix (Fin 2) (Fin 2) d.Γ₀) = !![0, s⁻¹; s, 0] := by
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  rw [show ((d.slX₂ s : Matrix.SpecialLinearGroup (Fin 2) d.Γ₀) : Matrix (Fin 2) (Fin 2) d.Γ₀) =
    !![1, 0; s, 1] from rfl, show ((d.slX₂ s⁻¹ : Matrix.SpecialLinearGroup (Fin 2) d.Γ₀) :
    Matrix (Fin 2) (Fin 2) d.Γ₀) = !![1, 0; s⁻¹, 1] from rfl,
    show ((d.slV : Matrix.SpecialLinearGroup (Fin 2) d.Γ₀) : Matrix (Fin 2) (Fin 2) d.Γ₀) =
    !![0, 1; 1, 0] from rfl]
  simp only [Matrix.mul_fin_two]
  have h1 : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  have h2 : s⁻¹ * s = 1 := inv_mul_cancel₀ hs
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h1, h2, d.one_add_one_Γ₀]

theorem a2Hom_slN₀₁_mul {t : d.Γ₀} (ht : t ≠ 0) :
    d.a2Hom (slN₀₁ t * slN₀₁ (-1)) = d.hA (Units.mk0 t ht) := by
  have hn : ∀ s : d.Γ₀, d.a2Hom (slN₀₁ s) = d.x₂ s * (d.v * d.x₂ (s⁻¹) * d.v) * d.x₂ s := by
    intro s
    rw [slN₀₁, map_mul, map_mul, d.a2Hom_transvection, d.a2Hom_transvection, a2_01, a2_10,
      d.neg_Γ₀, d.negRoot_x₂]
  set g : d.leviLong := ⟨d.x₂ t, d.x₂_mem_leviLong t⟩ *
    (⟨d.v, d.v_mem_leviLong⟩ * ⟨d.x₂ t⁻¹, d.x₂_mem_leviLong t⁻¹⟩ * ⟨d.v, d.v_mem_leviLong⟩) *
    ⟨d.x₂ t, d.x₂_mem_leviLong t⟩ * (⟨d.x₂ 1, d.x₂_mem_leviLong 1⟩ *
    (⟨d.v, d.v_mem_leviLong⟩ * ⟨d.x₂ 1, d.x₂_mem_leviLong 1⟩ * ⟨d.v, d.v_mem_leviLong⟩) *
    ⟨d.x₂ 1, d.x₂_mem_leviLong 1⟩) with hg
  have hgval : (g : X) = d.a2Hom (slN₀₁ t * slN₀₁ (-1)) := by
    rw [map_mul, hn, hn, d.neg_one_Γ₀, inv_one]
    rfl
  have h1 : ((d.slX₂ 1 * (d.slV * d.slX₂ 1 * d.slV) * d.slX₂ 1 :
      Matrix.SpecialLinearGroup (Fin 2) d.Γ₀) : Matrix (Fin 2) (Fin 2) d.Γ₀) = !![0, 1; 1, 0] := by
    simpa using d.coe_slX₂_slV_mul (one_ne_zero (α := d.Γ₀))
  have hrep : d.leviLongRep g = d.leviLongRep ⟨d.hA (Units.mk0 t ht), d.hA_mem_leviLong _⟩ := by
    rw [d.leviLongRep_hA, hg]
    simp only [map_mul, d.leviLongRep_x₂, d.leviLongRep_v]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, d.coe_slX₂_slV_mul ht, h1,
      show ((d.slDiag (Units.mk0 t ht) : Matrix.SpecialLinearGroup (Fin 2) d.Γ₀) :
        Matrix (Fin 2) (Fin 2) d.Γ₀) = !![t⁻¹, 0; 0, t] by simp [slDiag], Matrix.mul_fin_two]
    simp
  have := congrArg Subtype.val (d.leviLongRep_bijective.1 hrep)
  rw [← hgval]
  exact this

theorem a2Hom_slN₁₂ (s : d.Γ₀) : d.a2Hom (slN₁₂ s) = d.u * d.a2Hom (slN₀₁ s) * d.u := by
  have h1 : d.a2 1 2 s = d.u * d.a2 0 1 s * d.u :=
    (d.u_conj_a2 (i := 0) (j := 1) (by decide) s).symm
  have h2 : d.a2 2 1 (-s⁻¹) = d.u * d.a2 1 0 (-s⁻¹) * d.u :=
    (d.u_conj_a2 (i := 1) (j := 0) (by decide) _).symm
  rw [slN₁₂, slN₀₁, map_mul, map_mul, map_mul, map_mul, d.a2Hom_transvection,
    d.a2Hom_transvection, d.a2Hom_transvection, d.a2Hom_transvection, h1, h2]
  calc d.u * d.a2 0 1 s * d.u * (d.u * d.a2 1 0 (-s⁻¹) * d.u) * (d.u * d.a2 0 1 s * d.u) =
      d.u * d.a2 0 1 s * (d.u * d.u) * d.a2 1 0 (-s⁻¹) * (d.u * d.u) * d.a2 0 1 s * d.u := by group
    _ = d.u * (d.a2 0 1 s * d.a2 1 0 (-s⁻¹) * d.a2 0 1 s) * d.u := by
        rw [d.u_mul_self, mul_one, mul_one]; group

theorem a2Hom_slN₁₂_mul {t : d.Γ₀} (ht : t ≠ 0) :
    d.a2Hom (slN₁₂ t * slN₁₂ (-1)) = d.u * d.hA (Units.mk0 t ht) * d.u := by
  rw [map_mul, d.a2Hom_slN₁₂, d.a2Hom_slN₁₂, ← d.a2Hom_slN₀₁_mul ht, map_mul]
  calc d.u * d.a2Hom (slN₀₁ t) * d.u * (d.u * d.a2Hom (slN₀₁ (-1)) * d.u) =
      d.u * d.a2Hom (slN₀₁ t) * (d.u * d.u) * d.a2Hom (slN₀₁ (-1)) * d.u := by group
    _ = d.u * (d.a2Hom (slN₀₁ t) * d.a2Hom (slN₀₁ (-1))) * d.u := by
        rw [d.u_mul_self, mul_one]; group

theorem u_hA_u (b : (d.Γ₀)ˣ) : d.u * d.hA b * d.u = d.torus (b⁻¹, d.unitsIncl b) := by
  rw [hA_apply, u_torus_eq, nmUnits_unitsIncl, map_inv, inv_inv]
  congr 2
  group

theorem a2Hom_scalar {ω : d.Γ₀} (hω0 : ω ≠ 0) :
    d.a2Hom ((slN₀₁ ω * slN₀₁ (-1)) * (slN₁₂ (ω ^ 2) * slN₁₂ (-1))) =
      d.torus (1, d.unitsIncl (Units.mk0 ω hω0)) := by
  have hω2 : ω ^ 2 ≠ 0 := pow_ne_zero 2 hω0
  rw [map_mul, d.a2Hom_slN₀₁_mul hω0, d.a2Hom_slN₁₂_mul hω2, d.u_hA_u, hA_apply, ← map_mul]
  have hu : Units.mk0 (ω ^ 2) hω2 = Units.mk0 ω hω0 ^ 2 := Units.ext (by simp)
  rw [hu]
  congr 1
  refine Prod.ext ?_ ?_
  · change Units.mk0 ω hω0 ^ 2 * (Units.mk0 ω hω0 ^ 2)⁻¹ = 1
    exact mul_inv_cancel _
  · change d.unitsIncl (Units.mk0 ω hω0)⁻¹ * d.unitsIncl (Units.mk0 ω hω0 ^ 2) =
      d.unitsIncl (Units.mk0 ω hω0)
    rw [← map_mul]
    congr 1
    group

theorem scalar_eq_slN_mul {ω : d.Γ₀} (hω : ω ^ 3 = 1) (A : SL(3, d.Γ₀))
    (hA : (A : Matrix (Fin 3) (Fin 3) d.Γ₀) = scalar (Fin 3) ω) :
    A = (slN₀₁ ω * slN₀₁ (-1)) * (slN₁₂ (ω ^ 2) * slN₁₂ (-1)) := by
  have hω0 : ω ≠ 0 := by
    rintro rfl
    simp at hω
  apply Subtype.ext
  change (A : Matrix (Fin 3) (Fin 3) d.Γ₀) = ((slN₀₁ ω * slN₀₁ (-1 : d.Γ₀) : SL(3, d.Γ₀)) :
    Matrix (Fin 3) (Fin 3) d.Γ₀) * ((slN₁₂ (ω ^ 2) * slN₁₂ (-1 : d.Γ₀) : SL(3, d.Γ₀)) :
    Matrix (Fin 3) (Fin 3) d.Γ₀)
  rw [coe_slN₀₁_mul hω0, coe_slN₁₂_mul (pow_ne_zero 2 hω0), hA, scalar_eq_diag_mul hω]

theorem a2Hom_injective : Function.Injective d.a2Hom := by
  refine (injective_iff_map_eq_one _).2 fun A hA => ?_
  have hZ : A ∈ center SL(3, d.Γ₀) := d.ker_a2Hom_le_center hA
  obtain ⟨ω, hω, hωA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hZ
  rw [Fintype.card_fin] at hω
  have hω0 : ω ≠ 0 := by
    rintro rfl
    simp at hω
  have hA' := d.scalar_eq_slN_mul hω A hωA.symm
  rw [hA', d.a2Hom_scalar hω0] at hA
  have h1 := congrArg Prod.snd (d.torus_injective (hA.trans (map_one d.torus).symm))
  have hω1 : Units.mk0 ω hω0 = 1 := d.unitsIncl_injective (h1.trans (map_one _).symm)
  have hω1' : ω = 1 := congrArg Units.val hω1
  apply Subtype.ext
  rw [← hωA, hω1', Matrix.SpecialLinearGroup.coe_one, scalar_apply, diagonal_one]

theorem a2HomLevi_bijective : Function.Bijective d.a2HomLevi :=
  ⟨fun _ _ h => d.a2Hom_injective (congrArg Subtype.val h), d.a2HomLevi_surjective⟩

noncomputable def leviJ₀EquivSL3 : d.leviJ₀ ≃* SL(3, d.Γ₀) :=
  (MulEquiv.ofBijective d.a2HomLevi d.a2HomLevi_bijective).symm

end TrialityD4Data

end CFSG.LocalAnalysis.EvenBN.TrialityD4
