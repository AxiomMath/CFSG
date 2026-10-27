module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3FusionOrbit
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryFixed
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherConjDescentForm

public section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (semilinearSimilitudes hypUnitary
  mem_hypUnitary glAut coe_glAut exists_unitary_rep scalar_gram conjFixed mem_conjFixed
  finite_conjFixed span_conjFixed_of_ne finrank_conjFixed_of_ne conjDescentForm
  conjDescentForm_apply conjDescentForm_nondegenerate exists_orthonormal_basis_of_charTwo
  map_bar_comm map_similitude SemiGL)

namespace OuterInvolution

section Abstract

variable {P : Type*} [Group P]

theorem conj_mul_conj_inv_eq_of_eq_mul (α : MulAut P) {w c : P} (hw : w = c * α w)
    (hc : α c = c) : MulAut.conj w * α * (MulAut.conj w)⁻¹ = α * MulAut.conj c := by
  have h1 : w * (α w)⁻¹ = c := by rw [mul_inv_eq_iff_eq_mul]; exact hw
  ext z
  simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply, map_mul, map_inv, hc]
  rw [← h1]
  group

theorem exists_fusion_of_conj (β u : MulAut P) {D : Subgroup P} (hD : ∀ z ∈ D, u z = z)
    (hperf : ⁅D, D⁆ = D) {c w : P} (hcD : c ∈ D) (hc1 : c ≠ 1) (hc2 : c * c = 1)
    (hw : w = c * u w) :
    ∃ D' : Subgroup P, (∀ z ∈ D', (β * u * β⁻¹) z = z) ∧ ⁅D', D'⁆ = D' ∧
      ∃ c' ∈ D', c' ≠ 1 ∧ c' * c' = 1 ∧ ∃ w' : P,
        MulAut.conj w' * (β * u * β⁻¹) * (MulAut.conj w')⁻¹ = β * u * β⁻¹ * MulAut.conj c' := by
  have hconj : ∀ z, (β * u * β⁻¹) (β z) = β (u z) := fun z => by
    simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply]
  refine ⟨D.map β.toMonoidHom, ?_, ?_, β c, ⟨c, hcD, rfl⟩, ?_, ?_, β w, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    change (β * u * β⁻¹) (β z) = β z
    rw [hconj, hD z hz]
  · rw [← Subgroup.map_commutator, hperf]
  · intro h1
    exact hc1 (β.injective (by rw [h1, map_one]))
  · rw [← map_mul, hc2, map_one]
  · refine conj_mul_conj_inv_eq_of_eq_mul _ ?_ (by rw [hconj, hD c hcD])
    rw [hconj, ← map_mul, ← hw]

end Abstract

section Model

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

@[expose] def fieldElt (σ : K ≃+* K) : Gam h :=
  ⟨⟨1, σ⟩, 1, one_ne_zero, map_one _, by simp⟩

@[expose] noncomputable def transF : SpecialLinearGroup (Fin 2) h.fixedField :=
  ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩

variable {h}

theorem mat_act_fieldElt (σ : K ≃+* K) (g : hypSU h 2 1) :
    mat (act h (fieldElt h σ) g) = (mat g).map σ := by
  change ((1 * glAut σ (g : GL (HypIndex 2 1) K) * 1⁻¹ : GL (HypIndex 2 1) K) :
    Matrix (HypIndex 2 1) (HypIndex 2 1) K) = _
  rw [one_mul, inv_one, mul_one, coe_glAut]
  rfl

theorem map_mul_ringEquiv {ι : Type*} [Fintype ι] (σ : K ≃+* K) (M N : Matrix ι ι K) :
    (M * N).map σ = M.map σ * N.map σ :=
  Matrix.map_mul (f := (σ : K →+* K))

theorem oddDiag_map (σ : K ≃+* K) {A : Matrix (Fin 2) (Fin 2) K} (hA : IsUnit A.det) (d : K) :
    (oddDiag h A d).map σ = oddDiag h (A.map σ) (σ d) := by
  have hc : (A.map h.bar).map σ = (A.map σ).map h.bar := by
    ext i j
    simp [map_bar_comm h σ]
  have hinv : ((A.map h.bar)⁻¹).map σ = ((A.map σ).map h.bar)⁻¹ := by
    rw [← hc]
    symm
    apply Matrix.inv_eq_right_inv
    rw [← map_mul_ringEquiv, Matrix.mul_nonsing_inv _ (isUnit_det_map hA),
      Matrix.map_one _ (map_zero σ) (map_one σ)]
  ext a b
  rcases a with i | k | i <;> rcases b with j | l | j <;>
    simp only [Matrix.map_apply, oddDiag, barInvT, blk3_inl_inl, blk3_inl_inr_inl,
      blk3_inl_inr_inr, blk3_inr_inl_inl, blk3_inr_inl_inr_inl, blk3_inr_inl_inr_inr,
      blk3_inr_inr_inl, blk3_inr_inr_inr_inl, blk3_inr_inr_inr_inr, Matrix.zero_apply,
      Matrix.of_apply, Matrix.transpose_apply, map_zero]
  exact congrFun (congrFun hinv j) i

theorem mat_lev_of_det_eq_one {A : Matrix (Fin 2) (Fin 2) K} (hA : IsUnit A.det)
    (h1 : A.det = 1) : mat (lev (hK := h) A hA) = oddDiag h A 1 := by
  rw [mat_lev, h1, map_one, div_one]

theorem det_map_fixedField (B : SpecialLinearGroup (Fin 2) h.fixedField) :
    ((B : Matrix (Fin 2) (Fin 2) h.fixedField).map h.fixedField.subtype).det = 1 := by
  have h1 : (h.fixedField.subtype.mapMatrix (B : Matrix (Fin 2) (Fin 2) h.fixedField)).det =
      h.fixedField.subtype (B : Matrix (Fin 2) (Fin 2) h.fixedField).det :=
    (RingHom.map_det _ _).symm
  rw [RingHom.mapMatrix_apply] at h1
  rw [h1, B.2, map_one]

theorem isUnit_det_map_fixedField (B : SpecialLinearGroup (Fin 2) h.fixedField) :
    IsUnit ((B : Matrix (Fin 2) (Fin 2) h.fixedField).map h.fixedField.subtype).det := by
  rw [det_map_fixedField]
  exact isUnit_one

variable (h)

@[expose] noncomputable def levF : SpecialLinearGroup (Fin 2) h.fixedField →* hypSU h 2 1 :=
  MonoidHom.mk' (fun B => lev (hK := h)
      ((B : Matrix (Fin 2) (Fin 2) h.fixedField).map h.fixedField.subtype)
      (isUnit_det_map_fixedField B))
    (fun B B' => mat_injective (by
      rw [mat_mul, mat_lev_of_det_eq_one _ (det_map_fixedField _),
        mat_lev_of_det_eq_one _ (det_map_fixedField _),
        mat_lev_of_det_eq_one _ (det_map_fixedField _), oddDiag_mul, one_mul,
        ← Matrix.map_mul]
      rfl))

@[expose] noncomputable def levD : Subgroup (hypPSU h 2 1) :=
  ((hypProj h 2 1).comp (levF h)).range

variable {h}

theorem mat_levF (B : SpecialLinearGroup (Fin 2) h.fixedField) :
    mat (levF h B) =
      oddDiag h ((B : Matrix (Fin 2) (Fin 2) h.fixedField).map h.fixedField.subtype) 1 :=
  mat_lev_of_det_eq_one (isUnit_det_map_fixedField B) (det_map_fixedField B)

theorem levD_perfect (hf : 2 ≤ f) : ⁅levD h, levD h⁆ = levD h := by
  have := h.finite
  have hcard : 4 ≤ Nat.card h.fixedField := by
    rw [h.card_fixedField]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card h.fixedField hcard
  rw [levD, MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def,
    Group.IsPerfect.commutator_eq_top]

theorem fieldElt_fusion (hf : 2 ≤ f) {σ : K ≃+* K} (hσ : ∀ c, σ c = h.bar c) :
    (∀ z ∈ levD h, Phi h (fieldElt h σ) z = z) ∧ ⁅levD h, levD h⁆ = levD h ∧
      ∃ c ∈ levD h, c ≠ 1 ∧ c * c = 1 ∧ ∃ w, w = c * Phi h (fieldElt h σ) w := by
  have : CharP K 2 := h.charP
  have hfixF : ∀ B, act h (fieldElt h σ) (levF h B) = levF h B := by
    intro B
    apply mat_injective
    rw [mat_act_fieldElt, mat_levF, oddDiag_map σ (isUnit_det_map_fixedField B), map_one]
    congr 1
    ext i j
    simp only [Matrix.map_apply, hσ]
    exact (B i j).2
  refine ⟨?_, levD_perfect hf, ?_⟩
  · rintro _ ⟨B, rfl⟩
    change Phi h (fieldElt h σ) (hypProj h 2 1 (levF h B)) = hypProj h 2 1 (levF h B)
    rw [Phi_apply, hfixF]
  · obtain ⟨s, hs⟩ := trace_surj (hK := h) (a := 1) (map_one _)
    have hX : (!![1, s; 0, 1] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
      simp [Matrix.det_fin_two_of]
    have hXu : IsUnit (!![1, s; 0, 1] : Matrix (Fin 2) (Fin 2) K).det := by
      rw [hX]; exact isUnit_one
    refine ⟨hypProj h 2 1 (levF h (transF h)), ⟨transF h, rfl⟩, ?_, ?_,
      hypProj h 2 1 (lev (hK := h) !![1, s; 0, 1] hXu), ?_⟩
    · intro h1
      have h2 : levF h (transF h) ∈ hypScalars h 2 1 := by
        rw [← ker_hypProj]
        exact h1
      obtain ⟨c, -, -, hc⟩ := h2
      have h3 := congrArg (fun g : GL (HypIndex 2 1) K =>
        (g : Matrix (HypIndex 2 1) (HypIndex 2 1) K) (.inl 0) (.inl 1)) hc
      change mat (levF h (transF h)) (.inl 0) (.inl 1) = _ at h3
      rw [mat_levF] at h3
      simp [oddDiag, transF, GeneralLinearGroup.coe_scalar] at h3
    · rw [← map_mul, ← map_mul]
      have : transF h * transF h = 1 := by
        apply Subtype.ext
        change (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) h.fixedField) * !![1, 1; 0, 1] = 1
        rw [Matrix.mul_fin_two, Matrix.one_fin_two]
        simp [CharTwo.add_self_eq_zero]
      rw [this, map_one, map_one]
    · rw [Phi_apply, ← map_mul]
      congr 1
      apply mat_injective
      rw [mat_mul, mat_act_fieldElt, mat_lev_of_det_eq_one _ hX, mat_levF, oddDiag_map σ hXu,
        oddDiag_mul, map_one, one_mul]
      congr 1
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [transF, Matrix.mul_apply, Fin.sum_univ_two, hσ]
      linear_combination hs - h.bar s * CharTwo.two_eq_zero (R := K)

end Model

section Descent

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

@[expose] noncomputable def antiMap (A : Matrix (HypIndex 2 1) (HypIndex 2 1) K) :
    (HypIndex 2 1 → K) →ₛₗ[h.bar] (HypIndex 2 1 → K) where
  toFun v := A *ᵥ fun i => h.bar (v i)
  map_add' v w := by
    rw [← mulVec_add]
    congr 1
    funext i
    exact map_add h.bar (v i) (w i)
  map_smul' a v := by
    rw [← mulVec_smul]
    congr 1
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]

@[expose] def P0 : Matrix (Fin 5) (HypIndex 2 1) (ZMod 2) :=
  Matrix.of fun i a => match a with
    | .inl 0 => ![1, 1, 0, 0, 0] i
    | .inl 1 => ![0, 0, 0, 1, 1] i
    | .inr (.inl _) => ![1, 1, 1, 1, 1] i
    | .inr (.inr 0) => ![0, 1, 1, 0, 0] i
    | .inr (.inr 1) => ![1, 1, 1, 1, 0] i

theorem P0_gram : P0ᵀ * P0 = hypGram 2 1 (ZMod 2) := by decide

variable {h}

theorem bar_mulVec (N : Matrix (HypIndex 2 1) (HypIndex 2 1) K) (v : HypIndex 2 1 → K) :
    (fun i => h.bar ((N *ᵥ v) i)) = N.map h.bar *ᵥ fun i => h.bar (v i) :=
  funext fun i => RingHom.map_mulVec h.bar N v i

theorem exists_bar_rep {α : MulAut (hypPSU h 2 1)} (hα : α * α = 1) (hαP : α ∉ Pi h) :
    ∃ x : Gam h, Phi h x = α ∧ (∀ c, x.1.right c = h.bar c) ∧
      ((lmat x).map h.bar)ᵀ * hypGram 2 1 K * lmat x = hypGram 2 1 K ∧
      lmat x * (lmat x).map h.bar = 1 := by
  have : CharP K 2 := h.charP
  obtain ⟨x₀, hx₀⟩ := Phi_surjective h α
  obtain ⟨x, hxΦ, -, hxU⟩ := exists_unitary_rep h (r := 2) (ε := 1) (by norm_num) le_rfl
    (by norm_num) x₀
  have hx : Phi h x = α := by
    have h1 : Phi h x = Phi h x₀ := hxΦ
    rw [h1, hx₀]
  have hbar : ∀ c, x.1.right c = h.bar c := by
    rcases right_sq_of_sq hα hx with h1 | h1
    · exact absurd (Dlin_two_mem_Pi ((mem_Dlin_iff hx).2 h1) (k := 1)
        (by rw [pow_one, pow_two]; exact hα)) hαP
    · exact h1
  have hU : ((lmat x).map h.bar)ᵀ * hypGram 2 1 K * lmat x = hypGram 2 1 K := hxU
  refine ⟨x, hx, hbar, hU, ?_⟩
  have h1 : Phi h (x * x) = 1 := by rw [map_mul, hx, hα]
  obtain ⟨-, c, hc⟩ := Phi_eq_one_iff.1 h1
  have hσU : glAut x.1.right x.1.left ∈ hypUnitary h 2 1 := by
    rw [mem_hypUnitary, coe_glAut]
    have h2 := map_similitude h (μ := 1) (by rw [one_smul]; exact hU) x.1.right
    rwa [map_one, one_smul] at h2
  have hcU : GeneralLinearGroup.scalar (HypIndex 2 1) c ∈ hypUnitary h 2 1 := by
    rw [← hc]
    exact mul_mem hxU hσU
  have hN : h.norm (c : K) = 1 := by
    have h2 := mem_hypUnitary.1 hcU
    rw [GeneralLinearGroup.coe_scalar, scalar_gram h (c : K)] at h2
    have := congrFun (congrFun h2 (.inl 0)) (.inr (.inr 0))
    simpa using this
  set Am := lmat x with hAm
  have hmap : Am.map x.1.right = Am.map h.bar := Matrix.ext fun i j => hbar _
  have hc' : Am * Am.map h.bar = Matrix.scalar (HypIndex 2 1) (c : K) := by
    have h2 := congrArg (fun g : GL (HypIndex 2 1) K =>
      (g : Matrix (HypIndex 2 1) (HypIndex 2 1) K)) hc
    simp only [Subgroup.coe_mul, SemidirectProduct.mul_left, Units.val_mul, coe_glAut,
      GeneralLinearGroup.coe_scalar] at h2
    rw [← hmap]
    exact h2
  have hAinv : (((x.1.left⁻¹ : GL (HypIndex 2 1) K)) :
      Matrix (HypIndex 2 1) (HypIndex 2 1) K) * Am = 1 := by
    rw [hAm, lmat, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hbarbar : (Am.map h.bar).map h.bar = Am := Matrix.ext fun i j => h.bar_bar _
  have h3 : Am.map h.bar * Am = Matrix.scalar (HypIndex 2 1) (h.bar (c : K)) := by
    have h4 := congrArg (fun N => N.map h.bar) hc'
    simp only [Matrix.map_mul, hbarbar] at h4
    rw [h4, scalar_apply, scalar_apply, diagonal_map (map_zero h.bar)]
  have h5 : Am.map h.bar * Am = Matrix.scalar (HypIndex 2 1) (c : K) := by
    calc Am.map h.bar * Am
        = (((x.1.left⁻¹ : GL (HypIndex 2 1) K)) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) *
            (Am * Am.map h.bar) * Am := by rw [← Matrix.mul_assoc, hAinv, Matrix.one_mul]
      _ = Matrix.scalar (HypIndex 2 1) (c : K) := by
          rw [hc', Matrix.mul_assoc,
            ((Matrix.scalar_commute (c : K) (fun r => Commute.all (c : K) r)) Am).eq,
            ← Matrix.mul_assoc, hAinv, Matrix.one_mul]
  have hbarc : h.bar (c : K) = c := by
    have h6 := congrFun (congrFun (h3.symm.trans h5) (.inl 0)) (.inl 0)
    simpa using h6
  have hc1 : (c : K) = 1 := by
    have hsq : (c : K) * c = 1 := by
      have h7 : h.norm (c : K) = (c : K) * h.bar c := rfl
      rw [h7, hbarc] at hN
      exact hN
    rcases mul_self_eq_one_iff.mp hsq with h8 | h8
    · exact h8
    · rw [h8, CharTwo.neg_eq]
  rw [hc', hc1, map_one]

theorem exists_descent {A : Matrix (HypIndex 2 1) (HypIndex 2 1) K}
    (hU : (A.map h.bar)ᵀ * hypGram 2 1 K * A = hypGram 2 1 K) (hA : A * A.map h.bar = 1) :
    ∃ M : Matrix (HypIndex 2 1) (HypIndex 2 1) K,
      (M.map h.bar)ᵀ * hypGram 2 1 K * M = hypGram 2 1 K ∧ A * M.map h.bar = M ∧ M.det ≠ 0 := by
  have : CharP K 2 := h.charP
  have : Finite K := h.finite
  set τ := antiMap h A with hτ
  have hτv : ∀ v, τ v = A *ᵥ fun i => h.bar (v i) := fun v => rfl
  have hττ : ∀ v, τ (τ v) = v := by
    intro v
    rw [hτv, hτv, bar_mulVec, mulVec_mulVec, hA, one_mulVec]
    funext i
    exact h.bar_bar (v i)
  have hform : ∀ v w, hypForm h 2 1 (τ v) (τ w) = h.bar (hypForm h 2 1 v w) := by
    intro v w
    rw [hτv, hτv, gramForm_mulVec, hU]
    change hypForm h 2 1 _ _ = _
    rw [hypForm_apply, hypForm_apply, map_sum]
    simp only [map_mul, h.bar_bar]
  have hc1 : ∀ v w, v ∈ conjFixed h τ → w ∈ conjFixed h τ →
      h.bar (1 * hypForm h 2 1 v w) = 1 * hypForm h 2 1 v w := by
    intro v w hv hw
    rw [one_mul, ← hform, mem_conjFixed.1 hv, mem_conjFixed.1 hw]
  obtain ⟨c₀, hc₀⟩ := h.exists_bar_ne
  have hspan := span_conjFixed_of_ne hττ hc₀
  have hfin : Module.finrank h.fixedField (conjFixed h τ) = 5 := by
    rw [finrank_conjFixed_of_ne hττ hc₀, Module.finrank_fintype_fun_eq_card]
    rfl
  have : FiniteDimensional h.fixedField (conjFixed h τ) := finite_conjFixed
  set B := conjDescentForm (hypForm h 2 1) τ 1 hc1 with hBdef
  have hBapply : ∀ v w, (B v w : K) = hypForm h 2 1 v w := fun v w => by
    rw [hBdef, conjDescentForm_apply, one_mul]
  have hBnd : B.Nondegenerate := conjDescentForm_nondegenerate (hypForm_isSymm h)
    (hypForm_separatingLeft h) hspan one_ne_zero hc1
  have hHerm : (hypForm h 2 1).IsSymm := hypForm_isSymm h
  have hBsymm : B.IsSymm := ⟨fun v w => Subtype.ext (by
    rw [hBapply, hBapply, ← hHerm.eq v w]
    have h1 := hc1 v w v.2 w.2
    rw [one_mul] at h1
    exact h1.symm)⟩
  have halt : ∃ v, B v v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hev := LinearMap.BilinForm.IsAlt.even_finrank (B := B) hcon hBnd
    rw [hfin] at hev
    exact absurd hev (by decide)
  have hsq : ∀ a : h.fixedField, IsSquare a :=
    FiniteField.isSquare_of_char_two (ringChar.eq h.fixedField 2)
  obtain ⟨b, hb⟩ := exists_orthonormal_basis_of_charTwo hsq hBsymm hBnd (Or.inr halt)
  set b' := b.reindex (finCongr hfin) with hb'
  have hb'B : ∀ i j, B (b' i) (b' j) = if i = j then 1 else 0 := by
    intro i j
    rw [hb', Module.Basis.reindex_apply, Module.Basis.reindex_apply, hb]
    simp only [(finCongr hfin).symm.injective.eq_iff]
  set H : Matrix (HypIndex 2 1) (Fin 5) K := Matrix.of fun a i => (b' i : HypIndex 2 1 → K) a
    with hH
  have hHcol : ∀ i, H *ᵥ Pi.single i 1 = (b' i : HypIndex 2 1 → K) := by
    intro i
    rw [mulVec_single_one]
    funext a
    rfl
  have hHgram : (H.map h.bar)ᵀ * hypGram 2 1 K * H = 1 := by
    ext i j
    rw [← gramForm_single h ((H.map h.bar)ᵀ * hypGram 2 1 K * H) i j, ← gramForm_mulVec, hHcol,
      hHcol]
    change hypForm h 2 1 _ _ = _
    rw [← hBapply, hb'B, one_apply]
    split_ifs <;> rfl
  have hAH : A * H.map h.bar = H := by
    ext a i
    have h1 : τ (b' i) = b' i := mem_conjFixed.mp (b' i).2
    have h2 := congrFun h1 a
    rw [hτv] at h2
    simp only [hH, Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply]
    rw [← h2]
    rfl
  set ι : ZMod 2 →+* K := ZMod.castHom (dvd_refl 2) K with hι
  set P : Matrix (Fin 5) (HypIndex 2 1) K := P0.map ι with hP
  have hPbar : P.map h.bar = P := by
    rw [hP, Matrix.map_map]
    congr 1
    exact congrArg DFunLike.coe (RingHom.ext_zmod (h.bar.comp ι) ι)
  have hPgram : Pᵀ * P = hypGram 2 1 K := by
    rw [hP, ← Matrix.transpose_map, ← Matrix.map_mul, P0_gram, hypGram_map]
  have hM1 : ((H * P).map h.bar)ᵀ * hypGram 2 1 K * (H * P) = hypGram 2 1 K := by
    rw [Matrix.map_mul, Matrix.transpose_mul, hPbar]
    calc Pᵀ * (H.map h.bar)ᵀ * hypGram 2 1 K * (H * P)
        = Pᵀ * ((H.map h.bar)ᵀ * hypGram 2 1 K * H) * P := by simp only [Matrix.mul_assoc]
      _ = hypGram 2 1 K := by rw [hHgram, Matrix.mul_one, hPgram]
  refine ⟨H * P, hM1, ?_, ?_⟩
  · rw [Matrix.map_mul, hPbar, ← Matrix.mul_assoc, hAH]
  · intro h0
    have h1 := congrArg Matrix.det hM1
    rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at h1
    exact det_hypGram_ne_zero h1.symm

end Descent

end OuterInvolution

open OuterInvolution

variable {f : ℕ} {K : Type} [Field K]

theorem exists_eq_conj_fieldElt {h : UnitaryFieldData 2 f K} {α : MulAut (hypPSU h 2 1)}
    (hα : α * α = 1) (hαP : α ∉ Pi h) :
    ∃ σ : K ≃+* K, (∀ c, σ c = h.bar c) ∧ ∃ β ∈ Dlin h, α = β * Phi h (fieldElt h σ) * β⁻¹ := by
  obtain ⟨x, hx, hbar, hU, hAA⟩ := exists_bar_rep hα hαP
  obtain ⟨M, hMU, hAM, hdet⟩ := exists_descent hU hAA
  set Mg : GL (HypIndex 2 1) K := GeneralLinearGroup.mkOfDetNeZero M hdet
  have hyΓ : (SemidirectProduct.inl Mg : SemiGL (HypIndex 2 1) K) ∈
      semilinearSimilitudes h 2 1 :=
    ⟨1, one_ne_zero, map_one _, by rw [one_smul]; exact hMU⟩
  set y : Gam h := ⟨_, hyΓ⟩ with hy
  set u : Gam h := fieldElt h x.1.right with hu
  have hxy : x * y = y * u := by
    apply Subtype.ext
    apply SemidirectProduct.ext
    · simp only [Subgroup.coe_mul, SemidirectProduct.mul_left, hy, hu, fieldElt,
        SemidirectProduct.left_inl, SemidirectProduct.right_inl, map_one, mul_one]
      apply Units.ext
      rw [Units.val_mul, coe_glAut]
      have hmap : M.map x.1.right = M.map h.bar := Matrix.ext fun i j => hbar _
      change lmat x * M.map x.1.right = M
      rw [hmap, hAM]
    · simp only [Subgroup.coe_mul, SemidirectProduct.mul_right, hy, hu, fieldElt,
        SemidirectProduct.right_inl, mul_one, one_mul]
  refine ⟨x.1.right, hbar, Phi h y, ⟨y, mem_Gam1.2 rfl, rfl⟩, ?_⟩
  rw [← hx, ← map_mul, ← map_inv, ← map_mul, ← hxy, mul_inv_cancel_right]

theorem outerInvolutionFusion (h : UnitaryFieldData 2 f K) : OuterInvolutionFusion h := by
  intro hf _ α hα hαP
  obtain ⟨σ, hσ, β, -, rfl⟩ := exists_eq_conj_fieldElt hα hαP
  obtain ⟨hfix, hperf, c, hcD, hc1, hc2, w, hw⟩ := fieldElt_fusion hf hσ
  exact exists_fusion_of_conj β (Phi h (fieldElt h σ)) hfix hperf hcD hc1 hc2 hw

namespace Data

variable {G : Type} [Group G] [Finite G] {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem Hyp.sec3_1' (hd : d.Hyp) :
    centralizer (d.L : Set G) ⊓ centralizer ({d.t} : Set G) = zpowers d.t ∧
      (∀ X : Subgroup G, X ≤ centralizer ({d.t} : Set G) → CFSG.IsElementaryAbelian 2 X →
        Nat.card X ≤ 2 * (2 ^ f) ^ 4) ∧
      (∀ X : Subgroup G, X ≤ d.T → CFSG.IsElementaryAbelian 2 X →
        Nat.card X = 2 * (2 ^ f) ^ 4 → X = d.B₁) ∧
      {x | ∃ n ∈ normalizer (d.B₃ : Set G), x = n⁻¹ * d.t * n} =
        {x | ∃ a ∈ d.A₁, x = d.t * a} ∧
      {x | ∃ g : G, x = g⁻¹ * d.t * g} ∩ (d.B₁ : Set G) = {x | ∃ a ∈ d.A₁, x = d.t * a} ∧
      ∀ g : G, g⁻¹ * d.t * g ∉ d.L :=
  hd.sec3_1 (outerInvolutionFusion h)

end Data

end CFSG.LocalAnalysis.EvenBN.U5
