module

public import CFSG.LocalAnalysis.ComponentInitial.UnitarySixFieldTwoAutInner
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryDescent

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitarySixFieldTwoAut

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {F : Type} [Field F] (h : UnitaryFieldData 2 1 F)

theorem three_le_six : 3 ≤ 6 := by norm_num

theorem not_six_eq_three : ¬(6 = 3 ∧ 2 ^ 1 = 2) := by norm_num

noncomputable abbrev sixFieldFactor : MulAut (sixQ h) →* (F ≃+* F) :=
  primeFormFieldFactor h (isPrimeFormGram_sixJ h) three_le_six not_six_eq_three

noncomputable abbrev t0U : sixU h :=
  ⟨t0Elt h, (t0Elt h).2.1⟩

@[expose] noncomputable def alphaOne : MulAut (sixQ h) :=
  MulAut.conj (sixProj h (t0Elt h)) * sigmaQ h

theorem conj_sixProj_eq (s : sixS h) :
    MulAut.conj (sixProj h s) =
      primeFormConjHom h (sixJ h : Matrix (Fin 6) (Fin 6) F) ⟨s, s.2.1⟩ :=
  (primeFormConjHom_eq_conj h (sixJ h : Matrix (Fin 6) (Fin 6) F) s).symm

theorem alphaOne_eq : alphaOne h = primeFormConjHom h _ (t0U h) *
    primeFormFieldHom h (isPrimeFormGram_sixJ h) (barEquiv h) := by
  rw [alphaOne, conj_sixProj_eq]
  rfl

theorem sixFieldFactor_alphaOne : sixFieldFactor h (alphaOne h) = barEquiv h := by
  rw [alphaOne_eq]
  exact primeFormFieldFactor_apply h _ _ _ _ _

theorem sixFieldFactor_sigmaQ : sixFieldFactor h (sigmaQ h) = barEquiv h := by
  have := primeFormFieldFactor_apply h (isPrimeFormGram_sixJ h) three_le_six not_six_eq_three 1
    (barEquiv h)
  rwa [map_one, one_mul] at this

theorem barEquiv_ne_one : barEquiv h ≠ 1 := by
  intro h1
  obtain ⟨c, hc⟩ := h.exists_bar_ne
  exact hc (by rw [← barEquiv_eq_bar, h1]; rfl)

noncomputable abbrev sigmaS : sixS h ≃* sixS h :=
  primeFormFieldSU h (isPrimeFormGram_sixJ h) (barEquiv h)

theorem coe_sigmaS (g : sixS h) :
    ((sigmaS h g : sixS h) : GL (Fin 6) F) = glAut (barEquiv h) g :=
  rfl

theorem sigmaQ_sixProj' (g : sixS h) : sigmaQ h (sixProj h g) = sixProj h (sigmaS h g) :=
  sigmaQ_sixProj h g

theorem sigmaS_sigmaS (g : sixS h) : sigmaS h (sigmaS h g) = g := by
  refine Subtype.ext ?_
  rw [coe_sigmaS, coe_sigmaS, ← MulAut.mul_apply, ← map_mul, barEquiv_mul_self, map_one,
    MulAut.one_apply]

theorem sigmaS_eq_self_iff (g : sixS h) : sigmaS h g = g ↔ g ∈ binarySp h := by
  rw [mem_binarySp_iff_glAut, ← coe_sigmaS]
  exact ⟨fun h1 => by rw [h1], fun h1 => Subtype.ext h1⟩

theorem mem_bot_of_ite (p : Prop) [Decidable p] :
    (if p then (1 : F) else 0) ∈ (⊥ : Subfield F) := by
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem nMat_apply_mem_bot {B : Matrix (Fin 3) (Fin 3) F} (hB : ∀ i j, B i j ∈ (⊥ : Subfield F))
    (a b : Fin 6) : nMat B a b ∈ (⊥ : Subfield F) := by
  rw [nMat, reindex_apply, submatrix_apply]
  rcases sixEquiv.symm a with i | i <;> rcases sixEquiv.symm b with j | j
  · rw [fromBlocks_apply₁₁, one_apply]
    exact mem_bot_of_ite _
  · rw [fromBlocks_apply₁₂]
    exact hB i j
  · rw [fromBlocks_apply₂₁, Matrix.zero_apply]
    exact zero_mem _
  · rw [fromBlocks_apply₂₂, one_apply]
    exact mem_bot_of_ite _

theorem tElt_mem_binarySp (k : ℕ) : tElt h k ∈ binarySp h := by
  rw [mem_binarySp_iff]
  intro a b
  refine nMat_apply_mem_bot (fun i j => ?_) a b
  rw [dMat, diagonal_apply]
  split_ifs <;> first | exact one_mem _ | exact zero_mem _

theorem t0Elt_mem_binarySp : t0Elt h ∈ binarySp h :=
  tElt_mem_binarySp h 1

theorem t0Elt_mul_self : t0Elt h * t0Elt h = 1 :=
  nElt_mul_self h (dMat 1) (dMat_hermitian h 1)

theorem alphaOne_sixProj (g : sixS h) :
    alphaOne h (sixProj h g) = sixProj h (t0Elt h * sigmaS h g * (t0Elt h)⁻¹) := by
  rw [alphaOne, MulAut.mul_apply, sigmaQ_sixProj', MulAut.conj_apply, map_mul, map_mul, map_inv]

theorem alphaOne_mul_self : alphaOne h * alphaOne h = 1 := by
  refine MulEquiv.ext fun x => ?_
  obtain ⟨g, rfl⟩ := sixProj_surjective h x
  rw [MulAut.mul_apply, alphaOne_sixProj, alphaOne_sixProj, MulAut.one_apply]
  congr 1
  have ht : (t0Elt h)⁻¹ = t0Elt h := inv_eq_of_mul_eq_one_right (t0Elt_mul_self h)
  have hσt : sigmaS h (t0Elt h) = t0Elt h := (sigmaS_eq_self_iff h _).mpr (t0Elt_mem_binarySp h)
  rw [map_mul, map_mul, map_inv, sigmaS_sigmaS, hσt, ht]
  calc t0Elt h * (t0Elt h * g * t0Elt h) * t0Elt h =
        (t0Elt h * t0Elt h) * g * (t0Elt h * t0Elt h) := by group
    _ = g := by rw [t0Elt_mul_self, one_mul, mul_one]

theorem orderOf_alphaOne : orderOf (alphaOne h) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime (by rw [sq, alphaOne_mul_self]) fun h1 => ?_
  have := sixFieldFactor_alphaOne h
  rw [h1, map_one] at this
  exact barEquiv_ne_one h this.symm

theorem exists_conj_eq_conj_tElt (α : MulAut (sixQ h)) (hα : orderOf α = 2)
    (hφ : sixFieldFactor h α = RingEquiv.refl F) :
    ∃ (A : sixU h) (k : ℕ), (k = 1 ∨ k = 2 ∨ k = 3) ∧
      primeFormConjHom h _ A * α * (primeFormConjHom h _ A)⁻¹ =
        MulAut.conj (sixProj h (tElt h k)) := by
  obtain ⟨s, hs1, hss, hαs⟩ := exists_sq_eq_one_of_fieldFactor_eq_one h (isPrimeFormGram_sixJ h)
    three_le_six not_six_eq_three α hα hφ
  have hs1' : s ≠ 1 := fun h1 => hs1 (by rw [h1]; rfl)
  have hss' : s * s = 1 := Subtype.ext hss
  obtain ⟨g, k, hk, hg⟩ := exists_conj_tElt_of_involution h s hss' hs1'
  refine ⟨⟨(g⁻¹ : sixS h), (g⁻¹ : sixS h).2.1⟩, k, hk, ?_⟩
  rw [hαs, conj_sixProj_eq, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  refine Subtype.ext ?_
  rw [← hg]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
  group

theorem exists_conj_eq_of_descents {α α₁ : MulAut (sixQ h)} {H H₁ : GL (Fin 6) F}
    (hH : ((H : Matrix (Fin 6) (Fin 6) F).map h.bar)ᵀ * (sixJ h : Matrix (Fin 6) (Fin 6) F) *
      (H : Matrix (Fin 6) (Fin 6) F) = ((1 : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F))
    (hH₁ : ((H₁ : Matrix (Fin 6) (Fin 6) F).map h.bar)ᵀ * (sixJ h : Matrix (Fin 6) (Fin 6) F) *
      (H₁ : Matrix (Fin 6) (Fin 6) F) = ((1 : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F))
    {θ θ₁ : primeFormP h ((1 : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) ≃* sixQ h}
    (hθ : ∀ (g : gramSU h ((1 : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)) (g' : sixS h),
      (g' : GL (Fin 6) F) = H * g * H⁻¹ → θ (g : primeFormP h _) = g')
    (hθ₁ : ∀ (g : gramSU h ((1 : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)) (g' : sixS h),
      (g' : GL (Fin 6) F) = H₁ * g * H₁⁻¹ → θ₁ (g : primeFormP h _) = g')
    {f : MulAut (primeFormP h ((1 : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F))}
    (hα : ∀ x, α x = θ (f (θ.symm x))) (hα₁ : ∀ x, α₁ x = θ₁ (f (θ₁.symm x))) :
    ∃ A : sixU h, primeFormConjHom h _ A * α * (primeFormConjHom h _ A)⁻¹ = α₁ := by
  have hMU : H * H₁⁻¹ ∈ sixU h := by
    rw [mem_primeFormUnitary, Units.val_mul, barTranspose_mul_mul, hH]
    exact inv_gram_eq h hH₁
  set M : sixU h := ⟨H * H₁⁻¹, hMU⟩ with hM
  have hγ : ∀ x, θ (θ₁.symm x) = primeFormConjHom h _ M x := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    set g₀ : gramSU h ((1 : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) :=
      ⟨H₁⁻¹ * g * H₁⁻¹⁻¹, conj_mem_gramSU_of_gram h (inv_gram_eq h hH₁) g.2⟩ with hg₀
    have h1 : θ₁.symm (g : sixQ h) = (g₀ : primeFormP h _) := by
      rw [MulEquiv.symm_apply_eq]
      refine (hθ₁ g₀ g ?_).symm
      rw [hg₀]
      group
    rw [h1, hθ g₀ ⟨_, conj_mem_gramSU_of_gram h hH g₀.2⟩ rfl, primeFormConjHom_mk]
    congr 1
    refine Subtype.ext ?_
    rw [hg₀, hM]
    group
  refine ⟨M⁻¹, ?_⟩
  refine MulEquiv.ext fun x => ?_
  rw [map_inv, inv_inv, MulAut.mul_apply, MulAut.mul_apply, hα, ← hγ]
  have h2 : f (θ.symm (θ (θ₁.symm x))) = θ₁.symm (α₁ x) := by
    rw [MulEquiv.symm_apply_apply, hα₁, MulEquiv.symm_apply_apply]
  have h3 : (primeFormConjHom h _ M)⁻¹ (θ (θ₁.symm (α₁ x))) = α₁ x := by
    rw [hγ, ← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
  rw [h2, h3]

theorem exists_fixed_norm_one_of_psi_eq (ω : F) (hω : ω ^ 2 + ω + 1 = 0) (A : sixU h)
    (hA : primeFormPsi h (isPrimeFormGram_sixJ h) ⟨A, barEquiv h⟩ = alphaOne h) :
    ∃ x : Fin 6 → F, antiunitaryMap h ((A : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) x = x ∧
      gramForm h (sixJ h : Matrix (Fin 6) (Fin 6) F) x x = 1 := by
  have := h.charP
  have hcA : primeFormConjHom h _ A = primeFormConjHom h _ (t0U h) := by
    rw [primeFormPsi_apply, alphaOne_eq] at hA
    exact mul_right_cancel hA
  have hker : primeFormPsi h (isPrimeFormGram_sixJ h) ⟨(t0U h)⁻¹ * A, 1⟩ = 1 := by
    rw [primeFormPsi_apply, map_one, mul_one, map_mul, hcA, map_inv, inv_mul_cancel]
  obtain ⟨-, c, -, hc⟩ := (primeFormPsi_eq_one_iff h (isPrimeFormGram_sixJ h) three_le_six _).mp
    hker
  have hAc : ((A : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
      nMat (dMat 1) * Matrix.scalar (Fin 6) (c : F) := by
    have h1 : (A : GL (Fin 6) F) = (t0Elt h : GL (Fin 6) F) *
        Matrix.GeneralLinearGroup.scalar (Fin 6) c := by
      rw [← hc]
      change (A : GL (Fin 6) F) = (t0Elt h : GL (Fin 6) F) *
        ((t0Elt h : GL (Fin 6) F)⁻¹ * (A : GL (Fin 6) F))
      rw [mul_inv_cancel_left]
    rw [h1, Units.val_mul, GeneralLinearGroup.coe_scalar]
    rfl
  set v : Fin 6 → F := ![ω, 0, 0, 1, 0, 0] with hv
  have hc3 := pow_three_eq_one h c.ne_zero
  have h2 := two_eq_zero h
  have hω' : ω ^ 2 + 1 = ω := by linear_combination hω - ω * h2
  refine ⟨((c : F) ^ 2) • v, ?_, ?_⟩
  · rw [antiunitaryMap_apply, hAc, ← mulVec_mulVec, nMat_dMat_one]
    funext i
    fin_cases i <;>
      simp [hv, mulVec, dotProduct, Fin.sum_univ_six, scalar_apply, diagonal_apply,
        one_apply, single_apply, bar_eq_sq h]
    · linear_combination ((c : F) ^ 2 * (ω ^ 2 + 1)) * hc3 + (c : F) ^ 2 * hω'
    · linear_combination (c : F) ^ 2 * hc3
  · rw [gramForm_sixJ]
    simp [hv, bar_eq_sq h]
    linear_combination (c : F) ^ 6 * hω - ((c : F) ^ 3 + 1) * hc3 - h2

theorem exists_conj_eq_of_fieldFactor_bar (ω : F) (hω : ω ^ 2 + ω + 1 = 0)
    (α : MulAut (sixQ h)) (hα : orderOf α = 2) (hφ : ∀ x, sixFieldFactor h α x = h.bar x) :
    ∃ A : sixU h, primeFormConjHom h _ A * α * (primeFormConjHom h _ A)⁻¹ = sigmaQ h ∨
      primeFormConjHom h _ A * α * (primeFormConjHom h _ A)⁻¹ = alphaOne h := by
  have hφe : sixFieldFactor h α = barEquiv h := RingEquiv.ext hφ
  obtain ⟨A, H, C₀, hC₀, hcase, -, -, hHgram, -, ⟨θ, hθmk, hθα⟩, -⟩ :=
    even_unitary_antiunitary_involution_descent h (isPrimeFormGram_sixJ h) three_le_six
      not_six_eq_three α hα hφ
  rw [hφe] at hθα
  rcases hcase with hC₀1 | ⟨r, hr, hC₀J⟩
  ·
    have hC₀eq : C₀ = 1 := Units.ext (by rw [hC₀1, Units.val_one])
    subst hC₀eq
    have hφ₁ : ∀ x, sixFieldFactor h (alphaOne h) x = h.bar x := by
      intro x
      rw [sixFieldFactor_alphaOne]
      rfl
    obtain ⟨A₁, H₁, C₁, hC₁, hcase₁, hαA₁, -, hH₁gram, -, ⟨θ₁, hθ₁mk, hθ₁α⟩, B₁, hB₁, -, -, -,
      hiff₁⟩ := even_unitary_antiunitary_involution_descent h (isPrimeFormGram_sixJ h)
        three_le_six not_six_eq_three (alphaOne h) (orderOf_alphaOne h) hφ₁
    rw [sixFieldFactor_alphaOne] at hθ₁α hαA₁
    rcases hcase₁ with hC₁1 | hC₁J
    · have hC₁eq : C₁ = 1 := Units.ext (by rw [hC₁1, Units.val_one])
      subst hC₁eq
      obtain ⟨M, hM⟩ := exists_conj_eq_of_descents h hHgram hH₁gram hθmk hθ₁mk hθα hθ₁α
      exact ⟨M, Or.inr hM⟩
    ·
      exfalso
      obtain ⟨x, hx, hxx⟩ := exists_fixed_norm_one_of_psi_eq h ω hω A₁ hαA₁.symm
      have h0 := congrArg (fun y : h.fixedField => (y : F)) (hiff₁.mpr hC₁J ⟨x, hx⟩)
      simp only [hB₁, ZeroMemClass.coe_zero] at h0
      rw [hxx] at h0
      exact one_ne_zero h0
  ·
    obtain rfl : r = 3 := by omega
    have hC₀eq : C₀ = sixJ h := Units.ext (by rw [hC₀J]; rfl)
    subst hC₀eq
    have hHU : H ∈ sixU h := hHgram
    have hθc : ∀ x, θ x = primeFormConjHom h _ ⟨H, hHU⟩ x := by
      intro x
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
      rw [hθmk g ⟨_, conj_mem_gramSU h _ hHU g.2⟩ rfl, primeFormConjHom_mk]
    refine ⟨⟨H, hHU⟩⁻¹, Or.inl (MulEquiv.ext fun x => ?_)⟩
    rw [map_inv, inv_inv, MulAut.mul_apply, MulAut.mul_apply, hθα, ← hθc x,
      MulEquiv.symm_apply_apply, hθc, ← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
    rfl

theorem exists_conj_eq_of_orderOf_eq_two (ω : F) (hω : ω ^ 2 + ω + 1 = 0)
    (α : MulAut (sixQ h)) (hα : orderOf α = 2) :
    ∃ A : sixU h, (∃ k, (k = 1 ∨ k = 2 ∨ k = 3) ∧
        primeFormConjHom h _ A * α * (primeFormConjHom h _ A)⁻¹ =
          MulAut.conj (sixProj h (tElt h k))) ∨
      primeFormConjHom h _ A * α * (primeFormConjHom h _ A)⁻¹ = sigmaQ h ∨
      primeFormConjHom h _ A * α * (primeFormConjHom h _ A)⁻¹ = alphaOne h := by
  rcases (even_unitary_involution_matrix_lifts h (isPrimeFormGram_sixJ h) three_le_six
    not_six_eq_three α hα).1 with hid | hbar
  · obtain ⟨A, k, hk, hA⟩ := exists_conj_eq_conj_tElt h α hα hid
    exact ⟨A, Or.inl ⟨k, hk, hA⟩⟩
  · obtain ⟨A, hA⟩ := exists_conj_eq_of_fieldFactor_bar h ω hω α hα hbar
    exact ⟨A, Or.inr hA⟩

end CFSG.LocalAnalysis.ComponentInitial.UnitarySixFieldTwoAut
