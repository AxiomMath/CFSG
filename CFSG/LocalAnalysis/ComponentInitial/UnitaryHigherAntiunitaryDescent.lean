module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryFixed
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryTransport
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenInvolutionLifts
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherConjDescentForm

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Matrix Module CFSG.ClassicalGroups.UnitaryFlag
open LinearMap (BilinForm)
open CFSG.ComponentClassification.CatalogueBAlternatingIsometry (exists_symplectic_basis)

variable {f n : ℕ} {K : Type} [Field K]

theorem map_J_ringHom {k : Type*} [Field k] (ι : k →+* K) (l : Type*) [DecidableEq l] :
    (Matrix.J l k).map ι = Matrix.J l K := by
  rw [Matrix.J, Matrix.J, fromBlocks_map, Matrix.map_zero _ (map_zero ι),
    Matrix.map_neg _ (map_neg ι), Matrix.map_one _ (map_zero ι) (map_one ι)]

theorem conj_eq_of_mul_eq {G : Type*} [Group G] {A H M X : G} (hAM : A * M = H) :
    A * X * A⁻¹ = H * (M⁻¹ * X * M) * H⁻¹ := by
  subst hAM
  group

theorem exists_fixed_gram_basis (h : UnitaryFieldData 2 f K) {C : GL (Fin n) K}
    (hC : IsPrimeFormGram C) {τ : (Fin n → K) →ₛₗ[h.bar] (Fin n → K)}
    (hττ : ∀ v, τ (τ v) = v)
    (hc1 : ∀ v w, v ∈ conjFixed h τ → w ∈ conjFixed h τ →
      h.bar (1 * gramForm h (C : Matrix (Fin n) (Fin n) K) v w) =
        1 * gramForm h (C : Matrix (Fin n) (Fin n) K) v w) :
    ∃ (b : Basis (Fin n) h.fixedField (conjFixed h τ)) (C₀ : GL (Fin n) K),
      IsPrimeFormGram C₀ ∧
      (∀ i j, gramForm h (C : Matrix (Fin n) (Fin n) K) (b i) (b j) =
        (C₀ : Matrix (Fin n) (Fin n) K) i j) ∧
      (((C₀ : Matrix (Fin n) (Fin n) K) = 1 ∧
          ¬(conjDescentForm (gramForm h (C : Matrix (Fin n) (Fin n) K)) τ 1 hc1).IsAlt) ∨
        ∃ r, n = 2 * r ∧ (C₀ : Matrix (Fin n) (Fin n) K) = blockSwapJ n r ∧
          (conjDescentForm (gramForm h (C : Matrix (Fin n) (Fin n) K)) τ 1 hc1).IsAlt) := by
  have : CharP K 2 := h.charP
  have : Finite K := h.finite
  have : FiniteDimensional h.fixedField (conjFixed h τ) := finite_conjFixed
  obtain ⟨c₀, hc₀⟩ := h.exists_bar_ne
  have hspan := span_conjFixed_of_ne hττ hc₀
  have hfin : finrank h.fixedField (conjFixed h τ) = n :=
    (finrank_conjFixed_of_ne hττ hc₀).trans (Module.finrank_fin_fun K)
  set B := conjDescentForm (gramForm h (C : Matrix (Fin n) (Fin n) K)) τ 1 hc1 with hBdef
  have hHerm := gramForm_isSymm h (hC.barTranspose h)
  have hBnd : B.Nondegenerate := conjDescentForm_nondegenerate hHerm
    (gramForm_separatingLeft h (primeFormGram_det_ne_zero C)) hspan one_ne_zero hc1
  have hBapply : ∀ v w, (B v w : K) = gramForm h (C : Matrix (Fin n) (Fin n) K) v w :=
    fun v w => by rw [hBdef, conjDescentForm_apply, one_mul]
  by_cases halt : B.IsAlt
  · obtain ⟨m, b, hd, hb⟩ := exists_symplectic_basis B halt hBnd
    rw [hfin] at hd
    have hmm : m + m = n := by omega
    refine ⟨b.reindex (finSumFinEquiv.trans (finCongr hmm)), blockSwapGL hmm,
      isPrimeFormGram_blockSwapGL hmm, fun i j => ?_, Or.inr ⟨m, hd, rfl, halt⟩⟩
    obtain ⟨x, rfl⟩ := (finSumFinEquiv.trans (finCongr hmm)).surjective i
    obtain ⟨y, rfl⟩ := (finSumFinEquiv.trans (finCongr hmm)).surjective j
    rw [Basis.reindex_apply, Basis.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
      ← hBapply, ← BilinForm.toMatrix_apply, hb, coe_blockSwapGL, ← J_apply_eq_blockSwapJ hmm,
      ← map_J_ringHom h.fixedField.subtype (Fin m)]
    rfl
  · have hsq : ∀ a : h.fixedField, IsSquare a :=
      FiniteField.isSquare_of_char_two (ringChar.eq h.fixedField 2)
    have hBsymm : B.IsSymm := ⟨fun v w => Subtype.ext (by
      rw [hBapply, hBapply, ← hHerm.eq v w]
      have h1 := hc1 v w v.2 w.2
      rw [one_mul] at h1
      exact h1.symm)⟩
    have hx : ∃ x, B x x ≠ 0 := by
      by_contra hx
      push Not at hx
      exact halt hx
    obtain ⟨b, hb⟩ := exists_orthonormal_basis_of_charTwo hsq hBsymm hBnd (Or.inr hx)
    refine ⟨b.reindex (finCongr hfin), 1, isPrimeFormGram_one, fun i j => ?_,
      Or.inl ⟨Units.val_one, halt⟩⟩
    rw [Basis.reindex_apply, Basis.reindex_apply, ← hBapply, hb, Units.val_one, one_apply]
    simp only [(finCongr hfin).symm.injective.eq_iff]
    split_ifs <;> rfl

variable (h : UnitaryFieldData 2 f K) {C : GL (Fin n) K} (hC : IsPrimeFormGram C) (hn : 3 ≤ n)
  (hq : ¬(n = 3 ∧ 2 ^ f = 2))

include hn hq in
theorem even_unitary_antiunitary_involution_descent
    (α : MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K))) (hα : orderOf α = 2)
    (hφ : ∀ x, primeFormFieldFactor h hC hn hq α x = h.bar x) :
    ∃ (A : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K)) (H C₀ : GL (Fin n) K)
      (hC₀ : IsPrimeFormGram C₀),
      ((C₀ : Matrix (Fin n) (Fin n) K) = 1 ∨
        ∃ r, n = 2 * r ∧ (C₀ : Matrix (Fin n) (Fin n) K) = blockSwapJ n r) ∧
      α = primeFormPsi h hC ⟨A, primeFormFieldFactor h hC hn hq α⟩ ∧
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar = 1 ∧
      ((H : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * (C : Matrix (Fin n) (Fin n) K) *
        (H : Matrix (Fin n) (Fin n) K) = (C₀ : Matrix (Fin n) (Fin n) K) ∧
      (∀ v : Fin n → K, ((H⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
        (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
          fun i => h.bar (((H : Matrix (Fin n) (Fin n) K) *ᵥ v) i)) = fun i => h.bar (v i)) ∧
      (∃ θ : primeFormP h (C₀ : Matrix (Fin n) (Fin n) K) ≃*
          primeFormP h (C : Matrix (Fin n) (Fin n) K),
        (∀ (g : gramSU h (C₀ : Matrix (Fin n) (Fin n) K))
          (g' : gramSU h (C : Matrix (Fin n) (Fin n) K)),
          (g' : GL (Fin n) K) = H * g * H⁻¹ →
            θ (g : primeFormP h (C₀ : Matrix (Fin n) (Fin n) K)) = g') ∧
        ∀ x, α x = θ (primeFormFieldAut h hC₀ (primeFormFieldFactor h hC hn hq α) (θ.symm x))) ∧
      ∃ B : BilinForm h.fixedField
          (conjFixed h (antiunitaryMap h ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))),
        (∀ v w, (B v w : K) = gramForm h (C : Matrix (Fin n) (Fin n) K) v w) ∧ B.IsSymm ∧
        B.Nondegenerate ∧
        finrank h.fixedField
          (conjFixed h (antiunitaryMap h ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) = n ∧
        (B.IsAlt ↔ ∃ r, n = 2 * r ∧ (C₀ : Matrix (Fin n) (Fin n) K) = blockSwapJ n r) := by
  have : CharP K 2 := h.charP
  set φ := primeFormFieldFactor h hC hn hq α with hφdef
  obtain ⟨A, hαA, hA1, hT2, hform⟩ := exists_bar_lift_of_fieldFactor_bar h hC hn hq α hα hφ
  set Am := ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hAm
  set τ := antiunitaryMap h Am with hτ
  have hττ : ∀ v, τ (τ v) = v := hT2
  have hc1 : ∀ v w, v ∈ conjFixed h τ → w ∈ conjFixed h τ →
      h.bar (1 * gramForm h (C : Matrix (Fin n) (Fin n) K) v w) =
        1 * gramForm h (C : Matrix (Fin n) (Fin n) K) v w := by
    intro v w hv hw
    rw [one_mul, ← hform v w]
    change gramForm h _ (τ v) (τ w) = _
    rw [mem_conjFixed.mp hv, mem_conjFixed.mp hw]
  obtain ⟨c₀, hc₀⟩ := h.exists_bar_ne
  have hspan := span_conjFixed_of_ne hττ hc₀
  have hfin : finrank h.fixedField (conjFixed h τ) = n :=
    (finrank_conjFixed_of_ne hττ hc₀).trans (Module.finrank_fin_fun K)
  set B := conjDescentForm (gramForm h (C : Matrix (Fin n) (Fin n) K)) τ 1 hc1 with hBdef
  have hHerm := gramForm_isSymm h (hC.barTranspose h)
  have hBnd : B.Nondegenerate := conjDescentForm_nondegenerate hHerm
    (gramForm_separatingLeft h (primeFormGram_det_ne_zero C)) hspan one_ne_zero hc1
  have hBapply : ∀ v w, (B v w : K) = gramForm h (C : Matrix (Fin n) (Fin n) K) v w :=
    fun v w => by rw [hBdef, conjDescentForm_apply, one_mul]
  have hBsymm : B.IsSymm := ⟨fun v w => Subtype.ext (by
    rw [hBapply, hBapply, ← hHerm.eq v w]
    have h1 := hc1 v w v.2 w.2
    rw [one_mul] at h1
    exact h1.symm)⟩
  obtain ⟨b, C₀, hC₀, hgram, hcase⟩ := exists_fixed_gram_basis h hC hττ hc1
  set bE := conjFixedBasisOfNe hττ hc₀ b with hbE
  obtain ⟨H, hH⟩ : ∃ H : GL (Fin n) K,
      (H : Matrix (Fin n) (Fin n) K) = (Pi.basisFun K (Fin n)).toMatrix bE :=
    ⟨⟨_, _, (Pi.basisFun K (Fin n)).toMatrix_mul_toMatrix_flip bE,
      bE.toMatrix_mul_toMatrix_flip (Pi.basisFun K (Fin n))⟩, rfl⟩
  have hHij : ∀ i j, (H : Matrix (Fin n) (Fin n) K) i j = (b j : Fin n → K) i := by
    intro i j
    rw [hH, Basis.toMatrix_apply, Pi.basisFun_repr, hbE, conjFixedBasisOfNe_apply]
  have hHcol : ∀ j, (H : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single j 1 = (b j : Fin n → K) := by
    intro j
    rw [mulVec_single_one]
    funext i
    rw [col_apply, hHij]
  have hHgram : ((H : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * (C : Matrix (Fin n) (Fin n) K) *
      (H : Matrix (Fin n) (Fin n) K) = (C₀ : Matrix (Fin n) (Fin n) K) := by
    ext i j
    rw [← gramForm_single h (((H : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *
      (C : Matrix (Fin n) (Fin n) K) * (H : Matrix (Fin n) (Fin n) K)) i j, ← gramForm_mulVec,
      hHcol, hHcol, hgram]
  have hAH : Am * (H : Matrix (Fin n) (Fin n) K).map h.bar = H := by
    ext i j
    have h1 : τ (b j) = b j := mem_conjFixed.mp (b j).2
    have h2 : (Am *ᵥ fun k => h.bar ((b j : Fin n → K) k)) i = (b j : Fin n → K) i :=
      congrFun h1 i
    rw [hHij, ← h2]
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, hHij]
  have hconj : ∀ v : Fin n → K, ((H⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
      (Am *ᵥ fun i => h.bar (((H : Matrix (Fin n) (Fin n) K) *ᵥ v) i)) =
        fun i => h.bar (v i) := by
    intro v
    have hbar : (fun i => h.bar (((H : Matrix (Fin n) (Fin n) K) *ᵥ v) i)) =
        (H : Matrix (Fin n) (Fin n) K).map h.bar *ᵥ fun i => h.bar (v i) := by
      funext i
      exact RingHom.map_mulVec h.bar _ v i
    rw [hbar, mulVec_mulVec _ Am, hAH, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, one_mulVec]
  set θ := gramTransportP h hHgram with hθ
  have hθmk : ∀ (g : gramSU h (C₀ : Matrix (Fin n) (Fin n) K))
      (g' : gramSU h (C : Matrix (Fin n) (Fin n) K)), (g' : GL (Fin n) K) = H * g * H⁻¹ →
        θ (g : primeFormP h (C₀ : Matrix (Fin n) (Fin n) K)) = g' := by
    intro g g' hg'
    rw [hθ, gramTransportP_mk]
    congr 1
    exact Subtype.ext hg'.symm
  have hmapφ : (H : Matrix (Fin n) (Fin n) K).map φ = (H : Matrix (Fin n) (Fin n) K).map h.bar :=
    Matrix.ext fun i j => hφ _
  have hAGL : (A : GL (Fin n) K) * glAut φ H = H :=
    Units.ext (by rw [Units.val_mul, coe_glAut, hmapφ]; exact hAH)
  have hθα : ∀ x, α x = θ (primeFormFieldAut h hC₀ φ (θ.symm x)) := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    rw [hαA, primeFormPsi_apply, MulAut.mul_apply, hθ, gramTransportP_symm_mk,
      primeFormFieldAut_mk, gramTransportP_mk]
    change primeFormConjHom h _ A (primeFormFieldAut h hC φ (g : primeFormP h _)) = _
    rw [primeFormFieldAut_mk, primeFormConjHom_mk]
    congr 1
    apply Subtype.ext
    change (A : GL (Fin n) K) * glAut φ (g : GL (Fin n) K) * (A : GL (Fin n) K)⁻¹ =
      H * glAut φ (H⁻¹ * (g : GL (Fin n) K) * H⁻¹⁻¹) * H⁻¹
    rw [inv_inv, map_mul, map_mul, map_inv]
    exact conj_eq_of_mul_eq hAGL
  have hiff : B.IsAlt ↔ ∃ r, n = 2 * r ∧ (C₀ : Matrix (Fin n) (Fin n) K) = blockSwapJ n r := by
    rcases hcase with ⟨hC₀1, hnalt⟩ | ⟨r, hr, hC₀J, halt⟩
    · refine ⟨fun hB => absurd hB hnalt, ?_⟩
      rintro ⟨r, hr, hJ⟩
      have h1 := congrFun (congrFun hJ ⟨0, by omega⟩) ⟨0, by omega⟩
      rw [hC₀1, one_apply_eq] at h1
      have hr0 : r ≠ 0 := by omega
      simp only [blockSwapJ, Matrix.of_apply] at h1
      split_ifs at h1 with hcond
      · exact absurd hcond (by omega)
      · exact (one_ne_zero h1).elim
    · exact ⟨fun _ => ⟨r, hr, hC₀J⟩, fun _ => halt⟩
  refine ⟨A, H, C₀, hC₀, ?_, hαA, hA1, hHgram, hconj, ⟨θ, hθmk, hθα⟩, B, hBapply, hBsymm, hBnd,
    hfin, hiff⟩
  rcases hcase with ⟨hC₀1, -⟩ | ⟨r, hr, hC₀J, -⟩
  · exact Or.inl hC₀1
  · exact Or.inr ⟨r, hr, hC₀J⟩

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
