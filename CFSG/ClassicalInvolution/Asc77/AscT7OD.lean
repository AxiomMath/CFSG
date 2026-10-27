module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15D4Ord

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15

namespace T7O

open CFSG.ClassicalInvolution.G2D4Models.Twin CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.Balance.StrongBalance.Orth QuadraticMap
open scoped MatrixGroups

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

section Conj

variable {H : Type} [Group H]

theorem toInducedAutOn_eq_conj (ψ : spinGroup Q →* H) (t : spinGroup Q) :
    ((toInducedAutOn ψ.range ⟨ψ t, mem_normalizer_range ψ t⟩ : ↥(inducedAutOn ψ.range)) :
      MulAut ↥ψ.range) = MulAut.conj (ψ.rangeRestrict t) := by
  apply MulEquiv.ext
  intro ℓ
  apply Subtype.ext
  rw [toInducedAutOn_apply_coe]
  simp [MulAut.conj_apply]

theorem conj_e_of_lift {ψ : spinGroup Q →* H}
    (e : ↥(elementaryGroup Q) →* ↥(inducedAutOn ψ.range))
    (he : ∀ (s : spinGroup Q) (hs : spinAction Q s ∈ elementaryGroup Q),
      e ⟨spinAction Q s, hs⟩ = toInducedAutOn ψ.range ⟨ψ s, mem_normalizer_range ψ s⟩)
    (hrange : (spinAction Q).range = elementaryGroup Q)
    (v : ↥(inducedAutOn ψ.range)) (α : spinGroup Q ≃* spinGroup Q) (w : V ≃ₗ[F] V)
    (hαψ : ∀ x, ψ.rangeRestrict (α x) = (v : MulAut ↥ψ.range) (ψ.rangeRestrict x))
    (hθw : ∀ x, spinAction Q (α x) = w * spinAction Q x * w⁻¹) (g h : ↥(elementaryGroup Q))
    (hgh : (h : V ≃ₗ[F] V) = w * g * w⁻¹) : v * e g * v⁻¹ = e h := by
  have hmem : ∀ s : spinGroup Q, spinAction Q s ∈ elementaryGroup Q := fun s => by
    rw [← hrange]; exact ⟨s, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : spinGroup Q, spinAction Q s = g := by
    have h' : (g : V ≃ₗ[F] V) ∈ (spinAction Q).range := by
      rw [hrange]; exact g.2
    exact h'
  have hg : g = ⟨spinAction Q s, hmem s⟩ := Subtype.ext hs.symm
  have hh : h = ⟨spinAction Q (α s), hmem (α s)⟩ := by
    apply Subtype.ext
    change (h : V ≃ₗ[F] V) = spinAction Q (α s)
    rw [hθw s, hs, hgh]
  rw [hg, hh, he s (hmem s), he (α s) (hmem (α s))]
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, toInducedAutOn_eq_conj ψ,
    toInducedAutOn_eq_conj ψ]
  apply MulEquiv.ext
  intro ℓ
  have hv : (v : MulAut ↥ψ.range) (ψ.rangeRestrict s) = ψ.rangeRestrict (α s) := (hαψ s).symm
  change (v : MulAut ↥ψ.range) ((MulAut.conj (ψ.rangeRestrict s))
    ((v : MulAut ↥ψ.range).symm ℓ)) = (MulAut.conj (ψ.rangeRestrict (α s))) ℓ
  rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv, hv]
  simp

end Conj

section Frame

variable (fr : Frame Q)

theorem splitInv_frame (hQ : (polarBilin Q).Nondegenerate) :
    SplitInv Q fr.span fr.perp (fr.La (-1)) where
  ndS := polarNondegOn_of_isCompl hQ (Frame.isCompl_span_perp fr)
    (fun x hx y hy => polar_perp_of_mem_span fr hx hy)
  ndT := polarNondegOn_perp hQ fr
  orth := fun x hx y hy => polar_perp_of_mem_span fr hx hy
  top := by rw [(Frame.isCompl_span_perp fr).sup_eq_top]
  negS := fun x hx => La_neg_one_of_mem_span fr hx
  fixT := fun x hx => La_neg_one_of_mem_perp fr hx

theorem span_ne_bot [FiniteDimensional F V] : fr.span ≠ ⊥ := by
  intro h
  have := finrank_span_eq_four fr
  rw [h, finrank_bot] at this
  omega

theorem perp_ne_bot [FiniteDimensional F V] (hV : 5 ≤ Module.finrank F V) : fr.perp ≠ ⊥ := by
  intro h
  have := finrank_perp_add_four fr
  rw [h, finrank_bot] at this
  omega

theorem La_mem_elemOn (A : SL(2, F)) : fr.La A ∈ elemOn Q fr.span := by
  have h : fr.La A ∈ fr.La.range := ⟨A, rfl⟩
  rw [Frame.La_range_eq_closure] at h
  refine ((Subgroup.closure_le _).mpr ?_) h
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · exact eichler_mem_elemOn fr.e₂_mem_span (Submodule.smul_mem _ _ fr.e₁_mem_span)
  · exact eichler_mem_elemOn fr.f₁_mem_span (Submodule.smul_mem _ _ fr.f₂_mem_span)

theorem swap_La_mem_elemOn (A : SL(2, F)) : fr.swap.La A ∈ elemOn Q fr.span := by
  have := La_mem_elemOn (Q := Q) fr.swap A
  rwa [Frame.span_eq_swap_span] at this

end Frame

end T7O

end CFSG.ClassicalInvolution.ModelFacts.Orth15
