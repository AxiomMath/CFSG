module

public import CFSG.ClassicalInvolution.Q3.TL4D4NCCor

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

variable {W : Type} [Group W]

theorem not_forall_commute_of_isComponent {Q : Subgroup W} (hQ : CFSG.IsComponent Q) :
    ¬ ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x := by
  intro h
  obtain ⟨a, b, hab⟩ := hQ.1.2.2
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  have hxy : x * y = y * x := Subtype.ext (h x x.2 y y.2)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hxy]

theorem autOddFreeInner_of_lieSystemMod3 [Finite W] (hO : classicalInvolutionOddCore W = ⊥)
    {Λ : Set (Subgroup W)} (hΛ : LieSystemMod3 Λ) (hnc : ∀ M ∈ Λ, ¬ M ≤ Subgroup.center W)
    {Q : Subgroup W} (hQ : CFSG.IsComponent Q) : Q3NM.AutOddFreeInner ↥Q := by
  obtain ⟨ι, _, ⟨D⟩⟩ := hΛ
  set e : W ⧸ classicalInvolutionOddCore W ≃* W :=
    (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot with he
  have hθ : Function.Injective e.toMonoidHom := e.injective
  have hem : ∀ m : W, e (QuotientGroup.mk' (classicalInvolutionOddCore W) m) = m := fun _ => rfl
  have hnc' : ∀ M ∈ oddQuotientFamily Λ,
      ¬ M ≤ Subgroup.center (W ⧸ classicalInvolutionOddCore W) := by
    rintro _ ⟨M, hM, rfl⟩ hle
    refine hnc M hM fun m hm => ?_
    have h1 := hle ⟨m, hm, rfl⟩
    rw [Subgroup.mem_center_iff] at h1 ⊢
    intro g
    have h2 := congrArg e (h1 (e.symm g))
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, hem] at h2
  have hY : e.toMonoidHom.range.Normal := by
    rw [MonoidHom.range_eq_top.mpr e.surjective]
    infer_instance
  rcases Q3CH.eq_range_or_commutes ModelFacts.modelClauseZero m11Facts D e.toMonoidHom hθ hnc'
      hY ((CFSG.isComponent_iff_open Q).mp hQ) with ⟨i, rfl⟩ | hcomm
  · have hq : CFSG.Open.IsQuasisimple ↥(e.toMonoidHom.comp (D.hom i)).range :=
      ((CFSG.isComponent_iff_open _).mp hQ).2.2
    refine autOddFreeInner_range_of_nc d4OddAutInnerNC3_proved ?_ _
      (Q3CH.ker_comp_le_center D _ hθ i) (Q3CH.exists_comp_ne_one D _ hθ i)
    rcases D.valid i with hm | hc | hc
    · exact Or.inl hm
    · exact absurd hc (Q3CH.kind_ne_sl23_of_isQuasisimple D _ hq)
    · exact Or.inr hc
  · exact absurd (fun x hx y _ => hcomm x hx y ⟨e.symm y, e.apply_symm_apply y⟩)
      (not_forall_commute_of_isComponent hQ)

end CFSG.ClassicalInvolution.Q3.TL4
