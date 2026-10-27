module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthEigen
public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Discriminant

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open QuadraticMap

section List

variable {F : Type} [Field F] [Invertible (2 : F)]

theorem exists_orthogonal_list {W : Type} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (R : QuadraticForm F W) (hR : R.Nondegenerate) :
    ∃ l : List W, l.length = Module.finrank F W ∧ l.Pairwise R.IsOrtho ∧ (∀ x ∈ l, R x ≠ 0) ∧
      Submodule.span F {x | x ∈ l} = ⊤ ∧
      ∀ u : Fˣ, (u : F) = (l.map R).prod →
        TauCeti.RegularFormClass.discr (TauCeti.formClass R hR) = TauCeti.squareClass u := by
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (QuadraticForm.associated_isSymm F R)
  have hsep : (QuadraticMap.associated (R := F) R).SeparatingLeft :=
    (QuadraticMap.nondegenerate_associated_iff.mpr hR).1
  have hne : ∀ i, R (v i) ≠ 0 := by
    have := hv.not_isOrtho_basis_self_of_separatingLeft hsep
    simpa only [QuadraticMap.associated_eq_self_apply] using this
  set w : Fin (Module.finrank F W) → Fˣ := fun i => Units.mk0 (R (v i)) (hne i) with hw
  have hp : R.Equivalent (TauCeti.presentedForm (⟨Module.finrank F W, w⟩ :
      TauCeti.RegularFormPresentation F)) := by
    rw [TauCeti.presentedForm_eq_weightedSumSquares_coe]
    exact ⟨R.isometryEquivWeightedSumSquares v hv⟩
  refine ⟨List.ofFn v, List.length_ofFn, ?_, ?_, ?_, ?_⟩
  · rw [List.pairwise_ofFn]
    intro i j hij
    exact QuadraticMap.associated_isOrtho.mp (hv (ne_of_lt hij))
  · intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact hne i
  · have : {x | x ∈ List.ofFn v} = Set.range v := by
      ext x
      simp [List.mem_ofFn]
    rw [this, v.span_eq]
  · intro u hu
    rw [TauCeti.discr_formClass R hR _ hp]
    congr 1
    refine Units.ext ?_
    rw [Units.coe_prod, hu, List.map_ofFn, List.prod_ofFn]
    rfl

end List

section Restrict

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] [Invertible (2 : F)]

theorem exists_orthogonal_list_restrict [FiniteDimensional F V] (Q : QuadraticForm F V)
    (W : Submodule F V) (hW : (Q.restrict W).Nondegenerate) :
    ∃ l : List V, l.length = Module.finrank F W ∧ l.Pairwise Q.IsOrtho ∧ (∀ x ∈ l, Q x ≠ 0) ∧
      Submodule.span F {x | x ∈ l} = W ∧
      ∀ u : Fˣ, (u : F) = (l.map Q).prod →
        TauCeti.RegularFormClass.discr (TauCeti.formClass (Q.restrict W) hW) =
          TauCeti.squareClass u := by
  obtain ⟨l₀, hlen, hpw, hne, hspan, hdisc⟩ := exists_orthogonal_list (Q.restrict W) hW
  have hcomp : (Q ∘ (Subtype.val : W → V)) = Q.restrict W := rfl
  refine ⟨l₀.map Subtype.val, by rw [List.length_map, hlen], ?_, ?_, ?_, ?_⟩
  · rw [List.pairwise_map]
    exact hpw.imp fun {a b} h => h
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact hne y hy
  · have : {x | x ∈ l₀.map Subtype.val} = W.subtype '' {x | x ∈ l₀} := by
      ext x
      simp
    rw [this, Submodule.span_image, hspan, Submodule.map_top, Submodule.range_subtype]
  · intro u hu
    refine hdisc u ?_
    rw [hu, List.map_map, hcomp]

end Restrict

section Parity

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]

theorem even_finrank_minusSp (h2 : (2 : F) ≠ 0) {i : V ≃ₗ[F] V} (hii : i * i = 1)
    (hdet : LinearEquiv.det i = 1) : Even (Module.finrank F (minusSp i)) := by
  have hT : (i : Module.End F V) * (i : Module.End F V) = 1 :=
    LinearMap.ext fun x => by simpa using LinearEquiv.congr_fun hii x
  have h1 := CFSG.ClassicalInvolution.Models.OrthogonalPairs.det_eq_neg_one_pow_finrank h2 hT
  have h3 : LinearMap.det (i : Module.End F V) = 1 := by
    have := congrArg (fun u : Fˣ => (u : F)) hdet
    simpa using this
  rw [h3] at h1
  exact (neg_one_pow_eq_one_iff_even
    (CFSG.ClassicalInvolution.Models.OrthogonalPairs.neg_one_ne_one h2)).mp h1.symm

end Parity

end CFSG.ClassicalInvolution.ModelFacts
